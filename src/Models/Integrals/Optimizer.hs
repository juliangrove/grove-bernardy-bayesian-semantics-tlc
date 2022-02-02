{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Models.Integrals.Optimizer where

import Data.List (nub)
-- import Data.Ratio
import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import qualified Algebra.Morphism.LinComb as LC
import Algebra.Morphism.LinComb (LinComb)
import Algebra.Morphism.Polynomial.Multi hiding (constPoly)
import qualified Algebra.Morphism.Polynomial.Multi as Multi
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp)
import TLC.Terms hiding ((>>), u, Con)
import Algebra.Linear ((*<))
import Models.Field (Fld(..))
import qualified Models.Field
import Algebra.Linear.Chebyshev (chebIntegral)
import Algebra.Linear.FourierMotzkin (entailsStrict)
import Data.Complex
import Text.Pretty.Math

import Models.Integrals.Types
  

---------------------------------------------------------
-- Normalisation of integrals 

-- | Restrict the bounds in the domain according to some
-- conditions. Also return conditions that ensure that the bounds are
-- in the right order.
restrictDomain :: α ~ Rat
               => Cond (γ, α) α -> Domain γ α -> (Domain γ α, [Cond γ α])
restrictDomain c (Domain cs los his) = case solve' c of -- version with solver
  (LT, e) -> (Domain cs los (e:his), [ lo `lessThan` e | lo <- los ])
  (GT, e) -> (Domain cs (e:los) his, [ e `lessThan` hi | hi <- his ])
  _ -> error "restrictDomain: cannot be called/(1) on equality condition"

solveHere :: RatLike x => A.Affine (Available x (γ, x)) x -> (Bool, Expr γ x)
solveHere e0 = case A.solve Here e0 of
  Left _ -> error "solveHere: division by zero"
  Right (p, e1) -> case occurExpr e1 of
    Nothing -> error "solveHere panic: eliminated variable present elsewhere"
    Just e -> (p, e)

type Solution γ d = (Ordering, Expr γ d)
  
-- FIXME: detect always true and always false cases.
solve' :: Cond (γ, Rat) Rat -> Solution γ Rat
solve' c0 = case c0 of
    IsZero _ -> (EQ, e)
    IsNegative _ -> if positive then (LT, e) else (GT, e) 
  where (positive,e) = solveHere (condExpr c0)
  

occurExpr :: Additive t => Expr (γ, x) t -> Maybe (Expr γ t)
occurExpr = A.traverseVars $ \case
  Here -> Nothing
  There x -> Just x

domainToConds :: RatLike α => Domain γ α -> [Cond (γ,α) α]
domainToConds (Domain cs los his)
  = cs ++ [wkExpr e `lessThan` A.var Here | e <- los]
       ++ [A.var Here `lessThan` wkExpr e | e <- his]

conds_ :: RatLike a => [Cond γ a] -> P γ a -> P γ a
conds_ cs e = foldr Cond e cs

noHere :: Available x (γ,a) -> Maybe (Available x γ)
noHere = (\case Here -> Nothing; There x -> Just x)

integrate :: d ~ Rat => Domain γ d -> P (γ, d) Rat -> P γ Rat
integrate _ (Ret z) | isZero z = Ret $ zero
integrate d e | Just z' <- traverseP noHere e = z' / recip (Ret (hi-lo)) 
  where (lo,hi) = mkSuprema d -- ∫_lo^hi k dx = k*(hi-lo)
-- NOTE: the above causes many traversals to be made (making normalise
-- quadratic). To do this efficiently, we'd need to compute the unused
-- variables at every stage in this function, and record the result
-- using a new constructor in P. This new constructor can the be used
-- to check for free variables directly.
integrate d (Cond c@(IsNegative c') e) = case occurExpr c' of
  Nothing -> foldr cond (integrate d' e) cs
    where (d', cs) = restrictDomain c d
  Just c'' -> cond (IsNegative c'') (integrate d e)
integrate d (Cond (IsZero c') e) = case occurExpr c' of
  Nothing ->
    -- We apply the rule: ∫ f(x) δ(c x + k) dx = f(-k/c)   
    -- (The correct rule is: ∫ f(x) δ(c x + k) dx = (1/abs c) * f(-k/c)
    -- HOWEVER, due to the way we generate the equalities, my hunch is
    -- that we already take into account this coefficient. To be
    -- investigated.)
    substP (\case Here -> x0; There i -> A.var i) $ conds_ (domainToConds d) e
    where (_, x0) = solveHere c'
  Just c'' -> cond (IsZero c'') (integrate d e)
integrate d (Add e e') = Add (integrate d e) (integrate d e')
integrate d e = Integrate d e

normalise :: P γ Rat -> P γ Rat
normalise = \case
  Cond c (normalise -> e) -> cond c e
  Integrate d (normalise -> e) -> integrate d e
  Add (normalise -> p1) (normalise -> p2) -> p1 + p2
  Div (normalise -> p1) (normalise -> p2) -> p1 / p2
  Ret e -> Ret e

type Negative γ a = Expr γ a 

entail :: RatLike a => [Negative γ a] -> Negative γ a -> Bool
entail cs c = entailsStrict (map negate cs) (negate c)

dominated :: RatLike a => Dir -> [Negative γ a] -> Expr γ a -> [Expr γ a] -> Bool
dominated d cs x ys = any (\bnd -> entail cs (x `cmp` bnd)) ys
  where cmp = case d of Min -> flip (-); Max -> (-)

cleanBounds :: RatLike a
  => [Negative γ a] -> Dir -> [Expr γ a] -> [Expr γ a] -> [Expr γ a]
cleanBounds _  _ [] kept = kept
cleanBounds cs d (x:xs) kept =
  if dominated d cs x kept
  then cleanBounds cs d xs kept
  else cleanBounds cs d xs (x:filter (\k -> not (dominated d cs k [x])) kept)
 -- Example. We have kept z as bound (z ∈ kept).
 -- Now we consider 80, under (z ≤ 80) ∈ cs.
 -- We test the condition x ≤ 80, and find that it is entailed by cs.
 -- And so we can discard 80.

cleanDomain :: RatLike a => [Negative γ a] -> Domain γ a -> Domain γ a
cleanDomain cs (Domain c los his) =
  Domain c (cleanBounds cs Max los []) (cleanBounds cs Max his [])

-- | Remove redundant conditions
cleanConds :: (a ~ Rat) => [Negative γ a] -> P γ a -> P γ a
cleanConds cs = \case
  Ret x -> Ret x
  Integrate d e -> Integrate (cleanDomain cs d) $
                   cleanConds ((fromNegative <$> domainToConds d) ++
                               (map (A.mapVars  There) cs)) $
                   e
  Cond c e -> if cs `entail` fromNegative c
              then cleanConds cs e
              else cond c $ cleanConds (fromNegative c:cs) e
  Div x y -> Div (cleanConds cs x) (cleanConds cs y)
  Add x y -> Add (cleanConds cs x) (cleanConds cs y)
 where fromNegative (IsNegative c) = c
       fromNegative _ = error "cleanConds: equality condition remaining?"


