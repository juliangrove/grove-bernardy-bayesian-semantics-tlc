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

module Models.Integrals.Optimizer (cleanConds
                                  , normalise
                                  , splitDomains
                                  , conds_) where

-- import Data.Ratio
import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp)
import Algebra.Linear.FourierMotzkin (entailsStrict, hasContradictionStrict)

import Models.Integrals.Types
import Control.Applicative (Const(..))
import Data.List (partition)
import Data.Maybe (catMaybes)
  

---------------------------------------------------------
-- Normalisation of integrals 

-- | Restrict the bounds in the domain according to some
-- conditions. Also return conditions that ensure that the bounds are
-- in the right order.
restrictDomain :: Cond (γ × 'R) -> Domain γ -> (Domain γ, [Cond γ])
restrictDomain c (Domain los his) = case solve' c of -- version with solver
  (LT, e) -> (Domain los (e:his), [ lo `lessThan` e | lo <- los ])
  (GT, e) -> (Domain (e:los) his, [ e `lessThan` hi | hi <- his ])
  _ -> error "restrictDomain: cannot be called/(1) on equality condition"

solveGet :: (x ~ Rat) => A.Affine (Var (γ × 'R)) x -> (Bool, Expr γ)
solveGet e0 = case A.solve Get e0 of
  Left _ -> error "solveGet: division by zero"
  Right (p, e1) -> case occurExpr e1 of
    Nothing -> error "solveGet panic: eliminated variable present elsewhere"
    Just e -> (p, e)

type Solution γ = (Ordering, Expr γ)
  
-- FIXME: detect always true and always false cases.
solve' :: Cond (γ × 'R) -> Solution γ
solve' c0 = case c0 of
    IsZero _ -> (EQ, e)
    IsNegative _ -> if positive then (LT, e) else (GT, e) 
  where (positive,e) = solveGet (condExpr c0)
  

occurExpr :: Expr (γ × 'R) -> Maybe (Expr γ)
occurExpr = A.traverseVars $ \case
  Get -> Nothing
  Weaken x -> Just x

domainToConds :: Domain γ -> [Cond (γ × 'R)]
domainToConds (Domain los his)
  = [wkExpr e `lessThan` A.var Get | e <- los] ++
    [A.var Get `lessThan` wkExpr e | e <- his]

noGet :: Available x (γ × a) -> Maybe (Available x γ)
noGet = (\case Get -> Nothing; Weaken x -> Just x)

-- | Normalising condition, placing the shallowest conditions first,
-- so that they can be exposed to integrals which are able to resolve them.
cond :: Cond γ -> P γ -> P γ
cond (IsNegative (A.Affine k0 vs)) e | k0 <= zero, vs == zero = e
cond _ (Ret z) | isZero z = Ret $ zero
cond c (Cond c' e) | c == c' = cond c e
cond c (Cond c' e) = if (deepest c) `shallower` (deepest c')
                     then Cond c (Cond c' e)
                     else Cond c' (cond c e)
cond c e = Cond c e


integrate :: Domain γ -> P (γ × 'R) -> P γ
integrate _ (Ret z) | isZero z = Ret $ zero
integrate d e | Just z' <- varTraverse noGet e = z' / recip (Ret (hi-lo)) 
  where (lo,hi) = mkSuprema d -- ∫_lo^hi k dx = k*(hi-lo)
-- NOTE: the above causes many traver, we'd need to compute the unused
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
    substP (\case Get -> x0; Weaken i -> A.var i) $ conds_ (domainToConds d) e
    where (_, x0) = solveGet c'
  Just c'' -> cond (IsZero c'') (integrate d e)
integrate d (Add e e') = Add (integrate d e) (integrate d e')
integrate d e = Integrate d e

normalise :: P γ -> P γ
normalise = \case
  Cond c (normalise -> e) -> cond c e
  Integrate d (normalise -> e) -> integrate d e
  Add (normalise -> p1) (normalise -> p2) -> p1 + p2
  Div (normalise -> p1) (normalise -> p2) -> p1 / p2
  Ret e -> Ret e

type Negative γ = Expr γ 

entail :: [Negative γ] -> Negative γ -> Bool
entail cs c = entailsStrict (map negate cs) (negate c)

dominated :: Dir -> [Negative γ] -> Expr γ -> [Expr γ] -> Bool
dominated d cs x ys = any (\bnd -> entail cs (x `cmp` bnd)) ys
  where cmp = case d of Min -> flip (-); Max -> (-)

cleanBounds :: [Negative γ] -> Dir -> [Expr γ] -> [Expr γ] -> [Expr γ]
cleanBounds _ _ [] kept = kept
cleanBounds cs d (x:xs) kept =
  if dominated d cs x kept
  then cleanBounds cs d xs kept
  else cleanBounds cs d xs (x:filter (\k -> not (dominated d cs k [x])) kept)
 -- Example. We have kept z as bound (z ∈ kept).
 -- Now we consider 80, under (z ≤ 80) ∈ cs.
 -- We test the condition x ≤ 80, and find that it is entailed by cs.
 -- And so we can discard 80.

cleanDomain :: [Negative γ] -> Domain γ -> Domain γ
cleanDomain cs (Domain los his) =
  Domain (cleanBounds cs Max los []) (cleanBounds cs Min his [])

-- | Remove redundant conditions
cleanConds :: [Negative γ] -> P γ -> P γ
cleanConds cs = \case
  Ret x -> Ret x
  Integrate d e -> Integrate (cleanDomain cs d) $
                   cleanConds' ((fromNegative <$> domainToConds d) ++
                               (map (A.mapVars  Weaken) cs)) $
                   e
  Cond c e -> if cs `entail` fromNegative c
              then cleanConds cs e
              else cond c $ cleanConds' (fromNegative c:cs) e
  Div x y -> Div (cleanConds cs x) (cleanConds cs y)
  Add x y -> Add (cleanConds cs x) (cleanConds cs y)
 where fromNegative (IsNegative c) = c
       fromNegative _ = error "cleanConds: equality condition remaining?"

cleanConds' :: (a ~ Rat) => [Negative γ] -> P γ -> P γ
cleanConds' cs e = if hasContradictionStrict (map negate cs) then zero else cleanConds cs e

-- | Traversing with this returns free variables
getVars :: x ∈ γ -> Const [SomeVar γ] (x ∈ γ)
getVars v = Const  [SomeVar v]

-- | Return a list of conditions occuring, in the form of expressions
-- whose sign is tested.
discontinuities :: forall γ. P γ -> [Expr γ]
discontinuities  = \case
  Add a b -> discontinuities a <> discontinuities b
  Div a b -> discontinuities a <> discontinuities b
  Cond (IsNegative f) e -> f : discontinuities e
  Cond _ _ -> error "discontinuities equality?"
  Ret _ -> []
  Integrate (Domain los his) e -> mkEqs los <> mkEqs his <> catMaybes (fmap (A.traverseVars noGet) (discontinuities e))
    where mkEqs as = [a-b | a <- as, b <- as]

-- | Make an explicit test on a condition. The underlying formula is:
-- e = cond c e + cond (not c) e
testCond :: Domain γ -> [Expr (γ × 'R)] -> P (γ × 'R) -> P γ
testCond d [] e = Integrate d e
testCond d (f:fs) e = testCond d fs (Cond (isPositive f) e) + testCond d fs (Cond (isNegative f) e)

-- | Split domains of integration so that no condition remains
splitDomains :: P γ -> P γ
splitDomains = \case
  Integrate d (splitDomains -> e) -> testCond d fs e
    where fs = filter ((SomeVar Get `elem`) . getConst . A.traverseVars getVars) (discontinuities e)
  Cond c e -> Cond c (splitDomains e)
  Add a b -> Add (splitDomains a) (splitDomains b) 
  Div a b -> Div (splitDomains a) (splitDomains b) 
  Ret x -> Ret x


