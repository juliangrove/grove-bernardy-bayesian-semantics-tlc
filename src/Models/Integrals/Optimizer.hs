{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
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
import Prelude hiding (Num(..), Fractional(..), (^), product, sum 
                      , Floating (..))
import Algebra.Linear.FourierMotzkin (entailsStrict, hasContradictionStrict)
import Models.Integrals.Types
import Control.Applicative (Const(..))
import Data.Maybe (catMaybes)
import qualified Algebra.Expression as E
import Data.Either (partitionEithers)
import Data.List (sort, insert)


--------------------------------------------------------------------------------
-- | Normalisation of integrals 

insertUniq :: Eq a => a -> [a] -> [a]
insertUniq x [] = [x]
insertUniq x (y:xs) | x == y = (y:xs)
                    | otherwise = y : insertUniq x xs
                   
-- | Restrict the bounds in the domain according to some
-- conditions. Also return conditions that ensure that the bounds are
-- in the right order.
restrictDomain :: Cond (γ × R) -> Domain γ -> (Domain γ, [Cond γ])
restrictDomain c (Domain los his) = case solve' c of -- version with solver
  (LT, e) -> (Domain los (e `insertUniq` his), [ lo `lessThan` e | lo <- los ])
  (GT, e) -> (Domain (e `insertUniq` los) his, [ e `lessThan` hi | hi <- his ])
  _ -> error "restrictDomain: cannot be called/(1) on equality condition"

solveGet :: (x ~ Rat) => A.Affine (Var (γ × R)) x -> (Bool, Expr γ)
solveGet e0 = case A.solve Get e0 of
  Left _ -> error "solveGet: division by zero"
  Right (p, e1) -> case occurExpr e1 of
    Nothing -> error "solveGet panic: eliminated variable present elsewhere"
    Just e -> (p, e)

type Solution γ = (Ordering, Expr γ)
  
-- FIXME: detect always true and always false cases.
solve' :: Cond (γ × R) -> Solution γ
solve' c0 = case c0 of
    IsZero _ -> (EQ, e)
    IsNegative _ -> if positive then (LT, e) else (GT, e) 
  where (positive, e) = solveGet (condExpr c0) 

occurExpr :: Expr (γ × R) -> Maybe (Expr γ)
occurExpr = A.traverseVars $ \case
  Get -> Nothing
  Weaken x -> Just x

domainToConds :: Domain γ -> [Cond (γ × R)]
domainToConds (Domain los his) =
  [ wkExpr e `lessThan` A.var Get | e <- los ] ++
  [ A.var Get `lessThan` wkExpr e | e <- his ]

noGet :: Available x (γ × a) -> Maybe (Available x γ)
noGet = (\case Get -> Nothing; Weaken x -> Just x)

-- | Normalising condition, placing the shallowest conditions first,
-- so that they can be exposed to integrals which are able to resolve them.
cond :: Cond γ -> P γ -> P γ
cond (IsNegative (A.Affine k0 vs)) e | k0 <= zero, vs == zero = e
cond _ PZero  = zero
cond c (Cond c' e) | c == c' = cond c e
cond c (Cond c' e) = if deepest (condVars c) > deepest (condVars c')
                     then Cond c (Cond c' e)
                     else Cond c' (cond c e)
cond c e = Cond c e


integrate :: Domain γ -> P (γ × R) -> P γ
integrate _ PZero = zero
integrate d (Done k) | Just k' <- traverse (varTraverse noGet) k
                     -- integration variable does not occur in k
  = Done ((hi - lo) * k')
  where (lo, hi) = mkSuprema d -- ∫_lo^hi dx = (hi-lo)
integrate d (Cond c@(IsNegative c') e) = case occurExpr c' of
  Nothing -> foldr cond (integrate d' e) cs
    where (d', cs) = restrictDomain c d
  Just c'' -> cond (IsNegative c'') (integrate d e)
  -- integration variable does not occur in c'
integrate d (Cond (IsZero c') e) = case occurExpr c' of
  Nothing -> -- FIXME:
    -- We apply the rule: ∫ f(x) δ(c x + k) dx = f(-k/c)   
    -- (The correct rule is: ∫ f(x) δ(c x + k) dx = (1/abs c) * f(-k/c)
    -- HOWEVER, due to the way we generate the equalities, my hunch is
    -- that we already take into account this coefficient. To be
    -- investigated.)
    substP (\case Get -> x0; Weaken i -> A.var i) $
    foldr cond e (domainToConds d)
    where (_, x0) = solveGet c'
  Just c'' -> cond (IsZero c'') (integrate d e)
integrate d (Add e e') = Add (integrate d e) (integrate d e')
integrate d (Mul xs) = product ks * if null rest
                                    then integrate d one
                                    else Integrate d (Mul rest)
  where (ks, rest) = partitionEithers (fmap isConst xs)
        isConst p = case varTraverse noGet p of
          Just p' -> Left p'
          Nothing -> Right p
integrate d e | Just z' <- varTraverse noGet e = mul [Done (hi - lo), z']  
  where (lo, hi) = mkSuprema d

        
--- NOTE: the above causes many traversals. To avoid it we'd need to compute the (un)used
--- variables at every stage in this function, and record the result
--- using a new constructor in P. This new constructor can the be used
--- to check for free variables directly.

integrate d e = Integrate d e


normalise :: P γ -> P γ
normalise = \case
  Cond c (normalise -> e) -> cond c e
  Integrate d (normalise -> e) -> integrate d e
  Power p e -> power e (normalise p)
  Add (normalise -> p1) (normalise -> p2) -> p1 + p2
  Mul ps -> mul (fmap normalise ps)
  Done k -> done k
  -- Scale k e -> scal k (normalise e)

power :: Number -> P γ -> P γ
power (Number E.One) = id
power k = \case
  Mul as -> Mul (power k <$> as)
  Cond c e -> Cond c (power k e)
  Done e -> Done (e ** numberToRet k)
  -- Scale x e -> Scale (x ** numberToRet k) (power k e)
  Power e k' -> power (k * k') e
  e -> Power e k

-- scal :: Ret γ -> P γ -> P γ
-- scal E.Zero _ = zero
-- scal (E.Prod xs) e = foldr scal e xs -- split the product so that parts of it can commute with integrals
-- scal k (Cond c e) = Cond c (scal k e)
-- scal k (Add a b) = scal k a `Add` scal k b
-- scal (E.Con x) (Mul (E.Con y : e)) = scal (E.Con (x*y)) (Mul e)
-- -- scal c e0@(Scale c' e)
-- --   | deepest (retVars c) > deepest (retVars c') = Scale c e0
-- --   | deepest (retVars c) < deepest (retVars c') = scal c' (scal c e)
-- --   | E.Pow x' k' <- c', x' == c = scal (c ** (k' + 1)) e
-- --   | E.Pow x k <- c, E.Pow x' k' <- c', x == x' = scal (x ** (k + k')) e
-- --   | E.Pow x k <- c, E.Pow x' k' <- c', k == k' = scal ((x * x') ** k) e
-- --   | c == c' = scal (c ^+ 2) e
-- --   | c < c' = Scale c e0
-- --   | c > c' = scal c' (scal c e)
  
-- scal k e = Scale k e

done :: E.Expr (Elem γ) -> P γ
done (E.Prod xs) = mul (done <$> xs)
done x = Done x

mur :: P γ -> P γ -> P γ
mur a = \case
  Done E.Zero -> zero
  Done E.One -> a
  Cond c x -> Cond c (mur a x)
  Add p1 p2 -> Add (mur a p1) (mur a p2)
  Mul (Done x:xs) | Done y <- a, null (retVars x) && null (retVars y) ->
                    mur (Done (x * y)) (Mul xs)
  Mul xs -> Mul (a `insert` xs)
  x -> Mul (a `insert` [x])

mul :: [P γ] -> P γ
mul [] = one
mul [x] = x
mul (Done E.Zero : _) = zero
mul (Done E.One : xs) = mul xs
mul (Cond c x : xs) = Cond c (mul (x:xs))
mul (Add p1 p2 : xs) = Add (mul (p1:xs)) (mul (p2:xs))
mul (Mul xs : ys) = mul (xs <> ys)
mul (x : ys) = mur x (mul ys)


-- | The deepest variable in a list. Relies on correct order for Var type.
deepest :: [Var γ] -> SomeVar γ
deepest [] = NoVar
deepest xs = SomeVar (minimum xs)

-- varExamples :: [SomeVar ('Unit × R × R)]
-- varExamples = [NoVar, SomeVar (Get), SomeVar (Weaken Get)]

-- >>> [(x,y,x > y) | x <- varExamples, y <- varExamples]
-- [(NoVar,NoVar,False),(NoVar,SomeVar Get,True),(NoVar,SomeVar (Weaken Get),True),(SomeVar Get,NoVar,False),(SomeVar Get,SomeVar Get,False),(SomeVar Get,SomeVar (Weaken Get),False),(SomeVar (Weaken Get),NoVar,False),(SomeVar (Weaken Get),SomeVar Get,True),(SomeVar (Weaken Get),SomeVar (Weaken Get),False)]


data SomeVar γ = SomeVar (Var γ) | NoVar
  deriving (Eq, Ord, Show)

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
  else cleanBounds cs d xs (x : filter (\k -> not (dominated d cs k [x])) kept)
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
  Done k -> Done k
  Power e k -> Power (cleanConds cs e) k
  -- Scale k e -> Scale k (cleanConds cs e)
  Integrate d e -> Integrate (cleanDomain cs d) 
                   $ cleanConds' ((fromNegative <$> domainToConds d) ++ -- new conditions coming from the domain being traversed
                                  (map (A.mapVars Weaken) cs)) -- keep old conditions (but weaken variables)
                   $ e
  Cond c e -> if cs `entail` fromNegative c
              then cleanConds cs e
              else cond c $ cleanConds' (fromNegative c:cs) e
  Mul xs -> Mul (fmap (cleanConds cs) xs)
  Add x y -> Add (cleanConds cs x) (cleanConds cs y)
 where fromNegative (IsNegative c) = c
       fromNegative _ = error "cleanConds: equality condition remaining?"

cleanConds' :: (a ~ Rat) => [Negative γ] -> P γ -> P γ
cleanConds' cs e = if hasContradictionStrict (map negate cs)
                   then zero
                   else cleanConds cs e

-- | Traversing with this returns free variables.
getVars :: Var γ -> Const [Var γ] (Var γ)
getVars v = Const [v]

-- | Return a list of conditions occuring, in the form of expressions whose sign
-- is tested.
discontinuities :: forall γ. P γ -> [Expr γ]
discontinuities  = \case
  Add a b -> discontinuities a <> discontinuities b
  Power e _ -> discontinuities e
  Mul as -> concatMap discontinuities as
  Cond (IsNegative f) e -> f : discontinuities e
  Cond _ _ -> error "discontinuities equality?"
  -- Scale _ e -> discontinuities e
  Done _ -> []
  Integrate (Domain los his) e -> mkEqs los <> mkEqs his <> catMaybes (fmap (A.traverseVars noGet) (discontinuities e))
    where mkEqs as = [ a - b | a <- as, b <- as ]

-- | Make an explicit test on a condition. The underlying formula is:
-- e = cond c e + cond (not c) e
testCond :: Domain γ -> [Expr (γ × R)] -> P (γ × R) -> P γ
testCond d [] e = Integrate d e
testCond d (f:fs) e = testCond d fs (Cond (isPositive f) e) + testCond d fs (Cond (isNegative f) e)

-- | Split domains of integration so that no condition remains
splitDomains :: P γ -> P γ
splitDomains = \case
  Power e k -> Power (splitDomains e) k
  Integrate d (splitDomains -> e) -> testCond d fs e
    where fs = filter ((Get `elem`) . getConst . A.traverseVars getVars) (discontinuities e)
  Cond c e -> Cond c (splitDomains e)
  Add a b -> Add (splitDomains a) (splitDomains b) 
  Mul as -> Mul (fmap splitDomains as)
  -- Scale k e -> Scale k (splitDomains e)
  Done k -> Done k


