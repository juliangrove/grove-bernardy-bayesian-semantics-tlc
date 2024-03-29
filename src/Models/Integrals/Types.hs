{-# LANGUAGE TupleSections #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
module Models.Integrals.Types (module Models.Integrals.Types, module TLC.Terms) where

-- import Data.Ratio
import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import qualified Algebra.Morphism.LinComb as LC
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp, (**))
import Data.Complex
import TLC.Terms (type (∈)(..), Type(..), type(×), type(⟶), R)
import qualified Algebra.Expression as E
import Data.Function (on)
import Data.Foldable
import Data.List
--------------------------------------------------------------------------------
-- | Types

type C = Complex Double

data Zero deriving (Show,Eq,Ord)
newtype Number = Number (E.Expr Zero) deriving
  (Additive,Group,AbelianAdditive,Multiplicative,Division,Field,Ring,Roots,Transcendental)
instance Scalable Number Number where (*^) = (*)
type Rat = Number
fromNumber :: Number -> E.Expr Zero
fromNumber (Number x) = x
evalNumber :: Number -> Double
evalNumber (Number e) = E.eval (\case) e
instance Show Number where show = show . fromNumber
instance Eq Rat where
  (==) = (==) `on` evalNumber
instance Ord Rat where
  compare = compare `on` evalNumber
instance DecidableZero Rat where
  isZero  = (== 0) . evalNumber
type RatLike α = (Ring α, Ord α, DecidableZero α)


type Var γ = R ∈ γ
data Dir = Min | Max deriving (Eq,Ord,Show)
data Elem γ = Vari (Var γ)
            | Supremum Dir [Ret γ] -- either minimum or maximum of the arguments
  deriving (Eq, Ord, Show)
type Available α γ = α ∈ γ
type Expr γ = A.Affine (Var γ) Rat
type Ret γ = E.Expr (Elem γ)
type Cond γ = Cond' (Expr γ)
data Cond' e = IsNegative { condExpr :: e }
              -- Meaning of this constructor: expression ≤ 0
              | IsZero { condExpr :: e }
              -- Meaning of this constructor: expression = 0
   deriving (Eq, Show, Functor, Foldable, Traversable, Ord)

data Domain γ = Domain { domainLoBounds, domainHiBounds :: [Expr γ] }
  deriving (Show, Eq, Ord)


-- | needs to be 1st a order representation for optimisations to be
-- implementable
data P (γ :: Type) where
  Done :: Ret γ -> P γ
  Cond :: Cond γ -> P γ -> P γ
  Integrate :: Domain γ -> P (γ × R) -> P γ
  Add :: P γ -> P γ -> P γ
  Power :: P γ -> Rat -> P γ
  Mul :: [P γ] -> P γ
  -- Can this replaced by "Scale"? No, because we do integration in
  -- normalisation factors as well.
  -- Scale :: Ret γ -> P γ -> P γ
  deriving (Ord, Eq)


lift' :: Applicative f
  => (forall v. Available v γ -> f (Available v δ))
  -> (forall v. Available v (γ × α) -> f (Available v (δ × α)))
lift' _ (Get) = pure Get
lift' f (Weaken x) = Weaken <$> (f x)

class VarTraversable t where
  varTraverse :: (Applicative f)
    => (forall x. Available x γ -> f (Available x δ))
    -> t γ -> f (t δ)

instance VarTraversable Domain where
 varTraverse f (Domain los his)
  = Domain <$> traverse (A.traverseVars f) los <*>
               traverse (A.traverseVars f) his

instance VarTraversable P where
  varTraverse f = \case
    Power e k -> Power <$> varTraverse f e <*> pure k
    Done x -> Done <$> traverse (varTraverse f) x
    Mul xs -> Mul <$> traverse (varTraverse f) xs
    Integrate d e ->
      Integrate <$> (varTraverse f d) <*> (varTraverse (lift' f) e)
    Cond e x -> Cond <$> traverse (A.traverseVars f) e <*> varTraverse f x
    Add x y  -> Add <$> varTraverse f x <*> varTraverse f y

instance VarTraversable Elem where
  varTraverse f = \case
    Vari x -> Vari <$> f x
    Supremum d es -> Supremum d <$> traverse (traverse (varTraverse f)) es

deriving instance Show (P γ)


----------------------------------
-- | Smart constructors


conds_ :: [Cond γ] -> P γ -> P γ
conds_ cs e = foldr Cond e cs

isPositive,isNegative :: Expr γ -> Cond γ
isPositive e = isNegative (negate e)
isNegative e = IsNegative e


-- Domain without restriction
full :: Domain γ
full = Domain [] []

lessThan, greaterThan :: Expr γ -> Expr γ -> Cond γ
t `lessThan` u = isNegative (t - u)
t `greaterThan` u = u `lessThan` t



----------------------------
-- Instances

instance Multiplicative (P γ) where
  one = Done one
  x * y = Mul [x,y]

instance Division (P γ) where
  recip x = Power x (negate one)

instance AbelianAdditive (P γ)
instance Group (P γ) where
  negate = (negate (one :: Ret γ) *^)
instance Scalable (E.Expr (Elem γ)) (P γ) where
  k *^ e = Done k * e

pattern PZero :: P γ
pattern PZero <- Done E.Zero

instance Additive (P γ) where
  zero =  Done E.Zero
  PZero + x = x
  x + PZero = x
  x + y = Add x y



setHere :: f γ -> (Var γ -> f γ) -> Var (γ × α) -> f γ
setHere a f = \case
  Get -> a
  Weaken x -> f x

----------------------------------------------------------------
-- Normalising substitutions of variables to affine expressions

type SubstE γ δ = Var γ -> Expr δ

wkSubst :: SubstE γ δ -> SubstE (γ × α) (δ × α)
wkSubst f = \case
  Get -> A.var Get 
  Weaken x -> A.mapVars Weaken (f x)

substExpr :: SubstE γ δ ->  Expr γ -> Expr δ
substExpr = A.subst

substCond :: SubstE γ δ -> Cond γ -> Cond δ
substCond f = fmap (substExpr f)

substDomain :: SubstE γ δ -> Domain γ -> Domain δ
substDomain f (Domain lo hi) = Domain
                                 (nub (substExpr f <$> lo))
                                 (nub (substExpr f <$> hi))

wkP :: P γ -> P (γ × α)
wkP = substP $ \i -> A.var (Weaken i) 

substElem :: forall γ ζ. SubstE γ ζ -> Elem γ -> Ret ζ
substElem v = \case
  Supremum dir es -> supremum dir (substRet v <$> es)
  Vari x -> exprToPoly (v x)

substRet  :: forall γ ζ. SubstE γ ζ -> Ret γ -> Ret ζ
substRet v = E.eval (substElem v)

substP :: SubstE γ δ -> P γ -> P δ
substP f p0 = case p0 of
  Done e -> Done (E.eval (substElem f) e)
  Add p1 p2 -> substP f p1 + substP f p2
  Power p k -> Power (substP f p) k
  Mul ps -> Mul (substP f <$> ps)
  Cond c p -> Cond (substCond f c) (substP f p)
  Integrate d p -> Integrate (substDomain f d) (substP (wkSubst f) p) -- integrations are never simplified by substitution

swap2P :: P (γ × α × β) -> P (γ × β × α)
swap2P = substP $ \case
  Get -> A.var (Weaken Get)
  Weaken Get -> A.var Get
  Weaken (Weaken x) -> A.var (Weaken (Weaken x))

wkExpr :: Expr γ -> Expr (γ × β)
wkExpr = substExpr (A.var . Weaken) 

condVars :: Cond γ -> [Var γ]
condVars c = case condExpr c of
   (A.Affine _ e) -> map fst (LC.toList e)

retVars :: Ret γ -> [Var γ]
retVars x = concatMap elemVars (toList x)

elemVars :: Elem γ -> [Var γ]
elemVars = \case
   Vari x -> [x]
   Supremum _ es -> concatMap retVars es

supremum :: Dir -> [Ret γ] -> Ret γ
supremum _ [e] = e
supremum dir es = 
  case traverse (fmap retToNumber . traverse (varTraverse (const Nothing))) es of
    Just cs | not (null es) ->
       constPoly ((case dir of
                     Max -> maximum
                     Min -> minimum)
                   cs)
    _ -> E.Var (Supremum dir es)

constPoly :: Number -> Ret γ
constPoly (Number n) = (\case) <$> n

varPoly :: R ∈ γ -> Ret γ
varPoly = E.Var . Vari

retToNumber :: Ret 'Unit -> Number
retToNumber = E.eval $ \case
     Vari x -> case x of
     Supremum d xs -> (case d of Max -> maximum; Min -> minimum) (fmap retToNumber xs)

numberToRet :: Number -> Ret γ
numberToRet (Number x) = fmap (\case) x
exprToPoly :: Expr γ -> Ret γ
exprToPoly = A.eval (fmap (\case) .fromNumber) (E.Var .  Vari)

mkSuprema :: Domain γ -> (Ret γ, Ret γ)
mkSuprema (Domain los his) = (supremum Max $ map exprToPoly los,
                              supremum Min $ map exprToPoly his)

