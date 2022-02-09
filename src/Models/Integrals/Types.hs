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
import Algebra.Morphism.LinComb (LinComb)
import qualified Algebra.Morphism.Polynomial.Multi as Multi
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp)
import Data.Complex
import TLC.Terms (type (∈)(..), Type(..), type(×), type(⟶))
import qualified Algebra.Expression as E
import Data.Function (on)

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
evalNumber = E.eval @Double (\case) . fromNumber
instance Show Number where show = show . fromNumber
instance Eq Rat where
  (==) = (==) `on` evalNumber
instance Ord Rat where
  compare = compare `on` evalNumber
instance DecidableZero Rat where
  isZero  = (== 0) . evalNumber
type RatLike α = (Ring α, Ord α, DecidableZero α)


data Elem γ = Vari ('R ∈ γ) | Supremum Dir [Ret γ]
  deriving (Eq, Ord, Show)

data Dir = Min | Max deriving (Eq,Ord,Show)
type Available α γ = α ∈ γ
type Var γ = 'R ∈ γ
type Expr γ = A.Affine (Available 'R γ) Rat
type Ret γ = E.Expr (Elem γ)
type Cond γ = Cond' (Expr γ)
data Cond' e = IsNegative { condExpr :: e }
              -- Meaning of this constructor: expression ≤ 0
              | IsZero { condExpr :: e }
              -- Meaning of this constructor: expression = 0
   deriving (Eq, Show, Functor, Foldable, Traversable, Ord)

data Domain γ = Domain { domainLoBounds, domainHiBounds :: [Expr γ] }
  deriving (Show, Eq, Ord)

data P (γ :: Type) where
  Integrate :: Domain γ -> P (γ × 'R) -> P γ
  Cond :: Cond γ -> P γ -> P γ
  Add :: P γ -> P γ -> P γ
  Div :: P γ -> P γ -> P γ
  -- Can Div be replaced by "factor"? No, because we do integration in
  -- these factors as well.
  Ret :: Ret γ -> P γ
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
    Div x y -> Div <$> varTraverse f x <*> varTraverse f y
    Integrate d e ->
      Integrate <$> (varTraverse f d) <*> (varTraverse (lift' f) e)
    Cond e x -> Cond <$> traverse (A.traverseVars f) e <*> varTraverse f x
    Add x y  -> Add <$> varTraverse f x <*> varTraverse f y
    Ret x -> Ret <$> traverse (varTraverse f) x

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
  one = Ret one
  (Integrate d p1) * p2 = Integrate d $ p1 * wkP p2
  p2 * (Integrate d p1) = Integrate d $ p1 * wkP p2
  (Cond c p1) * p2 = Cond c (p1 * p2)
  p2 * (Cond c p1) = Cond c (p1 * p2)
  (Add p1 p1') * p2 = Add (p1 * p2) (p1' * p2)
  p1 * (Add p2 p2') = Add (p1 * p2) (p1 * p2')
  (Div p1 p1') * p2 = Div (p1 * p2) p1'
  p1 * (Div p2 p2') = Div (p1 * p2) p2'
  -- (Div p1 p1') * (Div p2 p2') = Div ((*) p1 p1') ((*) p2 p2') -- no need to regroup normalisation factors
  Ret e1 * Ret e2 = Ret (e1 * e2)

instance AbelianAdditive (P γ)
instance Group (P γ) where
  negate = (* (Ret (negate one)))
instance Scalable (Ret γ) (P γ) where
  p *^ q = Ret p * q
instance Additive (P γ) where
  zero = Ret zero
  (Ret (E.Sum [])) + x = x
  x + (Ret (E.Sum [])) = x
  x + y = Add x y

instance Division (P γ) where
  (Ret (E.Sum [])) / _  = Ret $ zero
  (Cond c n) / d = Cond c (n / d) -- this exposes conditions to the integrators in the denominator
  p1 / p2 = Div p1 p2



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
                                 (substExpr f <$> lo)
                                 (substExpr f <$> hi)

wkP :: P γ -> P (γ × α)
wkP = substP $ \i -> A.var (Weaken i) 

substElem :: forall γ ζ. SubstE γ ζ -> Elem γ -> Ret ζ
substElem v =
  let evP :: Ret γ -> Ret ζ
      evP = E.eval (substElem v) 
  in \case Supremum dir es -> supremum dir (evP <$> es)
           Vari x -> exprToPoly (v x)

substP :: SubstE γ δ -> P γ -> P δ
substP f p0 = case p0 of
  Ret e -> Ret (e >>= substElem f)
  Add p1 p2 -> substP f p1 + substP f p2
  Div p1 p2 -> substP f p1 / substP f p2
  Cond c p -> Cond (substCond f c) (substP f p)
  Integrate d p -> Integrate (substDomain f d) (substP (wkSubst f) p) -- integrations are never simplified by substitution

wkExpr :: Expr γ -> Expr (γ × β)
wkExpr = substExpr (A.var . Weaken) 


deepest :: Cond γ -> SomeVar γ
deepest c = case condExpr c of
   (A.Affine _ e) -> case LC.toList e of
     xs@(_:_) -> foldr1 minVar . map SomeVar . map fst $ xs
     [] -> NoVar

shallower :: SomeVar γ -> SomeVar γ -> Bool
SomeVar Get `shallower` _ = False
SomeVar (Weaken _) `shallower` SomeVar Get = True
SomeVar (Weaken x) `shallower` SomeVar (Weaken y)
  = SomeVar x `shallower` SomeVar y
NoVar `shallower` (SomeVar _) = True
(SomeVar _) `shallower` NoVar = True
_ `shallower` _ = False

data SomeVar γ where
  SomeVar :: Available v γ -> SomeVar γ
  NoVar :: SomeVar γ
instance Eq (SomeVar γ) where
  SomeVar Get == SomeVar Get = True
  SomeVar (Weaken x) == SomeVar (Weaken y) = SomeVar x == SomeVar y
  NoVar == NoVar = True
  _ == _ = False

minVar :: SomeVar γ -> SomeVar γ -> SomeVar γ
minVar (SomeVar Get) _ = SomeVar Get
minVar _ (SomeVar Get)  = SomeVar Get 
minVar (SomeVar (Weaken x)) (SomeVar (Weaken y))
  = case minVar (SomeVar x) (SomeVar y) of
      SomeVar z -> SomeVar (Weaken z)
      _ -> error "minVar: panic"
minVar NoVar y = y
minVar x NoVar = x


supremum :: Dir -> [Ret γ] -> Ret γ
supremum _ [e] = e
supremum dir es = E.Var (Supremum dir es)
  -- case traverse (traverse (varTraverse _)) es of
  --                   Just cs | not (null es) ->
  --                      constPoly ((case dir of
  --                                    Max -> maximum
  --                                    Min -> minimum)
  --                                  cs)
  --                   _ -> varP (Supremum dir es)

constPoly :: Number -> Ret γ
constPoly (Number n) = (\case) <$> n

varPoly :: 'R ∈ γ -> Ret γ
varPoly = E.Var . Vari

exprToPoly :: Expr γ -> Ret γ
exprToPoly = A.eval (fmap (\case) .fromNumber) (E.Var .  Vari)

mkSuprema :: Domain γ -> (Ret γ, Ret γ)
mkSuprema (Domain los his) = (supremum Max $ map exprToPoly los,
                              supremum Min $ map exprToPoly his)

