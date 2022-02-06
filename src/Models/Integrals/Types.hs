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
import Algebra.Morphism.Polynomial.Multi hiding (constPoly)
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp)
import Models.Field (Fld(..))
import Data.Complex
import TLC.Terms (type (∈)(..), Type(..), type(×), type(⟶))

--------------------------------------------------------------------------------
-- | Types

type C = Complex Double
deriving instance Ord a => Ord (Complex a) -- yikes
  
type Rat = Fld
type RatLike α = (Ring α, Ord α, DecidableZero α, Transcendental α)

-- Map of exp(poly) to its coefficient.
-- (A "regular" coefficient)
newtype Coef γ = Coef (LinComb (Poly γ) Rat)
  deriving (Eq, Ord, Additive, Group, Show)
instance DecidableZero (Coef g) where
  isZero (Coef c) = isZero c
instance Multiplicative (Coef g) where
  one = Coef (LC.var zero)
  Coef p * Coef q = Coef (LC.fromList [ (m1 + m2, coef1 * coef2)
                                      | (m1, coef1) <- LC.toList p
                                      , (m2, coef2) <- LC.toList q ])
instance Scalable (Coef g) (Coef g) where
  (*^) = (*)
instance AbelianAdditive (Coef g) 
instance Ring (Coef g)
  
data Dir = Min | Max deriving (Eq,Ord,Show)
type Available α γ = α ∈ γ
type Var γ = 'R ∈ γ
-- deriving instance Eq (Available α γ)
deriving instance Ord (Available α γ)
-- deriving instance Show (Available α γ)
type Expr γ = A.Affine (Available 'R γ) Rat
data Elem γ = Vari (Available 'R γ) | Supremum Dir [Poly γ] | CharFun (Poly γ)
  deriving (Eq, Ord, Show)
type Poly γ = Polynomial (Elem γ) (Coef γ)
type Mono γ a = Monomial (Elem γ)
data Dumb a = a :/ a deriving Show
type DD γ a = Dumb (Poly γ)
type Ret γ a = DD γ a 

type Cond γ = Cond' (Expr γ)
data Cond' e = IsNegative { condExpr :: e }
              -- Meaning of this constructor: expression ≤ 0
              | IsZero { condExpr :: e }
              -- Meaning of this constructor: expression = 0
   deriving (Eq, Show, Functor, Foldable, Traversable)

data Domain γ = Domain { domainLoBounds, domainHiBounds :: [Expr γ] }
  deriving Show

data P γ where
  Integrate :: Domain γ -> P (γ × 'R) -> P γ
  Cond :: Cond γ -> P γ -> P γ
  Add :: P γ -> P γ -> P γ
  Div :: P γ -> P γ -> P γ
  -- Can Div be replaced by "factor"? No, because we do integration in
  -- these factors as well.
  Ret :: Poly γ -> P γ


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

instance VarTraversable Elem where
  varTraverse f = \case
    Vari x -> Vari <$> f x
    CharFun c -> CharFun <$> (traversePoly f) c
    Supremum d es -> Supremum d <$> traverse (traversePoly f) es

traversePoly :: forall f γ δ. (Applicative f)
             => (forall x. Available x γ -> f (Available x δ))
             -> Poly γ -> f (Poly δ)
traversePoly f = bitraverse (varTraverse f) (varTraverse f)

instance VarTraversable Coef where
  varTraverse f (Coef x) = Coef <$> LC.traverseVars (traversePoly f) x

instance VarTraversable P where
  varTraverse f = \case
    Div x y -> Div <$> varTraverse f x <*> varTraverse f y
    Integrate d e ->
      Integrate <$> (varTraverse f d) <*> (varTraverse (lift' f) e)
    Cond e x -> Cond <$> traverse (A.traverseVars f) e <*> varTraverse f x
    Add x y  -> Add <$> varTraverse f x <*> varTraverse f y
    Ret x -> Ret <$> traversePoly f x


deriving instance Show (P γ)

infixl 7 :/
instance (Ring a,DecidableZero a) => DecidableZero (Dumb a) where
  isZero (x :/ _) = isZero x
instance {-# OVERLAPPABLE #-} Scalable s a => Scalable s (Dumb a) where
  f *^ (x :/ y) = (f *^ x) :/ y
instance Ring a => Additive (Dumb a) where
  zero = zero :/ one
  (x :/ y) + (x' :/ y') = (x * y' + x' * y) :/ (y * y')
instance Ring a => AbelianAdditive (Dumb a)
instance Multiplicative a => Multiplicative (Dumb a) where
  one = one :/ one
  (x :/ y) * (x' :/ y') = (x * x') :/ (y * y')
instance Ring a => Group (Dumb a) where
  negate (x :/ y) = negate x :/ y
instance Ring a => Scalable (Dumb a) (Dumb a) where
  (*^) = (*)
instance Ring a => Ring (Dumb a) where
  fromInteger x = fromInteger x :/ one
instance Multiplicative a => Division (Dumb a) where
  recip (x :/ y) = y :/ x
instance Ring a => Field (Dumb a)
evalDumb :: Division x => (a -> x) -> Dumb a -> x
evalDumb f (x :/ y) = f x / f y

----------------------------------
-- | Smart constructors


conds_ :: [Cond γ] -> P γ -> P γ
conds_ cs e = foldr Cond e cs

isConstantCoef :: Coef γ -> Maybe Rat
isConstantCoef (Coef l) = case LC.toList l of
  [(v,x)] | v == zero -> Just x
  _ -> Nothing

isConstPoly :: Poly γ -> Maybe Rat
isConstPoly es = case isConstant es of
  Nothing -> Nothing
  Just coef -> isConstantCoef coef

  
isPositive,isNegative :: Expr γ -> Cond γ
isPositive e = isNegative (negate e)
isNegative e = IsNegative e


-- Domain without restriction
full :: Domain γ
full = Domain [] []

lessThan, greaterThan :: Expr γ -> Expr γ -> Cond γ
t `lessThan` u = isNegative (t - u)
t `greaterThan` u = u `lessThan` t

exponential :: Poly γ -> Poly γ
exponential p = case isConstPoly p of
  Just c -> constPoly (exp c)
  Nothing -> Coef (LC.var p) *^ one

charfun :: Poly γ -> Poly γ
charfun e = case isConstPoly e of
  Nothing -> varP (CharFun e)
  Just x -> if x <= zero then one else zero

supremum :: Dir -> [Poly γ] -> Poly γ
supremum _ [e] = e
supremum dir es = case traverse isConstPoly es of
                  Just cs | not (null es) ->
                     constPoly ((case dir of
                                   Max -> maximum
                                   Min -> minimum)
                                 cs)
                  _ -> varP (Supremum dir es)

constCoef :: forall γ. Rat -> Coef γ
constCoef x = Coef (x *^ LC.var zero) -- x * Exp 0

constPoly :: Rat -> Poly γ
constPoly = Multi.constPoly . constCoef

varPoly :: Var γ -> Poly γ
varPoly = varP . Vari

mkSuprema :: Domain γ -> (Poly γ, Poly γ)
mkSuprema (Domain los his) = (supremum Max $ map exprToPoly los,
                                 supremum Min $ map exprToPoly his)


exprToPoly :: Expr γ -> Poly γ
exprToPoly = A.eval constPoly  (monoPoly .  varM . Vari) 

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
instance Scalable (Poly γ) (P γ) where
  p *^ q = Ret p * q
instance Additive (P γ) where
  zero = Ret zero
  (Ret z) + x | isZero z = x
  x + (Ret z) | isZero z = x
  x + y = Add x y

instance Division (P γ) where
  (Ret z) / _ | isZero z = Ret $ zero
  (Cond c n) / d = Cond c (n / d) -- this exposes conditions to the integrators in the denominator
  p1 / p2 = Div p1 p2


-----------------------------------------------------
-- | Normalising substitutions of variables to polys

evalCoef :: forall γ δ ζ. (Var γ -> Var δ) -> SubstP δ ζ -> Coef γ -> Poly ζ
evalCoef v f (Coef c)
  = LC.eval (constCoef @ζ) (exponential . evalPoly v f) c

evalPoly :: forall γ δ ζ. (Var γ -> Var δ) -> SubstP δ ζ -> Poly γ -> Poly ζ
evalPoly v f = eval (evalCoef v f) (evalElem v f) 

evalElem :: forall γ δ ζ. (Var γ -> Var δ) -> SubstP δ ζ -> Elem γ -> Poly ζ
evalElem v f =
  let evP :: Poly γ -> Poly ζ
      evP = evalPoly v f
  in \case Supremum dir es -> supremum dir (evP <$> es)
           Vari x -> f (v x)
           CharFun x -> charfun (evP x)

type SubstP γ δ = Var γ -> Poly δ

substPoly :: SubstP γ δ -> Poly γ -> Poly δ
substPoly f = evalPoly id f
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

substP :: SubstE γ δ -> P γ -> P δ
substP f p0 = case p0 of
  Ret e -> Ret (substPoly (exprToPoly . f) e)
  Add p1 p2 -> substP f p1 + substP f p2
  Div p1 p2 -> substP f p1 / substP f p2
  Cond c p -> Cond (substCond f c) (substP f p)
  Integrate d p -> Integrate (substDomain f d) (substP (wkSubst f) p) -- integrations are never simplified by substitution

wkExpr :: Expr γ -> Expr (γ × β)
wkExpr = substExpr (A.var . Weaken) 

wkP :: P γ -> P (γ × α)
wkP = substP $ \i -> A.var (Weaken i) 


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
