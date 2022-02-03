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
module Models.Integrals.Types where

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


--------------------------------------------------------------------------------
-- | Types

type C = Complex Double
deriving instance Ord a => Ord (Complex a) -- yikes
  
type Rat = Fld
type RatLike α = (Ring α, Ord α, DecidableZero α, Transcendental α)

-- Map of exp(poly) to its coefficient.
-- (A "regular" coefficient)
newtype Coef γ α = Coef (LinComb (Poly γ α) α)
  deriving (Eq, Ord, Additive, Group, Show)
instance RatLike a => DecidableZero (Coef g a) where
  isZero (Coef c) = isZero c
instance RatLike a => Multiplicative (Coef g a) where
  one = Coef (LC.var zero)
  Coef p * Coef q = Coef (LC.fromList [ (m1 + m2, coef1 * coef2)
                                      | (m1, coef1) <- LC.toList p
                                      , (m2, coef2) <- LC.toList q ])
instance RatLike a => Scalable (Coef g a) (Coef g a) where
  (*^) = (*)
instance RatLike a => AbelianAdditive (Coef g a) 
instance RatLike a => Ring (Coef g a)
  
data Dir = Min | Max deriving (Eq,Ord,Show)
data Available α γ where
  Here :: Available α (γ, α)
  There :: Available α γ -> Available α (γ, β)
deriving instance Eq (Available α γ)
deriving instance Ord (Available α γ)
deriving instance Show (Available α γ)
type Expr γ α = A.Affine (Available α γ) α
data Elem γ α = Vari (Available α γ) | Supremum Dir [Poly γ α] | CharFun (Poly γ α)
  deriving (Eq, Ord, Show)
type Poly γ a = Polynomial (Elem γ a) (Coef γ a)
type Mono γ a = Monomial (Elem γ a)
data Dumb a = a :/ a deriving Show
type DD γ a = Dumb (Poly γ a)
type Ret γ a = DD γ a 

type Cond γ a = Cond' (Expr γ a)
data Cond' e = IsNegative { condExpr :: e }
              -- Meaning of this constructor: expression ≤ 0
              | IsZero { condExpr :: e }
              -- Meaning of this constructor: expression = 0
   deriving (Eq, Show, Functor, Foldable, Traversable)

data Domain γ α = Domain { domainLoBounds, domainHiBounds :: [Expr γ α] }
  deriving Show

data P γ α where
  Integrate :: d ~ Rat => Domain γ d -> P (γ, d) α -> P γ α
  Cond :: (DecidableZero a, Ord a, Ring a) => Cond γ a -> P γ a -> P γ a
  Add :: P γ α -> P γ α -> P γ α
  Div :: P γ α -> P γ α -> P γ α
  -- Can Div be replaced by "factor"? No, because we do integration in
  -- these factors as well.
  Ret :: Poly γ α -> P γ α

lift' :: Applicative f
  => (forall v. Available v γ -> f (Available v δ))
  -> (forall v. Available v (γ, α) -> f (Available v (δ, α)))
lift' _ (Here) = pure Here
lift' f (There x) = There <$> (f x)

class VarTraversable t where
  varTraverse :: (Ord a, Applicative f)
    => (forall x. Available x γ -> f (Available x δ))
    -> t γ a -> f (t δ a)

instance VarTraversable Domain where
 varTraverse f (Domain los his)
  = Domain <$> traverse (A.traverseVars f) los <*>
               traverse (A.traverseVars f) his

instance VarTraversable Elem where
  varTraverse f = \case
    Vari x -> Vari <$> f x
    CharFun c -> CharFun <$> (traversePoly f) c
    Supremum d es -> Supremum d <$> traverse (traversePoly f) es

traversePoly :: forall a f γ δ. (Ord a, Applicative f)
             => (forall x. Available x γ -> f (Available x δ))
             -> Poly γ a -> f (Poly δ a)
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


deriving instance (RatLike α, Show α) => Show (P γ α)

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


isConstantCoef :: RatLike α => Coef γ α -> Maybe α
isConstantCoef (Coef l) = case LC.toList l of
  [(v,x)] | v == zero -> Just x
  _ -> Nothing

isConstPoly :: RatLike α => Poly γ α -> Maybe α
isConstPoly es = case isConstant es of
  Nothing -> Nothing
  Just coef -> isConstantCoef coef

  
isPositive,isNegative :: RatLike a => Expr γ a -> Cond γ a
isPositive e = isNegative (negate e)
isNegative e = IsNegative e


-- Domain without restriction
full :: Domain γ x
full = Domain [] []

lessThan, greaterThan :: RatLike a => Expr γ a -> Expr γ a -> Cond γ a
t `lessThan` u = isNegative (t - u)
t `greaterThan` u = u `lessThan` t

exponential :: RatLike α => Poly γ α -> Poly γ α
exponential p = case isConstPoly p of
  Just c -> constPoly (exp c)
  Nothing -> Coef (LC.var p) *^ one

charfun :: RatLike α => Poly γ α -> Poly γ α
charfun e = case isConstPoly e of
  Nothing -> varP (CharFun e)
  Just x -> if x <= zero then one else zero

supremum :: RatLike α => Dir -> [Poly γ α] -> Poly γ α
supremum _ [e] = e
supremum dir es = case traverse isConstPoly es of
                  Just cs | not (null es) ->
                     constPoly ((case dir of
                                   Max -> maximum
                                   Min -> minimum)
                                 cs)
                  _ -> varP (Supremum dir es)

constCoef :: forall γ a. RatLike a => a -> Coef γ a
constCoef x = Coef (x *^ LC.var zero) -- x * Exp 0

constPoly :: RatLike a => a -> Poly γ a
constPoly = Multi.constPoly . constCoef

varPoly :: RatLike α => Available α γ -> Poly γ α
varPoly = varP . Vari

mkSuprema :: RatLike α => Domain γ α -> (Poly γ α, Poly γ α)
mkSuprema (Domain los his) = (supremum Max $ map exprToPoly los,
                                 supremum Min $ map exprToPoly his)


exprToPoly :: RatLike α => Expr γ α -> Poly γ α
exprToPoly = A.eval constPoly  (monoPoly .  varM . Vari) 

----------------------------
-- Instances

instance Scalable C (Poly γ C) where
  x *^ p = constCoef @γ x *^ p

instance RatLike α => Multiplicative (P γ α) where
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

instance RatLike a => AbelianAdditive (P γ a)
instance RatLike a => Group (P γ a) where
  negate = (* (Ret (negate one)))
instance RatLike a => Scalable (Poly γ a) (P γ a) where
  p *^ q = Ret p * q
instance RatLike a => Additive (P γ a) where
  zero = Ret zero
  (Ret z) + x | isZero z = x
  x + (Ret z) | isZero z = x
  x + y = Add x y

instance RatLike a => Division (P γ a) where
  (Ret z) / _ | isZero z = Ret $ zero
  (Cond c n) / d = Cond c (n / d) -- this exposes conditions to the integrators in the denominator
  p1 / p2 = Div p1 p2


-----------------------------------------------------
-- | Normalising substitutions of variables to polys

evalCoef :: forall α β γ δ ζ. RatLike β => RatLike α
         => (Available α γ -> Available β δ)
         -> (α -> β) -> SubstP δ ζ -> Coef γ α -> Poly ζ β
evalCoef v fc f (Coef c)
  = LC.eval (constCoef @ζ . fc) (exponential . evalPoly v fc f) c

evalPoly :: forall α β γ δ ζ. RatLike β => RatLike α
         => (Available α γ -> Available β δ)
         -> (α -> β) -> SubstP δ ζ -> Poly γ α -> Poly ζ β
evalPoly v fc f = eval (evalCoef v fc f) (evalElem v fc f) 

evalElem :: forall α β γ δ ζ. RatLike β => RatLike α
         => (Available α γ -> Available β δ)
         -> (α -> β) -> SubstP δ ζ -> Elem γ α -> Poly ζ β
evalElem v fc f =
  let evP :: Poly γ α -> Poly ζ β
      evP = evalPoly v fc f
  in \case Supremum dir es -> supremum dir (evP <$> es)
           Vari x -> f (v x)
           CharFun x -> charfun (evP x)

type SubstP γ δ = forall α. RatLike α => Available α γ -> Poly δ α

substPoly :: RatLike α => SubstP γ δ -> Poly γ α -> Poly δ α
substPoly f = evalPoly id id f

----------------------------------------------------------------
-- Normalising substitutions of variables to affine expressions

type SubstE γ δ = forall α. Ring α => Available α γ -> Expr δ α

wkSubst :: Ring α => SubstE γ δ -> SubstE (γ, α) (δ, α)
wkSubst f = \case
  Here -> A.var Here 
  There x -> A.mapVars There (f x)

substExpr :: (DecidableZero α, Ring α) => SubstE γ δ ->  Expr γ α -> Expr δ α
substExpr = A.subst

substCond :: DecidableZero α => Ring α => SubstE γ δ -> Cond γ α -> Cond δ α
substCond f = fmap (substExpr f)

substDomain :: (DecidableZero α, Ring α)
            => SubstE γ δ -> Domain γ α -> Domain δ α
substDomain f (Domain lo hi) = Domain
                                 (substExpr f <$> lo)
                                 (substExpr f <$> hi)

substP :: RatLike x => SubstE γ δ -> P γ x -> P δ x
substP f p0 = case p0 of
  Ret e -> Ret (substPoly (exprToPoly . f) e)
  Add p1 p2 -> substP f p1 + substP f p2
  Div p1 p2 -> substP f p1 / substP f p2
  Cond c p -> cond (substCond f c) (substP f p)
  Integrate d p -> Integrate (substDomain f d) (substP (wkSubst f) p) -- integrations are never simplified by substitution

wkExpr :: RatLike α => Expr γ α -> Expr (γ, β) α
wkExpr = substExpr (A.var . There) 

wkP :: DecidableZero x => Transcendental x => Ord x => P γ x -> P (γ, α) x
wkP = substP $ \i -> A.var (There i) 


-- | Normalising condition, placing the shallowest conditions first,
-- so that they can be exposed to integrals which are able to resolve them.
cond :: RatLike a => Cond γ a -> P γ a -> P γ a
cond (IsNegative (A.Affine k0 vs)) e | k0 <= zero, vs == zero = e
cond _ (Ret z) | isZero z = Ret $ zero
cond c (Cond c' e) | c == c' = cond c e
cond c (Cond c' e) = if (deepest c) `shallower` (deepest c')
                     then Cond c (Cond c' e)
                     else Cond c' (cond c e)
cond c e = Cond c e



deepest :: Cond γ α -> SomeVar γ
deepest c = case condExpr c of
   (A.Affine _ e) -> case LC.toList e of
     xs@(_:_) -> foldr1 minVar . map SomeVar . map fst $ xs
     [] -> NoVar

shallower :: SomeVar γ -> SomeVar γ -> Bool
SomeVar Here `shallower` _ = False
SomeVar (There _) `shallower` SomeVar Here = True
SomeVar (There x) `shallower` SomeVar (There y)
  = SomeVar x `shallower` SomeVar y
NoVar `shallower` (SomeVar _) = True
(SomeVar _) `shallower` NoVar = True
_ `shallower` _ = False

data SomeVar γ where
  SomeVar :: Available v γ -> SomeVar γ
  NoVar :: SomeVar γ

minVar :: SomeVar γ -> SomeVar γ -> SomeVar γ
minVar (SomeVar Here) _ = SomeVar Here
minVar _ (SomeVar Here)  = SomeVar Here 
minVar (SomeVar (There x)) (SomeVar (There y))
  = case minVar (SomeVar x) (SomeVar y) of
      SomeVar z -> SomeVar (There z)
      _ -> error "minVar: panic"
minVar NoVar y = y
minVar x NoVar = x
