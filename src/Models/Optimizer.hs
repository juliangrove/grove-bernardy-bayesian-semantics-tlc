{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Models.Optimizer where

import Data.List (intercalate, nub)
import Data.Ratio
import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import qualified Algebra.Morphism.LinComb as LC
import Algebra.Morphism.Polynomial.Multi
import Algebra.Morphism.Exponential
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt, exp)
import TLC.Terms hiding ((>>), u, Con)
import Algebra.Linear ((*<))
import Models.Field (BinOp(..), Fld(..), half)
import qualified Models.Field
import Algebra.Linear.Chebyshev (chebIntegral)
import Data.Complex

type C = Complex Double
deriving instance Ord C -- yikes
instance (Field a, Ord a, Show a) => Pretty (Complex a) where
  pretty (a :+ b) _ | b < 10e-15 = show a
                    | otherwise = show a ++ "+" ++ show b ++ "i"
  
type Rat = Fld

data Dir = Min | Max deriving (Eq,Ord)
type Expr γ α = A.Affine (Available α γ) α
data Elem γ α = Vari (Available α γ) | Exp (Poly γ α) | MinMax Dir [Poly γ α] deriving (Eq,Ord)
type Poly γ a = Polynomial (Elem γ a) a
type Mono γ a = Monomial (Elem γ a)
type DD γ a = Dumb (Poly γ a)
type Ret γ a = DD γ a 

data Cond γ = IsNegative { condExpr :: Expr γ Rat }
              -- Meaning of this constructor: expression ≤ 0
              -- Example: u ≤ v is represented by @IsNegative [(1, u), (-1, v)]@
            | IsZero { condExpr :: Expr γ Rat }
              -- Meaning of this constructor: expression = 0
              -- Example: u = v is represented by @IsZero [(1, u), (-1, v)]@
   deriving (Eq)


data Dumb a = a :/ a
infixl 7 :/

  
instance Pretty a => Show (DD () a) where
  show x = showDumb (\case) x Mathematica 

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
instance Ring a => Field (Dumb a) where
  fromRational x = fromInteger (numerator x) :/ fromInteger (denominator x)


evalPoly :: forall α β γ δ ζ. Transcendental β => Ord β => Ring β => Transcendental α => (Ord α, Ring α, Eq α)
         => (Available α γ -> Available β δ)
         -> (α -> β)
         -> (forall x. (Ring x, Ord x) => Available x δ -> Poly ζ x)
         -> Poly γ α -> Poly ζ β
evalPoly v fc f = eval fc (evalElem v fc f) 

evalElem :: forall α β γ δ ζ. Transcendental β => Ord β => Ring β => Transcendental α => (Ord α, Ring α, Eq α)
         => (Available α γ -> Available β δ)
         -> (α -> β)
         -> (forall x. (Ring x, Ord x) => Available x δ -> Poly ζ x)
         -> Elem γ α -> Poly ζ β
evalElem v fc f =
  let evP :: Poly γ α -> Poly ζ β
      evP = evalPoly v fc f
  in \case
        MinMax dir es -> minMax dir (evP <$> es)
        (Vari x) -> f (v x)
        (Exp p) -> exponential (evP p)

exponential :: Transcendental α => Ord α => Ring α => Poly γ α -> Poly γ α
exponential p = case isConstant p of
  Just c -> constPoly (exp c)
  Nothing -> varP (Exp p)
  
minMax :: (Additive α, Ord α, Multiplicative α) =>
            Dir -> [Polynomial (Elem γ α) α] -> Polynomial (Elem γ α) α
minMax dir es = case traverse isConstant es of
                  Just cs -> constPoly ((case dir of Max -> maximum; Min -> minimum) cs)
                  Nothing -> varP (MinMax dir es)

collapseRat :: (Available Rat γ -> Available C δ) -> Poly γ Rat -> Poly δ C
collapseRat v = evalPoly v (Models.Field.eval @C) varPoly

collapseRat' :: (Available Rat γ -> Available C δ) -> Ret γ Rat -> Ret δ C
collapseRat' v (x :/ y) = collapseRat v x :/ collapseRat v y

class (Eq a, Field a) => Pretty a where
  pretty :: a -> ShowType -> String

instance Pretty Rat where
  pretty = showRat

showRat :: Rat -> ShowType -> String
showRat (Con x) | numerator x == 0 = const "0"
showRat (Con x) | denominator x == 1 = const $ show $ numerator x
showRat (Con x) = \case
      LaTeX -> "\\frac{" ++ num ++ "}{" ++ den ++ "}"
      _ -> parens $ num ++ "/" ++ den
  where num = show $ numerator x
        den = show $ denominator x
showRat (Pi) = \_ -> "pi"
showRat (Pow x 0.5) = \case
  Maxima -> "sqrt" ++ parens (showRat (x) Maxima)
  Mathematica -> "Sqrt" ++ brackets (showRat (x) Mathematica)
  LaTeX -> "\\sqrt" ++ braces (showRat (x) LaTeX)
showRat (Op Plus x y) = \st -> showRat x st ++ " + " ++ showRat y st
-- showRat (Op Times x y@(Inject _)) = \st -> showRat x st ++
--                                             case st of
--                                               LaTeX -> showRat y st
--                                               _ -> " * " ++ showRat y st
showRat (Op Times x y) = \st -> showRat x st ++ " * " ++ showRat y st
showRat (Pow x n) = \st -> parens (showRat x st) ++ "^" ++
                           (if n < 0 then (case st of
                                             LaTeX -> braces
                                             _ -> parens) else id) (show n)

data Domain γ α = Domain { domainConditions :: [Cond (γ, α)]
                         , domainLoBounds, domainHiBounds :: [Expr γ α] }

isPositive :: Expr γ Rat -> Cond γ
isPositive e = isNegative (negate e)

isNegative :: Expr γ Rat -> Cond γ
isNegative e = IsNegative e

lessThan :: Expr γ Rat -> Expr γ Rat -> Cond γ
t `lessThan` u = isNegative (t - u)

greaterThan :: Expr γ Rat -> Expr γ Rat -> Cond γ
t `greaterThan` u = u `lessThan` t

domainToConditions :: Expr γ Rat -> Domain γ Rat -> P γ α -> P γ α
domainToConditions e0 = \case
  Domain [] [] [] -> id
  Domain (c:cs) los his ->
    Cond (substCond (\Here -> e0) c) . domainToConditions e0 (Domain cs los his)
  Domain cs (e:los) his ->
    Cond (e `lessThan` e0) . domainToConditions e0 (Domain cs los his)
  Domain cs los (e:his) ->
    Cond (e0 `lessThan` e) . domainToConditions e0 (Domain cs los his)

data Available α γ where
  Here :: Available α (γ, α)
  There :: Available α γ -> Available α (γ, β)
deriving instance Eq (Available α γ)
deriving instance Ord (Available α γ)
deriving instance Show (Available α γ)

data Expr γ α = Expr α [(α, Available α γ)] deriving Eq
  -- Linear combination. List of coefficients and variables (α is a Ring).
  -- Example: u - v is represented by @Expr 0 [(1, u), (-1,v)]@.

type Mono γ a = Exponential (Map (Either (Available a γ) (Poly γ a)) Natural)
deriving instance Eq a => Eq (Mono γ a)
deriving instance Ord a => Ord (Mono γ a)

-- map each monomial to its coefficient
newtype Poly γ a = P (Map (Mono γ a) a)
  deriving (Additive, Group, AbelianAdditive, Ord, Eq)
deriving instance (Ord a, Ring a) => Module a (Poly γ a)

instance (Eq a, Ord a, Ring a) => Multiplicative (Poly γ a) where
  one = P (M.singleton one one)
  P p * P q = P (M.fromListWith (+)
                 [ (m1 * m2, coef1 * coef2)
                 | (m1, coef1) <- M.toList p, (m2, coef2) <- M.toList q ])

instance (Eq a, Ord a,Ring a) => Module (Poly γ a) (Poly γ a) where
  (*^) = (*)

instance (Eq a, Ord a,Ring a) => Ring (Poly γ a) where

-- | Induced vector space structure over Expr γ α:

-- | Multiplication by a scalar (expresions are linear)
(*<) :: Ring α => α -> Expr γ α -> Expr γ α
c *< Expr k0 xs = Expr (c * k0) [ (c * c', v) | (c', v) <- xs ]

instance Additive α => Additive (Expr γ α) where
  (Expr c1 xs1) + (Expr c2 xs2) = Expr (c1 + c2) (xs1 ++ xs2)
  zero = Expr zero []

data Cond γ = IsNegative { condExpr :: (Expr γ Rat) }
              -- Meaning of this constructor: expression ≤ 0
              -- Example: u ≤ v is represented by @IsNegative [(1, u), (-1, v)]@
            | IsZero { condExpr :: (Expr γ Rat) }
              -- Meaning of this constructor: expression = 0
              -- Example: u = v is represented by @IsZero [(1, u), (-1, v)]@
   deriving (Eq)

-- | Restrict the bounds by moving the bounds. Also return conditions that
-- ensure that the bounds are in the right order.
restrictDomain :: α ~ Rat => Cond (γ, α) -> Domain γ α -> (Domain γ α, [Cond γ])
restrictDomain c (Domain cs los his) = case solve' c of -- version with solver
  (LT, e) -> (Domain cs los (e:his), [ lo `lessThan` e | lo <- los ])
  (GT, e) -> (Domain cs (e:los) his, [ e `lessThan` hi | hi <- his ])
  _ -> error "restrictDomain: cannot be called/(1) on equality condition"

data P γ α where
  Integrate :: d ~ Rat => Domain γ d -> P (γ, d) α -> P γ α
  Cond :: Cond γ -> P γ α -> P γ α
  Add :: P γ α -> P γ α -> P γ α
  Div :: P γ α -> P γ α -> P γ α -- Can this be replaced by "factor" ? No, because we do integration in these factors as well.
  Ret :: Ret γ α -> P γ α

instance (Ord α, Transcendental α) => Multiplicative (P γ α) where
  one = Ret one
  (*) = multP

instance (Ord a, Ring a, DecidableZero a) => AbelianAdditive (P γ a)
instance (Transcendental a, Ord a, DecidableZero a) => Group (P γ a) where
  negate = (* (Ret (negate one)))
instance (Transcendental a, Ord a) => Scalable (Poly γ a) (P γ a) where
  p *^ q = retPoly p * q
instance (Ord a, Ring a, DecidableZero a) => Additive (P γ a) where
  zero = Ret zero
  (+) = adding
instance (Ord a, Transcendental a, DecidableZero a) => Division (P γ a) where
  (/) = divide

multP :: (Ord α, Transcendental α) => P γ α -> P γ α -> P γ α
multP (Integrate d p1) (wkP -> p2) = Integrate d $ multP p1 p2
multP (Cond c p1) p2 = Cond c $ multP p1 p2
multP (Ret e) (Integrate d p) = Integrate d $ multP (wkP $ Ret e) p
multP (Ret e) (Cond c p) = Cond c $ multP (Ret e) p
multP (Ret e1) (Ret e2) = Ret $ e1 * e2
multP (Add p1 p1') p2 = Add (multP p1 p2) (multP p1' p2)
multP p1 (Add p2 p2') = Add (multP p1 p2) (multP p1 p2')
multP (Div p1 p1') (Div p2 p2') = Div (multP p1 p1') (multP p2 p2')
multP (Div p1 p1') p2 = Div (multP p1 p2) p1'
multP p1 (Div p2 p2') = Div (multP p1 p2) p2'
  
type Subst γ δ = forall α. Ring α => Available α γ -> Expr δ α

wkSubst :: Ring α => Subst γ δ -> Subst (γ, α) (δ, α)
wkSubst f = \case
  Here -> A.var Here 
  There x -> A.mapVars There (f x)

substExpr :: Subst γ δ -> forall α. Ring α => Expr γ α -> Expr δ α
substExpr = A.subst

exprToPoly :: forall γ α. Ord α => (Eq α, Ring α) => Expr γ α -> Poly γ α
exprToPoly = A.eval constPoly (monoPoly . varMono) 

varMono :: Available α γ -> Mono γ α
varMono = varM . Vari

varPoly :: Ring α => Available α γ -> Poly γ α
varPoly = varP . Vari

substElem :: Transcendental α => (Ord α, Ring α, Eq α)
          => Subst γ δ -> Elem γ α -> Poly δ α
substElem f = substElem' (exprToPoly . f)

substElem' :: Transcendental α => (Ord α, Ring α, Eq α)
           => (forall x. (Ring x, Ord x) => Available x γ -> Poly δ x)
           -> Elem γ α -> Poly δ α
substElem' f = evalElem id id f

substRet :: (Ord f, Ord e, Ord c, Ring c)
         => Substitution e f c -> Dumb (Polynomial e c) -> Dumb (Polynomial f c)
substRet f (x :/ y) = subst f x :/ subst f y
              
substCond :: Subst γ δ -> Cond γ -> Cond δ
substCond f (IsNegative e) = IsNegative $ substExpr f e
substCond f (IsZero e) = IsZero $ substExpr f e

substDomain :: Ring α => Subst γ δ -> Domain γ α -> Domain δ α
substDomain f (Domain c lo hi) = Domain
                                 (substCond (wkSubst f) <$> c)
                                 (substExpr f <$> lo)
                                 (substExpr f <$> hi)

substP :: Ord x => Eq x => Transcendental x => Subst γ δ -> P γ x -> P δ x
substP f p0 = case p0 of
  Ret e -> Ret (substRet (substElem f) e)
  Add (substP f -> p1) (substP f -> p2) -> Add p1 p2
  Div (substP f -> p1) (substP f -> p2) -> Div p1 p2
  Cond c p -> Cond (substCond f c) (substP f p)
  Integrate d p -> Integrate (substDomain f d) (substP (wkSubst f) p)

wkP :: Transcendental x => Ord x => P γ x -> P (γ, α) x
wkP = substP $ \i -> A.var (There i) 

type family Eval γ where
  Eval 'R = Rat
  Eval 'Unit = ()
  Eval (γ × α) = (Eval γ, Eval α)

pattern NNVar :: Available (Eval α) (Eval γ) -> NF γ α
pattern NNVar i <- Neu (NeuVar (evalVar -> i))
pattern Equ :: forall (γ :: Type) (α :: Type).
                 () =>
                 forall (α1 :: Type) (α2 :: Type).
                 ((α2 ⟶ (α1 ⟶ α)) ~ ('R ':-> ('R ⟶ 'R))) =>
                 NF γ α2 -> NF γ α1 -> NF γ α
pattern Equ x y = Neu (NeuApp (NeuApp (NeuCon (General EqRl)) x) y)
pattern EqVars :: 'R ∈ γ -> 'R ∈ γ -> NF γ 'R
pattern EqVars i j = Neu (NeuApp (NeuApp (NeuCon (General EqRl))
                                  (Neu (NeuVar i))) (Neu (NeuVar j)))
pattern Mults :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Mults x y = Neu (NeuApp (NeuApp (NeuCon (General Mult)) x) y)
pattern Adds :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Adds x y = Neu (NeuApp (NeuApp (NeuCon (General Addi)) x) y)
pattern MultsVar :: NF γ 'R -> 'R ∈ γ -> NF γ 'R
pattern MultsVar x j = Neu (NeuApp
                            (NeuApp (NeuCon (General Mult)) x) (Neu (NeuVar j)))
pattern InEqVars :: 'R ∈ γ -> 'R ∈ γ -> NF γ 'R
pattern InEqVars i j = Neu (NeuApp (NeuCon (General Indi))
                            (Neu (NeuApp (NeuApp (NeuCon (Special GTE))
                                          (Neu (NeuVar i)))
                                  (Neu (NeuVar j)))))
pattern InEq :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern InEq x y = Neu (NeuApp (NeuCon (General Indi))
                            (Neu (NeuApp (NeuApp (NeuCon (Special GTE))
                                          x)
                                  y)))
pattern Normal :: forall (γ :: Type) (α :: Type).
                    () =>
                    forall (α2 :: Type) (α3 :: Type) (α4 :: Type) (β :: Type).
                    ((α3 ⟶ (α2 ⟶ α)) ~ (('R × 'R) ':-> (('R ⟶ 'R) ⟶ 'R)),
                     α3 ~ (α4 ':× β), α4 ~ 'R, β ~ 'R) =>
                    Rational -> Rational -> NF γ α2 -> NF γ α
pattern Normal x y f = Neu (NeuApp (NeuApp (NeuCon (General Nml))
                                    (NFPair (Neu (NeuCon (General (Incl x))))
                                     (Neu (NeuCon (General (Incl y)))))) f)

pattern Cauchy :: forall (γ :: Type) (α :: Type).
                    () =>
                    forall (α1 :: Type) (α2 :: Type) (α3 :: Type) (β :: Type).
                    ((α2 ⟶ (α1 ⟶ α)) ~ (('R × 'R) ':-> (('R ⟶ 'R) ⟶ 'R)),
                     α2 ~ (α3 ':× β), α3 ~ 'R, β ~ 'R) =>
                    Rational -> Rational -> NF γ α1 -> NF γ α
pattern Cauchy x y f = Neu (NeuApp (NeuApp (NeuCon (General Cau))
                                    (NFPair (Neu (NeuCon (General (Incl x))))
                                     (Neu (NeuCon (General (Incl y)))))) f)
pattern Quartic :: forall (γ :: Type) (α :: Type).
                     () =>
                     forall (α2 :: Type) (α3 :: Type) (α4 :: Type) (β :: Type).
                     ((α3 ⟶ (α2 ⟶ α)) ~ (('R × 'R) ':-> (('R ⟶ 'R) ⟶ 'R)),
                      α3 ~ (α4 ':× β), α4 ~ 'R, β ~ 'R) =>
                     Rational -> Rational -> NF γ α2 -> NF γ α
pattern Quartic x y f = Neu (NeuApp (NeuApp (NeuCon (General Qua))
                                    (NFPair (Neu (NeuCon (General (Incl x))))
                                     (Neu (NeuCon (General (Incl y)))))) f)
pattern Uniform :: forall (γ :: Type) (α :: Type).
                     () =>
                     forall (α2 :: Type) (α3 :: Type) (α4 :: Type) (β :: Type).
                     ((α3 ⟶ (α2 ⟶ α)) ~ (('R × 'R) ':-> (('R ⟶ 'R) ⟶ 'R)),
                      α3 ~ (α4 ':× β), α4 ~ 'R, β ~ 'R) =>
                     Rational -> Rational -> NF γ α2 -> NF γ α
pattern Uniform x y f = Neu (NeuApp (NeuApp (NeuCon (General Uni))
                                     (NFPair (Neu (NeuCon (General (Incl x))))
                                      (Neu (NeuCon (General (Incl y)))))) f)
pattern Lesbegue :: NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Lesbegue f = Neu (NeuApp (NeuCon (General Les)) f)
pattern Divide :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Divide x y = Neu (NeuApp (NeuApp (NeuCon (General Divi)) x) y)
pattern NNCon :: forall (γ :: Type) (α :: Type).
                   () =>
                   (α ~ 'R) => Rational -> NF γ α
pattern NNCon x = Neu (NeuCon (General (Incl x)))

evalP :: NF 'Unit 'R -> P () Rat
evalP = evalP'

retPoly :: Ord a => Ring a => Poly γ a -> P γ a
retPoly = Ret . (:/ one)

evalP' :: NF γ 'R -> P (Eval γ) Rat
evalP' = \case
  NNCon x -> retPoly $ constPoly (fromRational x)
  Neu (NeuApp (NeuCon (General Indi)) (Neu (NeuCon (Logical Tru)))) -> one
  Neu (NeuApp (NeuApp (NeuCon (General EqRl))
               (Adds (NNVar i) (NNVar j))) (NNVar k)) ->
    Cond (IsZero $ A.var i + A.var j - A.var k) $ one
  EqVars (evalVar -> i) (evalVar -> j) ->
    Cond (IsZero $ A.var i - A.var j) $ one
  InEqVars (evalVar -> i) (evalVar -> j) ->    
    Cond (IsNegative $ A.var j - A.var i) $ one
  Equ (NNVar i) (NNCon (fromRational -> x)) ->
    Cond (IsZero $ A.constant x - A.var i) $ one
  InEq (NNVar i) (NNCon (fromRational -> x)) ->
    Cond (IsNegative $ A.constant x - A.var i) $ one
  Adds (evalP' -> x) (evalP' -> y) -> Add x y
  Mults (evalP' -> x) (evalP' -> y) -> multP x y
  Normal (fromRational -> μ) (fromRational -> σ) f ->
    Integrate full $ multP
    (retPoly $ (:/ one) $ constPoly (one / (σ * sqrt2pi)) * exponential (constPoly (negate half) * (sqr ((recip σ) *^ (constPoly μ - varPoly Here)))))
    (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
    where sqrt2pi = sqrt (2 * pi)
  Cauchy (fromRational -> x0) (fromRational -> γ) f ->
    Integrate full $ Div (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))  
    (retPoly $ (constPoly (pi * γ) * (one + sqr ((one/γ) *^ (varPoly Here - constPoly x0)))))
  Quartic (fromRational -> μ) (fromRational -> σ) f ->
    Integrate (Domain [] [A.constant (μ - a)] [A.constant (μ + a)]) $ multP
    (retPoly $ (constPoly $ fromRational (15 % 16) / (a ^+ 5)) * ((varPoly Here - constPoly μ) - constPoly a) ^+ 2 * ((varPoly Here - constPoly μ) + constPoly a) ^+ 2)
    (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
    where sqrt7 = sqrt 7
          a = sqrt7 * σ
  Uniform (fromRational -> x) (fromRational -> y) f ->
    Integrate (Domain [] [A.constant x] [A.constant y]) $ multP
    (retPoly $ constPoly (1 / (y - x)))
    (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Lesbegue f -> Integrate (Domain [] [] []) $
                (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Neu (NeuVar (evalVar -> i)) -> retPoly $ varPoly i
  Divide x y -> Div (evalP' x) (evalP' y)
  t -> error ("evalP': don't know how to handle: " ++ (show . nf_to_λ) t)

sqr :: Multiplicative a => a -> a
sqr x = x * x
          
evalVar :: α ∈ γ -> Available (Eval α) (Eval γ)
evalVar = \case
  Get -> Here
  Weaken (evalVar -> i) -> There i

data ShowType = Maxima | Mathematica | LaTeX

type Vars γ  = forall v. Available v γ -> String

showExpr :: Vars γ -> Expr γ Rat -> ShowType -> String
showExpr v (A.Affine k0 xs) st
  = intercalate " + " $ (if k0 /= 0 || xs == zero then [showRat k0 st] else []) ++
    [ (if c /= one then parens else id) $
      let binOp' = case st of {LaTeX -> ""; _ -> " * "}
      in (if (c /= one && c /= -1) || xs == zero
          then showRat c st ++ binOp'
          else "") ++
         ((if c == -1 then ("-" ++) else id) (v x)) | (x,c) <- LC.toList xs ]
  
showExp :: Int -> String -> String
showExp e
  | e == 1 = id
  | otherwise = (++ "^" ++ show e)

                
showElem :: Pretty a => Vars γ -> Elem γ a -> ShowType -> String
showElem vs (MinMax m es) st = foldrAlt op bnd [showPoly vs p st | p <- es]
  where (op,bnd) = case m of
          Min -> (binOp "⊓" ,"+∞")
          Max -> (binOp "⊔", "-∞")
showElem vs (Vari v) _ = vs v
showElem vs (Exp p) st = (case st of
                              Maxima -> ("exp"<>) . parens
                              Mathematica -> ("Exp"<>) . brackets
                              LaTeX -> braces . ("e^"<>) . braces)
                           (showPoly vs p st)
    
showMono :: Pretty a => a -> Vars γ -> Mono γ a -> ShowType -> String
showMono coef vs (M (Exponential p)) st
  = (if coef == -1 then ("-" ++) else id) $ -- BUG, FIXME
    foldrAlt (binOp (case st of LaTeX -> ""; _ -> "*")) "1" $
    [ pretty coef st | coef /= 1 && coef /= -1 ] ++ 
    [ showExp e (showElem vs m st) | (m, e) <- LC.toList p, e /= zero ]

showPoly :: Pretty x => Vars γ -> Poly γ x -> ShowType -> String
showPoly v (P p) st
  = foldrAlt  (binOp " + ") "0" [ showMono coef v m st | (m, coef) <- LC.toList p, coef /= zero ]

showDumb :: Pretty a => Vars γ -> Dumb (Poly γ a) -> ShowType -> String
showDumb v (x :/ y) st = parens (showPoly v x st) ++ "/" ++  parens (showPoly v y st)

binOp :: [a] -> [a] -> [a] -> [a]
binOp op x y = x ++ op ++ y

showCond :: ShowType -> Vars γ -> Cond γ -> String
showCond st v c0 = case c0 of
  (IsNegative c') -> case st of
                         Mathematica -> "Boole" ++
                                        (brackets $ showExpr v c' st ++ " ≤ 0")
                         Maxima -> "charfun" ++
                                   (parens $ showExpr v c' st ++ " ≤ 0")
                         LaTeX -> "\\mathbb{1}" ++
                                  (parens $ showExpr v c' st ++ " \\leq 0")
  (IsZero c') -> case st of
                     LaTeX -> "\\delta" ++ (braces $ showExpr v c' st)
                     _ -> "DiracDelta" ++ (brackets $ showExpr v c' st)

parens :: String -> String
parens x = "(" ++ x ++ ")"

brackets :: String -> String
brackets x = "[" ++ x ++ "]"

braces :: String -> String
braces x = "{" ++ x ++ "}"

foldrAlt :: (p -> p -> p) -> p -> [p] -> p
foldrAlt _ k [] = k
foldrAlt f _ xs = foldr1 f xs

showBounds :: Vars γ -> Bool -> [Expr γ Rat] -> ShowType -> String
showBounds v lo (nub -> xs) = \case
  Maxima -> if lo
            then foldrAlt
                 (\x y -> "max(" ++ x ++ ", " ++ y ++ ")")
                 "-inf" $
                 map (flip (showExpr v) Maxima) xs
            else foldrAlt
                 (\x y -> "min(" ++ x ++ ", " ++ y ++ ")")
                 "inf" $
                 map (flip (showExpr v) Maxima) xs
  Mathematica -> if lo
                 then foldrAlt
                      (\x y -> "Max[" ++ x ++ ", " ++ y ++ "]")
                      "-Infinity" $
                      map (flip (showExpr v) Mathematica) xs
                 else foldrAlt
                      (\x y -> "Min[" ++ x ++ ", " ++ y ++ "]")
                      "Infinity" $
                      map (flip (showExpr v) Mathematica) xs
  LaTeX -> if lo
           then foldrAlt
                (\x y -> "Max[" ++ x ++ ", " ++ y ++ "]")
                "-\\infty" $
                map (flip (showExpr v) LaTeX) xs
           else foldrAlt
                (\x y -> "Min[" ++ x ++ ", " ++ y ++ "]")
                "\\infty" $
                map (flip (showExpr v) LaTeX) xs

when :: [a] -> [Char] -> [Char]
when [] _ = ""
when _ x = x


(+!) :: String -> Vars γ -> Vars (γ, d)
f +! v = \case Here -> f
               There i -> v i

showP :: [String] -> Vars γ -> P γ Rat -> ShowType -> String
showP [] _ = error "showP: ran out of freshes"
showP freshes@(f:fs) v = \case
  Ret e -> showDumb v e
  Add p1 p2 -> \st -> "(" ++ showP freshes v p1 st ++ ") + (" ++
                      showP freshes v p2 st ++ ")"
  Div p1 p2 -> \st -> case st of
                        LaTeX -> "\\frac{" ++ showP freshes v p1 LaTeX ++
                                 "}{" ++ showP freshes v p2 LaTeX ++ "}"
                        _ -> "(" ++ showP freshes v p1 st ++ ") / (" ++
                             showP freshes v p2 st ++ ")"
  Integrate (Domain cs los his) e ->
    \st -> case st of
             LaTeX -> "\\int_{" ++ showBounds v True los LaTeX ++ "}^{" ++
                      showBounds v False his LaTeX ++ "}" ++
                      showP fs (f +! v) e LaTeX ++
                      "\\,d" ++ f 
             _ -> (\(integrand,dom) ->
                     case st of
                       Maxima -> "integrate" ++
                                 parens (integrand ++ ", " ++ dom)
                       Mathematica -> "Integrate" ++
                                      brackets
                                      (integrand ++ ", " ++ braces dom)) $
                  (showP fs (f +! v) e st,
                  (when cs $ f ++ "∈" ++
                   braces (intercalate "∧" $ map (showCond st (f +! v))
                           cs)) ++ f ++ ", " ++
                  showBounds v True los st ++ ", " ++
                  showBounds v False his st)
  Cond c e -> \st -> showCond st v c ++ " * " ++ showP freshes v e st

showProg :: P () Rat -> ShowType -> String
showProg = showP freshes (\case)


printAs :: ShowType -> P γ Rat -> String
printAs = flip $ showP freshes (\case)

instance Show (P () Rat) where
  show = flip showProg Mathematica


mathematica' :: [String] -> Vars γ -> P γ Rat -> IO ()
mathematica' fs vars = putStrLn . flip (showP fs vars) Mathematica

latex' :: [String] -> Vars γ -> P γ Rat -> IO ()
latex' fs vars = putStrLn . flip (showP fs vars) LaTeX

type Solution γ d = (Ordering, Expr γ d)


solveHere :: (Ord x, Field x) => A.Affine (Available x (γ, x)) x -> (Bool, Expr γ x)
solveHere e0 = (p,e)
  where Right (p,occurExpr -> Just e) = A.solve Here e0
  
-- FIXME: detect always true and always false cases.
solve' :: Cond (γ, Rat) -> Solution γ Rat
solve' c0 = case c0 of
    IsZero _ -> (EQ, e)
    IsNegative _ -> if positive then (LT, e) else (GT, e) 
  where (positive,e) = solveHere (condExpr c0)
  
  
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

deepest :: Cond γ -> SomeVar γ
deepest c = case condExpr c of
   (A.Affine _ e) -> case LC.toList e of
                   xs@(_:_) -> foldr1 minVar . map SomeVar . map fst $ xs
                   [] -> NoVar

travExpr :: Additive t => Applicative f =>
            (forall v. Available v γ -> f (Available v δ)) ->
            Expr γ t -> f (Expr δ t)
travExpr = A.traverseVars

occurExpr :: Additive t => Expr (γ, x) t -> Maybe (Expr γ t)
occurExpr = travExpr $ \case
  Here -> Nothing
  There x -> Just x


integrate :: d ~ Rat => Domain γ d -> P (γ, d) Rat -> P γ Rat
integrate _ (Ret z) | isZero z = Ret $ zero
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
    domainToConditions x0 d $ substP (\case { Here -> x0;
                                              There i -> A.var i }) e
    where (_,x0) = solveHere c'
  Just c'' -> cond (IsZero c'') (integrate d e)
integrate d (Add e e') = Add (integrate d e) (integrate d e')
integrate d e = Integrate d e

adding :: Ring a => Ord a => DecidableZero a => P γ a -> P γ a -> P γ a
adding (Ret z) x | isZero z = x
adding x (Ret z) | isZero z = x
adding x y = Add x y

cond :: Cond γ -> P γ Rat -> P γ Rat
cond _ (Ret z) | isZero z = Ret $ zero
cond (IsNegative (A.Affine k0 vs)) e | k0 <= 0, vs == zero = e
cond c (Cond c' e) | c == c' = cond c e
cond c (Cond c' e) = if (deepest c) `shallower` (deepest c')
                     then Cond c (Cond c' e)
                     else Cond c' (cond c e)
cond c (normalise -> e) = Cond c e

normalise :: P γ Rat -> P γ Rat
normalise = \case
  Cond c (normalise -> e) -> cond c e
  Integrate d (normalise -> e) -> integrate d e
  Add (normalise -> p1) (normalise -> p2) -> adding p1 p2
  Div (normalise -> p1) (normalise -> p2) -> divide p1 p2
  Ret e -> Ret e

approximateIntegrals :: forall γ δ. Int -> (Available Rat γ -> Available C δ) -> P γ Rat -> Ret δ C
approximateIntegrals n v =
  let r :: forall ξ ζ.  (Available Rat ξ -> Available C ζ) -> P ξ Rat -> Ret ζ C
      r = approximateIntegrals n
      r0 :: P γ Rat -> Ret δ C
      r0 = r v
      v' :: Available Rat (γ,Rat) -> Available C (δ,C)
      v' = \case
        Here -> Here
        There x -> There (v x)
  in \case
    Add a b -> r0 a + r0 b
    Div a b -> r0 a / r0 b
    Ret x -> collapseRat' v x
    Cond {} -> error "approximateIntegrals: condition not eliminated ?"
    Integrate (Domain [] los his) e -> chebIntegral @C n lo hi (\x -> substP0 x (r v' e))
      where lo,hi :: Poly δ C
            lo = minMax Max $ map (collapseRat v . exprToPoly) los
            hi = minMax Min $ map (collapseRat v . exprToPoly) his
    Integrate {} -> error "approximateIntegrals: unbounded integral?"


substP0 :: Poly γ C -> Ret (γ,C) C -> Ret γ C
substP0 x = substRet (substElem' $ \case Here -> x; There v -> varPoly v)

divide :: DecidableZero a => Ord a => Ring a => P γ a -> P γ a -> P γ a
divide (Ret z) _ | isZero z = Ret $ zero
divide (Cond c n) d = Cond c (divide n d) -- this exposes conditions to the integrate function.
divide p1 p2 = Div p1 p2

-- | Take typed descriptions of real numbers onto Maxima programs. 
maxima :: (γ ⊢ 'R) -> P (Eval γ) Rat
maxima = normalise . evalP' . normalForm . clean . evalβ

-- | Take typed descriptions of real numbers onto Mathematica programs.
mathematica :: 'Unit ⊢ 'R -> IO ()
mathematica = mathematica' freshes (\case) . maxima

-- | Take typed descriptions of real numbers onto Mathematica programs.
mathematicaFun :: 'Unit ⊢ ('R ⟶ 'R) -> IO ()
mathematicaFun = mathematica' fs (\case Here -> f; There _ -> error "mathematicaFun: are you trying to access the end of context? (Unit)") . maxima . absInversion
  where (f:fs) = freshes

latexFun :: 'Unit ⊢ ('R ⟶ 'R) -> IO ()
latexFun = latex' fs (\case Here -> f; There _ -> error "latexFun: are you trying to access the end of context? (Unit)") . maxima . absInversion
  where (f:fs) = freshes

mathematicaFun' :: 'Unit ⊢ ('R ⟶ ('R ⟶ 'R)) -> IO ()
mathematicaFun' = mathematica' fs (\case
                                      Here -> f
                                      There Here -> f'
                                      There (There _) ->
                                        error "mathematicaFun: are you" ++
                                        "trying to access the end of" ++
                                        "context? (Unit)") .
                  maxima . absInversion . absInversion
  where (f:f':fs) = freshes

-- Domain without restriction
full :: Domain γ x
full = Domain [] [] []

example0 :: P () Rat
example0 = Integrate full $
           retPoly $  constPoly 10 + varPoly Here

-- >>> example0
-- integrate((10 + x), x, -inf, inf)

exampleInEq :: P () Rat
exampleInEq = Integrate full $
              Cond (IsNegative (A.constant 7 - A.var Here)) $
              retPoly $  constPoly 10 + varPoly Here

-- >>> exampleInEq
-- integrate(charfun[7 + (-1 * x) ≤ 0] * 10 + x, x, -inf, inf)

-- >>> normalise exampleInEq
-- integrate(10 + x, x, 7, inf)

exampleEq :: P () Rat
exampleEq = Integrate full $
            Cond (IsZero (A.constant 7 - A.var Here)) $
            retPoly $  constPoly 10 + varPoly Here

-- >>> exampleEq
-- integrate(DiracDelta[7 + (-1 * x)] * 10 + x, x, -inf, inf)

-- >>> normalise exampleEq
-- 17

example :: P () Rat
example = Integrate full $ Integrate full $
          Cond (IsNegative (3 *< A.var Here + 2 *< A.var Here)) $
          Cond (IsNegative (A.constant 2 + A.var Here)) $
          one

-- >>> example
-- integrate(integrate(charfun[(3 * x) + (2 * y) ≤ 0] * charfun[x ≤ 0] * (1), y, -inf, inf), x, -inf, inf)

-- >>> normalise example
-- integrate(integrate((1), y, -inf, (-3/2 * x)), x, -inf, )

example1 :: P () Rat
example1 = Integrate full $ Integrate full $
           Cond (IsZero (A.constant 4 + A.var (There Here) - A.var Here)) $
           one

-- >>> example1
-- integrate(integrate(DiracDelta[4 + x + (-1 * y)] * (1), y, -inf, inf), x, -inf, inf)

-- >>> normalise example1
-- integrate((1), x, -inf, inf)

example2 :: P () Rat
example2 = Integrate full $
           Integrate (Domain [] [A.constant 1 + A.var Here] []) $
           Cond (IsZero (A.constant 4 + A.var (There Here) - A.var Here) ) $
           retPoly $  varPoly Here

-- >>> example2
-- Integrate[Integrate[DiracDelta[4 + (2 * x) + (-y)] * y, {y, 1 + x, Infinity}], {x, -Infinity, Infinity}]

-- >>> normalise example2
-- Integrate[(4 + 2*x)/(1), {x, -3, Infinity}]

example3 :: P () Rat
example3 = Integrate full $
           Integrate full $
           Cond (IsNegative (A.constant 3 - A.var Here)) $
           Cond (IsZero (A.constant 4 + A.var (There Here) - A.var Here)) $
           retPoly $ constPoly 2 + sqr (varPoly Here) + 2 *< varPoly (There Here)

-- >>> example3
-- Integrate[Integrate[Boole[3 + (-y) ≤ 0] * DiracDelta[4 + x + (-y)] * 2 + y^2 + 2*x, {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> normalise example3
-- Integrate[18 + 10*x + x^2, {x, -1, Infinity}]

example4a :: P () Rat
example4a = Integrate (Domain [] [zero] [A.constant 1]) $ one

-- >>> normalise example4a
-- Integrate[(1)/(1), {x, 0, 1}]

-- >>> approximateIntegrals 4 noVarToC $ normalise example4a
-- (1)/(1)


example4 :: P () Rat
example4 = Integrate full $
           Integrate full $
           Cond (IsNegative (A.constant (-3) - A.var Here)) $
           Cond (IsNegative (A.constant (-3) + A.var Here)) $
           Cond (IsZero (A.var  (There Here) - A.var Here)) $
           retPoly $ exponential $ negate $ varPoly Here ^+2 + (varPoly (There Here) ^+2)

-- >>> example4
-- Integrate[Integrate[Boole[-3 + (-y) ≤ 0] * Boole[-3 + y ≤ 0] * DiracDelta[(-y) + x] * (Exp[-y^2 + -x^2])/(1), {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> normalise example4
-- Integrate[(Exp[-2*x^2])/(1), {x, -3, 3}]

-- >>> approximateIntegrals 16 noVarToC $ normalise example4
-- (1.253346416637889)/(1)

example5 :: P ((),Rat) Rat
example5 = Integrate full $
           Cond (IsNegative (A.constant (-3) - A.var Here)) $
           Cond (IsNegative (A.constant (-3) + A.var Here)) $
           retPoly $ exponential $ negate $ varPoly Here ^+2 + (varPoly (There Here) ^+2)

-- >>> putStrLn $ showProg1 example5 Maxima
-- integrate(charfun(-3 + (-x) ≤ 0) * charfun(-3 + x ≤ 0) * (exp(-x^2 + -α^2))/(1), x, -inf, inf)

-- >>> putStrLn $ showProg1 (normalise example5) Maxima
-- integrate((exp(-x^2 + -α^2))/(1), x, -3, 3)


-- >>> putStrLn $ showDumb oneVar (approximateIntegrals 8 oneVarToC $ normalise example5) Mathematica
-- (9.523809523809527e-2*Exp[-9.0 + -α^2] + 0.8773118952961091*Exp[-7.681980515339462 + -α^2] + 0.8380952380952381*Exp[-4.499999999999999 + -α^2] + 0.8380952380952381*Exp[-4.499999999999997 + -α^2] + 1.0851535761614692*Exp[-1.318019484660537 + -α^2] + 1.0851535761614692*Exp[-1.3180194846605355 + -α^2] + 1.180952380952381*Exp[-4.930380657631324e-32 + -α^2])/(1)


----------------
-- Show helpers


noVarToC :: Available Rat () -> Available C ()
noVarToC = \case

oneVarToC :: Available Rat ((),Rat) -> Available C ((),C)
oneVarToC = \case
     Here -> Here
     There x -> There (noVarToC x)

showProg1 :: P ((),α) Rat -> ShowType -> String
showProg1 = showP freshes oneVar

oneVar :: Vars ((),α)
oneVar = (\case Here -> "α"; _ -> error "oneVar: access empty context")

  
