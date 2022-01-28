{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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
import Models.Field (BinOp(..), Fld(..))
import qualified Models.Field
import Algebra.Linear.Chebyshev (chebIntegral)
import Data.Complex

-------------------------------------------------------
-- Types

type C = Complex Double
deriving instance Ord C -- yikes
instance (Field a, Ord a, Show a) => Pretty (Complex a) where
  pretty (a :+ b) _ | b < 10e-15 = show a
                    | otherwise = show a ++ "+" ++ show b ++ "i"
  
type Rat = Fld

data Dir = Min | Max deriving (Eq,Ord)
type Expr γ α = A.Affine (Available α γ) α
data Elem γ α = Vari (Available α γ) | Exp (Poly γ α) | Supremum Dir [Poly γ α] deriving (Eq,Ord)
type Poly γ a = Polynomial (Elem γ a) a
type Mono γ a = Monomial (Elem γ a)
type DD γ a = Dumb (Poly γ a)
type Ret γ a = DD γ a 

data Cond γ a = IsNegative { condExpr :: Expr γ a }
              -- Meaning of this constructor: expression ≤ 0
              -- Example: u ≤ v is represented by @IsNegative (u - v)@
              | IsZero { condExpr :: Expr γ a }
              -- Meaning of this constructor: expression = 0
              -- Example: u = v is represented by @IsZero (u - v)@
   deriving (Eq)

data Domain γ α = Domain { domainConditions :: [Cond (γ, α) α]
                         , domainLoBounds, domainHiBounds :: [Expr γ α] }

data P γ α where
  Integrate :: d ~ Rat => Domain γ d -> P (γ, d) α -> P γ α
  Cond :: (DecidableZero a, Ord a, Ring a) => Cond γ a -> P γ a -> P γ a
  Add :: P γ α -> P γ α -> P γ α
  Div :: P γ α -> P γ α -> P γ α -- Can this be replaced by "factor" ? No, because we do integration in these factors as well.
  Ret :: Ret γ α -> P γ α


data Dumb a = a :/ a
infixl 7 :/

-------------------------------------------
-- Evaluator and normaliser
  
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

evalPoly :: forall α β γ δ ζ. DecidableZero β => Transcendental β => Ord β => Ring β => Transcendental α => (Ord α, Ring α, Eq α)
         => (Available α γ -> Available β δ)
         -> (α -> β)
         -> (forall x. (Ring x, Ord x, DecidableZero x) => Available x δ -> Poly ζ x)
         -> Poly γ α -> Poly ζ β
evalPoly v fc f = eval fc (evalElem v fc f) 

evalElem :: forall α β γ δ ζ. DecidableZero β => Transcendental β => Ord β => Ring β => Transcendental α => (Ord α, Ring α, Eq α)
         => (Available α γ -> Available β δ)
         -> (α -> β)
         -> (forall x. (Ring x, Ord x, DecidableZero x) => Available x δ -> Poly ζ x)
         -> Elem γ α -> Poly ζ β
evalElem v fc f =
  let evP :: Poly γ α -> Poly ζ β
      evP = evalPoly v fc f
  in \case
        Supremum dir es -> supremum dir (evP <$> es)
        (Vari x) -> f (v x)
        (Exp p) -> exponential (evP p)

exponential :: DecidableZero α => Transcendental α => Ord α => Ring α => Poly γ α -> Poly γ α
exponential p = case isConstant p of
  Just c -> constPoly (exp c)
  Nothing -> varP (Exp p)
  
supremum :: DecidableZero α => (Additive α, Ord α, Multiplicative α) =>
            Dir -> [Polynomial (Elem γ α) α] -> Polynomial (Elem γ α) α
supremum dir es = case traverse isConstant es of
                  Just cs -> constPoly ((case dir of Max -> maximum; Min -> minimum) cs)
                  Nothing -> varP (Supremum dir es)

isPositive :: Expr γ Rat -> Cond γ Rat
isPositive e = isNegative (negate e)

isNegative :: Expr γ a -> Cond γ a
isNegative e = IsNegative e

lessThan :: DecidableZero a => Group a => Expr γ a -> Expr γ a -> Cond γ a
t `lessThan` u = isNegative (t - u)

greaterThan :: Expr γ Rat -> Expr γ Rat -> Cond γ Rat
t `greaterThan` u = u `lessThan` t

data Available α γ where
  Here :: Available α (γ, α)
  There :: Available α γ -> Available α (γ, β)
deriving instance Eq (Available α γ)
deriving instance Ord (Available α γ)
deriving instance Show (Available α γ)

instance (Ord α, Transcendental α, DecidableZero α) => Multiplicative (P γ α) where
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

instance (Ord a, Ring a, DecidableZero a) => AbelianAdditive (P γ a)
instance (Transcendental a, Ord a, DecidableZero a) => Group (P γ a) where
  negate = (* (Ret (negate one)))
instance (Transcendental a, Ord a, DecidableZero a) => Scalable (Poly γ a) (P γ a) where
  p *^ q = retPoly p * q
instance (Ord a, Ring a, DecidableZero a) => Additive (P γ a) where
  zero = Ret zero
  (Ret z) + x | isZero z = x
  x + (Ret z) | isZero z = x
  x + y = Add x y

instance (Ord a, Transcendental a, DecidableZero a) => Division (P γ a) where
  (Ret z) / _ | isZero z = Ret $ zero
  (Cond c n) / d = Cond c (n / d) -- this exposes conditions to the integrate function.
  p1 / p2 = Div p1 p2

type Subst γ δ = forall α. Ring α => Available α γ -> Expr δ α

wkSubst :: Ring α => Subst γ δ -> Subst (γ, α) (δ, α)
wkSubst f = \case
  Here -> A.var Here 
  There x -> A.mapVars There (f x)

substExpr :: Subst γ δ -> forall α. DecidableZero α => Ring α => Expr γ α -> Expr δ α
substExpr = A.subst

exprToPoly :: forall γ α. DecidableZero α => Ord α => (Eq α, Ring α)
           => Expr γ α -> Poly γ α
exprToPoly = A.eval constPoly (monoPoly . varMono) 

varMono :: Available α γ -> Mono γ α
varMono = varM . Vari

varPoly :: Ring α => Available α γ -> Poly γ α
varPoly = varP . Vari

substElem :: DecidableZero α => Transcendental α => (Ord α, Ring α, Eq α)
          => Subst γ δ -> Elem γ α -> Poly δ α
substElem f = substElem' (exprToPoly . f)

substElem' :: DecidableZero α => Transcendental α => (Ord α, Ring α, Eq α)
           => (forall x. (Ring x, Ord x, DecidableZero x) => Available x γ -> Poly δ x)
           -> Elem γ α -> Poly δ α
substElem' f = evalElem id id f

substRet :: DecidableZero c => (Ord f, Ord e, Ord c, Ring c)
         => Substitution e f c -> Dumb (Polynomial e c) -> Dumb (Polynomial f c)
substRet f (x :/ y) = subst f x :/ subst f y
              
substCond :: DecidableZero α => Ring α => Subst γ δ -> Cond γ α -> Cond δ α
substCond f (IsNegative e) = IsNegative $ substExpr f e
substCond f (IsZero e) = IsZero $ substExpr f e

substDomain :: DecidableZero α => Ring α => Subst γ δ -> Domain γ α -> Domain δ α
substDomain f (Domain c lo hi) = Domain
                                 (substCond (wkSubst f) <$> c)
                                 (substExpr f <$> lo)
                                 (substExpr f <$> hi)

-- | Normalising substitution
substP :: DecidableZero x => Ord x => Eq x => Transcendental x => Subst γ δ -> P γ x -> P δ x
substP f p0 = case p0 of
  Ret e -> Ret (substRet (substElem f) e)
  Add (substP f -> p1) (substP f -> p2) -> p1 + p2
  Div (substP f -> p1) (substP f -> p2) -> p1 / p2
  Cond c p -> cond (substCond f c) (substP f p)
  Integrate d p -> Integrate (substDomain f d) (substP (wkSubst f) p) -- integrations are never simplified by substitution

wkP :: DecidableZero x => Transcendental x => Ord x => P γ x -> P (γ, α) x
wkP = substP $ \i -> A.var (There i) 

-- | Restrict the bounds by moving the bounds. Also return conditions that
-- ensure that the bounds are in the right order.
restrictDomain :: α ~ Rat => Cond (γ, α) α -> Domain γ α -> (Domain γ α, [Cond γ α])
restrictDomain c (Domain cs los his) = case solve' c of -- version with solver
  (LT, e) -> (Domain cs los (e:his), [ lo `lessThan` e | lo <- los ])
  (GT, e) -> (Domain cs (e:los) his, [ e `lessThan` hi | hi <- his ])
  _ -> error "restrictDomain: cannot be called/(1) on equality condition"

solveHere :: DecidableZero x => (Ord x, Field x) => A.Affine (Available x (γ, x)) x -> (Bool, Expr γ x)
solveHere e0 = case A.solve Here e0 of
  Left _ -> error "solveHere: division by zero"
  Right (p,e1) -> case occurExpr e1 of
    Nothing -> error "solveHere: panic: eliminated variable present in rest of expression"
    Just e -> (p,e)

type Solution γ d = (Ordering, Expr γ d)
  
-- FIXME: detect always true and always false cases.
solve' :: Cond (γ, Rat) Rat -> Solution γ Rat
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

deepest :: Cond γ α -> SomeVar γ
deepest c = case condExpr c of
   (A.Affine _ e) -> case LC.toList e of
     xs@(_:_) -> foldr1 minVar . map SomeVar . map fst $ xs
     [] -> NoVar

occurExpr :: Additive t => Expr (γ, x) t -> Maybe (Expr γ t)
occurExpr = A.traverseVars $ \case
  Here -> Nothing
  There x -> Just x

type RatLike α = (Ring α, Ord α, DecidableZero α)

domainToConds :: RatLike α => Domain γ α -> [Cond (γ,α) α]
domainToConds = \case
  Domain [] [] [] -> []
  Domain (c:cs) los his -> c : domainToConds (Domain cs los his)
  Domain cs (e:los) his -> (wkExpr e `lessThan` A.var Here) : domainToConds (Domain cs los his)
  Domain cs los (e:his) -> (A.var Here `lessThan` wkExpr e) : domainToConds (Domain cs los his)

wkExpr :: RatLike α => Expr γ α -> Expr (γ, β) α
wkExpr = substExpr (A.var . There) 

conds_ :: RatLike a => [Cond γ a] -> P γ a -> P γ a
conds_ cs e = foldr Cond e cs

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
    substP (\case { Here -> x0; There i -> A.var i }) $ conds_ (domainToConds d) e
    where (_,x0) = solveHere c'
  Just c'' -> cond (IsZero c'') (integrate d e)
integrate d (Add e e') = Add (integrate d e) (integrate d e')
integrate d e = Integrate d e

cond :: (DecidableZero a, Ord a, Ring a) => Cond γ a -> P γ a -> P γ a
cond _ (Ret z) | isZero z = Ret $ zero
cond (IsNegative (A.Affine k0 vs)) e | k0 <= 0, vs == zero = e
cond c (Cond c' e) | c == c' = cond c e
cond c (Cond c' e) = if (deepest c) `shallower` (deepest c')
                     then Cond c (Cond c' e)
                     else Cond c' (cond c e)
cond c e = Cond c e


normalise :: P γ Rat -> P γ Rat
normalise = \case
  Cond c (normalise -> e) -> cond c e
  Integrate d (normalise -> e) -> integrate d e
  Add (normalise -> p1) (normalise -> p2) -> p1 + p2
  Div (normalise -> p1) (normalise -> p2) -> p1 / p2
  Ret e -> Ret e

-- | Remove redundant conditions
cleanConds :: (a ~ Rat) => [Cond γ a] -> P γ a -> P γ a
cleanConds cs = \case
  Ret x -> Ret x
  Integrate d e -> Integrate d (cleanConds (domainToConds d ++ (map (substCond (A.var . There)) cs)) e)
  Cond c e -> if any (== c) cs -- NOTE: this can be made stronger to "can prove c from the intersection of cs"
              then cleanConds cs e
              else Cond c $ cleanConds (c:cs) e
  Div x y -> Div (cleanConds cs x) (cleanConds cs y)
  Add x y -> Add (cleanConds cs x) (cleanConds cs y)
  

------------------------------------------------------------------------------
-- Conversion from lambda terms

type family Eval γ where
  Eval 'R = Rat
  Eval 'Unit = ()
  Eval (γ × α) = (Eval γ, Eval α)

pattern NNVar :: Available (Eval α) (Eval γ) -> NF γ α
pattern NNVar i <- Neu (NeuVar (evalVar -> i))
pattern Equ :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Equ x y = Neu (NeuApp (NeuApp (NeuCon (General EqRl)) x) y)
pattern EqVars :: Available Rat (Eval γ) -> Available Rat (Eval γ)  -> NF γ 'R
pattern EqVars i j <- Neu (NeuApp (NeuApp (NeuCon (General EqRl))
                                  (NNVar i)) (NNVar j))
pattern Mults :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Mults x y = Neu (NeuApp (NeuApp (NeuCon (General Mult)) x) y)
pattern Adds :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Adds x y = Neu (NeuApp (NeuApp (NeuCon (General Addi)) x) y)
pattern InEqVars :: Available Rat (Eval γ) -> Available Rat (Eval γ) -> NF γ 'R
pattern InEqVars i j <- Neu (NeuApp (NeuCon (General Indi))
                            (Neu (NeuApp (NeuApp (NeuCon (Special GTE))
                                           (NNVar i)) (NNVar j))))
pattern InEq :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern InEq x y = Neu (NeuApp (NeuCon (General Indi))
                            (Neu (NeuApp (NeuApp (NeuCon (Special GTE))
                                          x) y)))
pattern Normal :: Field x=> x -> x -> NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Normal x y f <- Neu (NeuApp (NeuApp (NeuCon (General Nml))
                                    (NFPair (NNCon x) (NNCon y))) f)
pattern Cauchy :: Field x => x -> x ->NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Cauchy x y f <- Neu (NeuApp (NeuApp (NeuCon (General Cau))
                                    (NFPair (NNCon x) (NNCon y))) f)
pattern Quartic :: Field x => x -> x ->NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Quartic x y f <- Neu (NeuApp (NeuApp (NeuCon (General Qua))
                                    (NFPair (NNCon x) (NNCon y))) f)
pattern Uniform :: Field x => x -> x ->NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Uniform x y f <- Neu (NeuApp (NeuApp (NeuCon (General Uni))
                                     (NFPair (NNCon x) (NNCon y))) f)
pattern Lesbegue :: NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Lesbegue f = Neu (NeuApp (NeuCon (General Les)) f)
pattern Divide :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Divide x y = Neu (NeuApp (NeuApp (NeuCon (General Divi)) x) y)
pattern NNCon :: Field x => x -> NF γ 'R
pattern NNCon x <- Neu (NeuCon (General (Incl (fromRational -> x))))

evalP :: NF 'Unit 'R -> P () Rat
evalP = evalP'

retPoly :: DecidableZero a => Ord a => Ring a => Poly γ a -> P γ a
retPoly = Ret . (:/ one)

-- Domain without restriction
full :: Domain γ x
full = Domain [] [] []

evalP' :: NF γ 'R -> P (Eval γ) Rat
evalP' = \case
  NNCon x -> retPoly $ constPoly (fromRational x)
  Neu (NeuApp (NeuCon (General Indi)) (Neu (NeuCon (Logical Tru)))) -> one
  Neu (NeuApp (NeuApp (NeuCon (General EqRl))
               (Adds (NNVar i) (NNVar j))) (NNVar k)) ->
    Cond (IsZero $ A.var i + A.var j - A.var k) $ one
  EqVars i j -> Cond (IsZero $ A.var i - A.var j) $ one
  InEqVars i j -> Cond (IsNegative $ A.var j - A.var i) $ one
  Equ (NNVar i) (NNCon x) -> Cond (IsZero $ A.constant x - A.var i) $ one
  InEq (NNVar i) (NNCon x) -> Cond (IsNegative $ A.constant x - A.var i) $ one
  InEq (NNCon x) (NNVar i) -> Cond (IsNegative $ A.var i - A.constant x) $ one
  Adds (evalP' -> x) (evalP' -> y) -> Add x y
  Mults (evalP' -> x) (evalP' -> y) -> x * y
  Normal μ σ f -> Integrate full $ 
      (retPoly $ constPoly (1 / (σ * sqrt (2 * pi))) * exponential (constPoly (-1/2) * ((1/σ) *^ (constPoly μ - varPoly Here))^+2))
    * (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Cauchy x0 γ f -> Integrate full $ Div (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))  
    (retPoly $ (constPoly (pi * γ) * (one + ((one/γ) *^ (varPoly Here - constPoly x0)) ^+2)))
  Quartic μ σ f -> Integrate (Domain [] [A.constant (μ - a)] [A.constant (μ + a)]) $
    (retPoly $ (constPoly ((15 / 16) / (a ^+ 5))) * ((varPoly Here - constPoly μ) - constPoly a) ^+ 2 * ((varPoly Here - constPoly μ) + constPoly a) ^+ 2) *
    (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
    where a = sqrt 7 * σ
  Uniform x y f -> Integrate (Domain [] [A.constant x] [A.constant y]) $ 
    (retPoly $ constPoly (1 / (y - x))) *
    (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Lesbegue f -> Integrate (Domain [] [] []) $
                (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  NNVar i -> retPoly $ varPoly i
  Divide x y -> Div (evalP' x) (evalP' y)
  t -> error ("evalP': don't know how to handle: " ++ (show . nf_to_λ) t)

evalVar :: α ∈ γ -> Available (Eval α) (Eval γ)
evalVar = \case
  Get -> Here
  Weaken (evalVar -> i) -> There i

-----------------------------------------------------------
-- Show functions

-------------------------------------------------
-- Approximation of integrals

class IntegrableContext γ where
  type Tgt γ 
  vRatToC :: Available Rat γ -> Available C (Tgt γ)

instance IntegrableContext () where
  type Tgt () = ()
  vRatToC = \case

instance IntegrableContext γ => IntegrableContext (γ,Rat) where
  type Tgt (γ,Rat) = (Tgt γ,C)
  vRatToC = \case
     Here -> Here
     There x -> There (vRatToC x)


ratToC :: (Available Rat γ -> Available C δ) -> Poly γ Rat -> Poly δ C
ratToC v = evalPoly v (Models.Field.eval @C) varPoly

ratToC' :: (Available Rat γ -> Available C δ) -> Ret γ Rat -> Ret δ C
ratToC' v (x :/ y) = ratToC v x :/ ratToC v y


approximateIntegralsAny :: forall γ. IntegrableContext γ => Int -> P γ Rat -> P (Tgt γ) C
approximateIntegralsAny n = approximateIntegralsConds n vRatToC

substCond' :: (Available Rat γ -> Available C δ) -> Cond γ Rat -> Cond δ C
substCond' f (IsNegative e) = IsNegative (A.mapVars f $ fmap (Models.Field.eval @C) e)
substCond' f (IsZero e) = IsZero (A.mapVars f $ fmap (Models.Field.eval @C) e)

approximateIntegralsConds :: forall γ δ. Int -> (Available Rat γ -> Available C δ) -> P γ Rat -> P δ C
approximateIntegralsConds n v (Cond c e) = Cond (substCond' v c) (approximateIntegralsConds n v e)
approximateIntegralsConds n v (Div x y) = Div (approximateIntegralsConds n v x) (approximateIntegralsConds n v y)  
approximateIntegralsConds n v e = Ret $ approximateIntegrals n v e

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
    Ret x -> ratToC' v x
    Cond _ _ -> error ("approximateIntegrals: condition not eliminated")
    Integrate (Domain [] los his) e -> chebIntegral @C n lo hi (\x -> substP0 x (r v' e))
      where lo,hi :: Poly δ C
            lo = supremum Max $ map (ratToC v . exprToPoly) los
            hi = supremum Min $ map (ratToC v . exprToPoly) his
    Integrate {} -> error "approximateIntegrals: unbounded integral?"

substP0 :: Poly γ C -> Ret (γ,C) C -> Ret γ C
substP0 x = substRet (substElem' $ \case Here -> x; There v -> varPoly v)

---------------------------------------------
-- Showing stuff
----------------------------------------------

class ShowableContext γ where
  -- This stupidifying interface is dictated by lack of "impredicative polymorphism"
  varsForCtx :: [String] -> Vars γ
  restOfVars :: [String] -> [String]

instance ShowableContext () where
  varsForCtx _ = \case
  restOfVars = id

instance ShowableContext γ => ShowableContext (γ,α) where
  varsForCtx [] = error "varsForCtx: panic: no more fresh variables"
  varsForCtx (f:fs) = \case
    Here -> f
    There x -> varsForCtx fs x
  restOfVars = drop 1 . restOfVars @γ

showProg :: forall γ a. Pretty a => ShowableContext γ => ShowType -> P γ a -> String
showProg = flip (showP (restOfVars @γ freshes) (varsForCtx freshes))

instance (Pretty a, ShowableContext γ) => Show (P γ a) where
  show = showProg Mathematica

class (Eq a, Field a) => Pretty a where
  pretty :: a -> ShowType -> String

instance Pretty Rat where
  pretty = showRat

showCon :: (Show a, Eq a, Ring a) => Ratio a -> ShowType -> [Char]
showCon x  
  | numerator x == 0 = const "0"
  | denominator x == 1 = const $ show $ numerator x
  | otherwise = \case
      LaTeX -> "\\frac{" ++ num ++ "}{" ++ den ++ "}"
      _ -> parens $ num ++ "/" ++ den
  where num = show $ numerator x
        den = show $ denominator x

showRat :: Rat -> ShowType -> String
showRat (Con x) = showCon x
showRat Pi = \case
  LaTeX -> "\\pi"
  Maxima -> "%pi"
  Mathematica -> "Pi"
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
                                             _ -> parens) else id) (showCon n st)

data ShowType = Maxima | Mathematica | LaTeX

type Vars γ  = forall v. Available v γ -> String

(+!) :: String -> Vars γ -> Vars (γ, d)
f +! v = \case Here -> f
               There i -> v i

showExpr :: DecidableZero a => Ord a => Pretty a => Vars γ -> Expr γ a -> ShowType -> String
showExpr v = showPoly v . exprToPoly
  
showExp :: Int -> String -> String
showExp e
  | e == 1 = id
  | otherwise = (++ "^" ++ show e)
                
showElem :: Pretty a => Vars γ -> Elem γ a -> ShowType -> String
showElem vs (Supremum m es) st = showSupremum m [showPoly vs p st | p <- es] st
showElem vs (Vari v) _ = vs v
showElem vs (Exp p) st = (case st of
                              Maxima -> ("exp"<>) . parens
                              Mathematica -> ("Exp"<>) . brackets
                              LaTeX -> braces . ("e^"<>) . braces)
                           (showPoly vs p st)
    
showMono :: Pretty a => a -> Vars γ -> Mono γ a -> ShowType -> String
showMono coef vs (M (Exponential p)) st
  = (if coef == -1 then ("-" ++) else id) $
    foldrAlt (binOp (case st of LaTeX -> ""; _ -> "*")) "1" $
    [ pretty coef st | coef /= 1 && coef /= -1 ] ++ 
    [ showExp e (showElem vs m st) | (m, e) <- LC.toList p, e /= zero ]

showPoly :: Pretty x => Vars γ -> Poly γ x -> ShowType -> String
showPoly v (P p) st
  = foldrAlt plus "0" [ showMono coef v m st | (m, coef) <- LC.toList p, coef /= zero ]
  where plus x y = case y of
          ('-':y') -> x <> " - " <> y'
          _ -> x <> " + " <> y

showDumb :: Pretty a => Vars γ -> Dumb (Poly γ a) -> ShowType -> String
showDumb v (x :/ y) st = parens (showPoly v x st) ++ "/" ++  parens (showPoly v y st)

instance (Pretty a, ShowableContext γ) => Show (Dumb (Poly γ a)) where
  show x = showDumb (varsForCtx freshes) x Mathematica

binOp :: [a] -> [a] -> [a] -> [a]
binOp op x y = x ++ op ++ y

showCond :: DecidableZero α => Pretty α => Ord α => ShowType -> Vars γ -> Cond γ α -> String
showCond st v c0 = case c0 of
  (IsNegative c') -> case st of
      Mathematica -> "Boole" ++ (brackets $ showExpr v c' st ++ " ≤ 0")
      Maxima -> "charfun" ++ (parens $ showExpr v c' st ++ " <= 0")
      LaTeX -> "\\mathbb{1}" ++ (parens $ showExpr v c' st ++ " \\leq 0")
  (IsZero c') -> case st of
      LaTeX -> "\\delta" ++ (parens $ showExpr v c' st)
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

showSupremum :: Dir -> [String] -> ShowType -> String
showSupremum dir xs st = foldrAlt op (sign <> extremum) xs
  where
    sign = case dir of Max -> "-"; Min -> ""
    (extremum,op) = case st of
      Mathematica -> ("Infinity",) $ case dir of
        Min -> (\x y -> "Min[" ++ x ++ ", " ++ y ++ "]")
        Max -> (\x y -> "Max[" ++ x ++ ", " ++ y ++ "]")
      Maxima -> ("inf",) $ case dir of
        Min -> (\x y -> "min(" ++ x ++ ", " ++ y ++ ")")
        Max -> (\x y -> "max(" ++ x ++ ", " ++ y ++ ")")
      LaTeX -> ("\\infty",) $ case dir of
        Min -> binOp "⊓"
        Max -> binOp "⊔"
      
showBounds :: Vars γ -> Dir -> [Expr γ Rat] -> ShowType -> String
showBounds v lo (nub -> xs) st
  = showSupremum lo (map (flip (showExpr v) st) xs) st

when :: [a] -> [Char] -> [Char]
when [] _ = ""
when _ x = x

showP :: Pretty a => [String] -> Vars γ -> P γ a -> ShowType -> String
showP [] _ = error "showP: ran out of freshes"
showP fs@(f:fsRest) v = \case
  Ret e -> showDumb v e
  Add p1 p2 -> \st -> "(" ++ showP fs v p1 st ++ ") + (" ++
                      showP fs v p2 st ++ ")"
  Div p1 p2 -> \st -> case st of
                        LaTeX -> "\\frac{" ++ showP fs v p1 LaTeX ++
                                 "}{" ++ showP fs v p2 LaTeX ++ "}"
                        _ -> "(" ++ showP fs v p1 st ++ ") / (" ++
                             showP fs v p2 st ++ ")"
  Integrate (Domain cs los his) e -> \st -> 
    let body = showP fsRest (f +! v) e st
        dom = (when cs $ f ++ "∈" ++
               braces (intercalate "∧" $ map (showCond st (f +! v))
                       cs)) ++ f ++ ", " ++
              showBounds v Max los st ++ ", " ++
              showBounds v Min his st
    in case st of
         LaTeX -> "\\int_{" ++ showBounds v Max los LaTeX ++ "}^{" ++
                  showBounds v Min his LaTeX ++ "}" ++
                  showP fsRest (f +! v) e LaTeX ++
                  "\\,d" ++ f 
         Maxima -> "integrate" ++ parens (body ++ ", " ++ dom)
         Mathematica -> "Integrate" ++
                        brackets (body ++ ", " ++ braces dom)
  Cond c e -> \st -> showCond st v c ++ " * " ++ showP fs v e st

mathematica :: ShowableContext γ => P γ Rat -> IO ()
mathematica = putStrLn . showProg Mathematica  

latex :: Pretty a => ShowableContext γ => P γ a -> IO ()
latex = putStrLn . showProg LaTeX

maxima :: Pretty a => ShowableContext γ => P γ a -> IO ()
maxima = putStrLn . showProg Maxima

-----------------------------------------------------------
-- Top-level Entry points

-- | Take typed descriptions of real numbers onto integrators 
simplify :: (γ ⊢ 'R) -> P (Eval γ) Rat
simplify = cleanConds [] . normalise . evalP' . normalForm . clean . evalβ

-- | Take typed descriptions of functions onto integrators with a free var
simplifyFun :: 'Unit ⊢ ('R ⟶ 'R) -> P ((), Rat) Rat
simplifyFun = simplify . absInversion

-- | Take typed descriptions of functions onto integrators with two free vars
simplifyFun2 :: 'Unit ⊢ ('R ⟶ ('R ⟶ 'R)) -> (P (((), Rat), Rat) Rat)
simplifyFun2 = simplify . absInversion . absInversion


------------------------------------------------------------
-- Examples

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
          Cond (IsNegative (3 *< A.var (There Here) + 2 *< A.var (Here))) $
          Cond (IsNegative (A.var (There Here))) $
          one

-- >>> example
-- Integrate[Integrate[Boole[2*y + 3*x ≤ 0] * Boole[x ≤ 0] * (1)/(1), {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> normalise example
-- Integrate[Integrate[(1)/(1), {y, -Infinity, (-3/2)*x}], {x, -Infinity, 0}]

example1 :: P () Rat
example1 = Integrate full $ Integrate full $
           Cond (IsZero (A.constant 4 + A.var (There Here) - A.var Here)) $
           one

-- >>> example1
-- Integrate[Integrate[DiracDelta[4 - y + x] * (1)/(1), {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> normalise example1
-- integrate((1), x, -inf, inf)

example2 :: P () Rat
example2 = Integrate full $
           Integrate (Domain [] [A.constant 1 + A.var Here] []) $
           Cond (IsZero (A.constant 4 + 2 *< A.var (There Here) - A.var Here) ) $
           retPoly $  varPoly Here

-- >>> example2
-- Integrate[Integrate[DiracDelta[4 - y + 2*x] * (y)/(1), {y, 1 + x, Infinity}], {x, -Infinity, Infinity}]

-- >>> normalise example2
-- Integrate[(4 + 2*x)/(1), {x, -3, Infinity}]

example3 :: P () Rat
example3 = Integrate full $
           Integrate full $
           Cond (IsNegative (A.constant 3 - A.var Here)) $
           Cond (IsZero (A.constant 4 + A.var (There Here) - A.var Here)) $
           retPoly $ constPoly 2 + (varPoly Here) ^+ 2 + 2 *< varPoly (There Here)

-- >>> example3
-- Integrate[Integrate[Boole[3 - y ≤ 0] * DiracDelta[4 - y + x] * (2 + y^2 + 2*x)/(1), {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> normalise example3
-- Integrate[(18 + 10*x + x^2)/(1), {x, -1, Infinity}]

example4a :: P () Rat
example4a = Integrate (Domain [] [zero] [A.constant 1]) $ one

-- >>> normalise example4a
-- Integrate[(1)/(1), {x, 0, 1}]

-- >>> approximateIntegralsAny 4 (normalise example4a)
-- (1)/(1)


example4 :: P () Rat
example4 = Integrate full $
           Integrate full $
           Cond (IsNegative (A.constant (-3) - A.var Here)) $
           Cond (IsNegative (A.constant (-3) + A.var Here)) $
           Cond (IsZero (A.var  (There Here) - A.var Here)) $
           retPoly $ exponential $ negate $ varPoly Here ^+2 + (varPoly (There Here) ^+2)

-- >>> example4
-- Integrate[Integrate[Boole[-3 - y ≤ 0] * Boole[-3 + y ≤ 0] * DiracDelta[-y + x] * (Exp[-y^2 - x^2])/(1), {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> normalise example4
-- Integrate[(Exp[-2*x^2])/(1), {x, -3, 3}]

-- >>> approximateIntegralsAny 16 $ normalise example4
-- (1.253346416637889)/(1)

example5 :: P ((),Rat) Rat
example5 = Integrate full $
           Cond (IsNegative (A.constant (-3) - A.var Here)) $
           Cond (IsNegative (A.constant (-3) + A.var Here)) $
           retPoly $ exponential $ negate $ varPoly Here ^+2 + (varPoly (There Here) ^+2)

-- >>> example5
-- Integrate[Boole[-3 - y ≤ 0] * Boole[-3 + y ≤ 0] * (Exp[-y^2 - x^2])/(1), {y, -Infinity, Infinity}]

-- >>> normalise example5
-- Integrate[(Exp[-y^2 - x^2])/(1), {y, -3, 3}]

-- >>> (approximateIntegralsAny 8 $ normalise example5) 
-- (9.523809523809527e-2*Exp[-9.0 - x^2] + 0.8773118952961091*Exp[-7.681980515339462 - x^2] + 0.8380952380952381*Exp[-4.499999999999999 - x^2] + 0.8380952380952381*Exp[-4.499999999999997 - x^2] + 1.0851535761614692*Exp[-1.318019484660537 - x^2] + 1.0851535761614692*Exp[-1.3180194846605355 - x^2] + 1.180952380952381*Exp[-4.930380657631324e-32 - x^2])/(1)


