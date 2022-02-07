{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module Models.Integrals.Approximate2  where

import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp)
import qualified Models.Field
import qualified Algebra.Linear.Chebyshev as Chebyshev
import Data.Complex
import qualified Algebra.Morphism.Polynomial.Multi as Multi
import Algebra.Morphism.Polynomial.Multi hiding (constPoly)
import qualified Algebra.Morphism.LinComb as LC
import Control.Applicative

import Models.Integrals.Types

type family Env γ where
  Env 'Unit = ()
  Env (a ':× b) = (Env a, Env b)
  Env 'R = Double

type RR = Double

newtype PointWise x a = PW (x -> a) deriving Functor
instance Applicative (PointWise x) where
  pure x = PW $  \_ -> x
  PW f <*> PW a = PW (\x -> (f x) (a x))

fromPointWise :: PointWise x a -> x -> a
fromPointWise (PW x) = x

instance Additive a => Additive (PointWise x a) where
  zero = pure zero
  (+) = liftA2 (+)

instance Group a => Group (PointWise x a) where
  negate = fmap negate
  (-) = liftA2 (-)

instance AbelianAdditive a => AbelianAdditive (PointWise x a)

instance Multiplicative a => Multiplicative (PointWise x a) where
  one  = pure one
  (*) = liftA2 (*)

instance Division a => Division (PointWise x a) where
  recip  = fmap recip
  (/) = liftA2 (/)


instance Roots a => Roots (PointWise x a) where
  root n  = fmap (root n)

instance Transcendental a => Transcendental (PointWise x a) where
  pi = pure pi
  -- log = fmap log
  -- sin = fmap sin
  -- cos = fmap cos
  -- asin = fmap asin
  -- acos = fmap acos
  -- atan = fmap atan
  -- sinh = fmap sinh
  -- cosh = fmap cosh
  -- asinh = fmap asinh
  -- acosh = fmap acosh
  -- atanh = fmap atanh
  exp = fmap exp

instance Multiplicative a => Scalable (PointWise x a) (PointWise x a) where
  (*^) = (*)

instance Ring a => Ring (PointWise x a) where
  fromInteger = PW . const . fromInteger

instance Field a => Field (PointWise x a) where
  fromRational = PW . const . fromRational

type S γ = PointWise (Env γ) RR

lk :: Var γ -> Env γ -> RR
lk Get (_,x) = x
lk (Weaken x) (ρ,_) = lk x ρ

lk' :: Var γ -> S γ
lk' v = PW $ lk v

evalC :: forall γ. Coef γ -> S γ
evalC (Coef c) = LC.eval (\x -> PW @(Env γ) $ \_ρ -> Models.Field.eval @RR x)
                         (exp . evalP) c

evalP :: forall γ. Poly γ -> S γ
evalP = Multi.eval evalC evalE 

evalE :: forall γ. Elem γ -> S γ
evalE = \case
  Supremum dir es -> case dir of
    Min ->  foldr (liftA2 min) (pure ( 1/0)) (evalP <$> es)
    Max ->  foldr (liftA2 max) (pure (-1/0)) (evalP <$> es)
  Vari x -> lk' x
  CharFun x -> fmap (\y -> if y >= 0 then 1 else 0) (evalP x)


approxIntegrals :: Int -> Env γ -> P γ -> RR
approxIntegrals n ρ =
  let evP x = fromPointWise (evalP x) ρ
  in \case
      Add a b -> approxIntegrals n ρ a + approxIntegrals n ρ b
      Div a b -> approxIntegrals n ρ a / approxIntegrals n ρ b
      Integrate (mkSuprema -> (lo,hi)) e ->
        realPart (Chebyshev.integral @Double @C n (evP lo) (evP hi) $
                  \x -> approxIntegrals n (ρ,x) e :+ 0)
      Ret x -> evP x
      Cond (IsNegative c) e -> if A.eval Models.Field.eval (flip lk ρ) c <= 0 then approxIntegrals n ρ e else 0
      Cond (IsZero _) _ -> error "approxIntegrals: equality not eliminated?"
