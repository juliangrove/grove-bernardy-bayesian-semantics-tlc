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
{-# LANGUAGE RebindableSyntax #-}

module Models.Integrals.Approx3  where

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
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M

import Models.Integrals.Types

type family Env γ where
  Env 'Unit = ()
  Env (a ':× b) = (Env a, Env b)
  Env 'R = Double

type RR = Double


evalC :: Coef 'Unit -> RR
evalC (Coef c) = LC.eval (\x -> Models.Field.eval @RR x) (exp . evalP) c

evalP :: Poly 'Unit -> RR
evalP = Multi.eval evalC evalE 

evalE :: Elem 'Unit -> RR
evalE = \case
  Supremum dir es -> case dir of
    Min ->  foldr (min) (( 1/0)) (evalP <$> es)
    Max ->  foldr (max) ((-1/0)) (evalP <$> es)
  Vari x -> case x of
  CharFun x -> if evalP x >= 0 then 1 else 0 

evalX :: Expr  'Unit -> RR
evalX = A.eval Models.Field.eval (\case)

approxIntegralsNaive :: Int -> P 'Unit -> RR
approxIntegralsNaive n = \case
      Add a b -> approxIntegralsNaive n a + approxIntegralsNaive n b
      Div a b -> approxIntegralsNaive n a / approxIntegralsNaive n b
      Integrate (mkSuprema -> (lo,hi)) e ->
        realPart (Chebyshev.integral @Double @C n (evalP lo) (evalP hi) $
                     \x -> approxIntegralsNaive n (substP (\case Get -> A.constant (Models.Field.Con (toRational x))
                                                                 ; Weaken v -> A.var v) e) :+ 0)
     
      Ret x -> evalP x
      Cond (IsNegative c) e -> if A.eval @RR Models.Field.eval (\case) c <= 0 then approxIntegralsNaive n e else 0
      Cond (IsZero _) _ -> error "approxIntegralsNaive: equality not eliminated?"


size__ :: Int
size__ = 16

lint :: forall s a. Field s => Module s a => s -> a -> a -> a
lint f lo hi = (0.5::s) *^ ((f+1) *^ hi + (1-f) *^ lo)

domLo, domHi :: RR
domLo = 55
domHi = 75

type WithCache a = State (Map (P ('Unit × 'R)) (Chebyshev.Polynomial RR)) a


chebPtsDom :: Chebyshev.Samples RR
chebPtsDom =  (\x -> lint x domLo domHi) <$> Chebyshev.Samples (Chebyshev.chebPoints @RR size__)


approxIntegralsWithCache :: P 'Unit -> WithCache RR
approxIntegralsWithCache =
  let aa = approxIntegralsWithCache
  in \case
      Add a b -> (+) <$> aa a <*> aa b
      Div a b -> (/) <$> aa a <*> aa b
      Integrate (Domain (maximum . fmap evalX  -> lo) (maximum . fmap evalX -> hi)) e -> do
        cachedFun <- gets (M.lookup e)
        p <- case cachedFun of
          Nothing -> do
            s <- flip traverse chebPtsDom $ \x' -> 
              aa (substP (\case Get -> A.constant (Models.Field.Con (toRational x')) ; Weaken v -> A.var v) e)
            pure $ Chebyshev.integrate @RR $ fmap realPart $ Chebyshev.samplesToPoly @(Complex RR) $ fmap (:+ 0) s
          Just q -> pure q
        pure (((0.5::RR) *^ (domHi-domLo)) *^ (Chebyshev.clenshaw hi p - Chebyshev.clenshaw lo p))
      Ret x -> pure (evalP x)
      Cond (IsNegative c) e -> if A.eval @RR Models.Field.eval (\case) c <= 0 then aa e else pure 0
      Cond (IsZero _) _ -> error "approxIntegrals: equality not eliminated?"

type family FUN γ x where
  FUN 'Unit x = x
  FUN (a ':× 'R) x = Chebyshev.Samples (FUN a x)

class KnownContext (γ :: Type) where
  approxFUN :: P γ -> WithCache (FUN γ RR)
instance KnownContext 'Unit where
  approxFUN x = approxIntegralsWithCache x
instance KnownContext γ => KnownContext (γ × 'R) where
  approxFUN e = flip traverse chebPtsDom $ \x ->
                approxFUN $
                flip substP e $ \case
                   Get -> A.constant (Models.Field.Con (toRational x))
                   Weaken v -> A.var v

runWithCache :: WithCache x -> x
runWithCache e = fst (runState e M.empty)

approxTop :: KnownContext γ => P γ -> FUN γ RR
approxTop e = runWithCache  (approxFUN e)
