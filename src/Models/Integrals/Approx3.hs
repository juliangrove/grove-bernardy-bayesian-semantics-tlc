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
size__ = 128

lint :: forall s a. Field s => Module s a => s -> a -> a -> a
lint f lo hi = (0.5::s) *^ ((f+1) *^ hi + (1-f) *^ lo)

domLo, domHi :: RR
domLo = 65 - 15
domHi = 63 + 15

rlint :: RR -> RR
rlint x = (2 * x - domLo - domHi) / (domHi - domLo)

-- >>> fmap rlint chebPtsDom
-- Samples (Vec [1.0,0.9987954562051726,0.9951847266721969,0.9891765099647813,0.9807852804032308,0.9700312531945443,0.9569403357322088,0.9415440651830209,0.9238795325112875,0.9039892931234433,0.8819212643483553,0.8577286100002723,0.8314696123025456,0.8032075314806448,0.7730104533627369,0.7409511253549595,0.7071067811865476,0.6715589548470191,0.6343932841636445,0.5956993044924331,0.5555702330196013,0.5141027441932209,0.47139673682599864,0.42755509343028136,0.38268343236508995,0.33688985339221916,0.29028467725446205,0.24298017990326456,0.19509032201612797,0.14673047445536155,9.801714032956141e-2,4.9067674327417876e-2,0.0,-4.9067674327417876e-2,-9.801714032956141e-2,-0.14673047445536155,-0.19509032201612797,-0.24298017990326387,-0.29028467725446205,-0.33688985339222055,-0.38268343236508995,-0.4275550934302821,-0.4713967368259972,-0.5141027441932223,-0.555570233019602,-0.5956993044924339,-0.6343932841636459,-0.6715589548470184,-0.7071067811865476,-0.7409511253549589,-0.7730104533627369,-0.8032075314806448,-0.8314696123025456,-0.8577286100002723,-0.8819212643483546,-0.9039892931234427,-0.9238795325112867,-0.9415440651830209,-0.9569403357322088,-0.9700312531945435,-0.9807852804032301,-0.9891765099647806,-0.9951847266721977,-0.9987954562051726,-1.0])

type WithCache a = State (Map (P ('Unit × 'R)) (Chebyshev.Polynomial RR)) a


chebPtsDom :: Chebyshev.Samples RR
chebPtsDom =  (\x -> lint x domLo domHi) <$> Chebyshev.Samples (Chebyshev.chebPoints @RR size__)

-- >>> chebPtsDom
-- Samples (Vec [75.0,74.98795456205173,74.95184726672197,74.89176509964781,74.80785280403231,74.70031253194544,74.56940335732209,74.41544065183021,74.23879532511287,74.03989293123443,73.81921264348355,73.57728610000272,73.31469612302546,73.03207531480645,72.73010453362737,72.4095112535496,72.07106781186548,71.71558954847019,71.34393284163644,70.95699304492433,70.55570233019601,70.14102744193221,69.71396736825999,69.27555093430281,68.8268343236509,68.36889853392219,67.90284677254462,67.42980179903265,66.95090322016128,66.46730474455362,65.98017140329561,65.49067674327418,65.0,64.50932325672582,64.01982859670439,63.532695255446384,63.04909677983872,62.57019820096736,62.09715322745538,61.631101466077794,61.1731656763491,60.72444906569718,60.28603263174003,59.85897255806778,59.44429766980398,59.04300695507566,58.65606715836354,58.284410451529816,57.928932188134524,57.59048874645041,57.26989546637263,56.96792468519355,56.685303876974544,56.42271389999728,56.180787356516454,55.96010706876557,55.76120467488713,55.58455934816979,55.43059664267791,55.299687468054564,55.1921471959677,55.108234900352194,55.04815273327802,55.012045437948274,55.0])

approxIntegralsWithCache :: P 'Unit -> WithCache RR
approxIntegralsWithCache =
  let aa = approxIntegralsWithCache
  in \case
      Add a b -> (+) <$> aa a <*> aa b
      Div a b -> (/) <$> aa a <*> aa b
      Integrate d e -> do
        cachedFun <- gets (M.lookup e)
        p <- case cachedFun of
          Nothing -> do
            s <- flip traverse chebPtsDom $ \x -> do
                   y <- aa (substP (\case Get -> A.constant (Models.Field.Con (toRational x)) ; Weaken v -> A.var v) e)
                   when (isInfinite y) $ do
                     error ("approxIntegralsWithCache: infinite sample\n  x=" ++ show x ++ "\n   e=" ++ show e)
                   pure y
            let p = Chebyshev.integrate @RR $ fmap realPart $ Chebyshev.samplesToPoly @(Complex RR) $ fmap (:+ 0) s
            modify (M.insert e p)
            pure p
          Just p -> pure p
        let (Domain (maximum . fmap evalX  -> lo0) (minimum . fmap evalX -> hi0)) = d
            [lo,hi] = fmap rlint [lo0,hi0]
        pure (((0.5::RR) *^ (hi-lo)) *^ (Chebyshev.clenshaw hi p - Chebyshev.clenshaw lo p))
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
