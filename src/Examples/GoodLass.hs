{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Examples.GoodLass where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Integrals
import Models.Integrals.Types (P(..),Domain(..),swap2P)
import TLC.HOAS
import qualified TLC.Terms as F
import qualified Algebra.Linear.Vector as V
import qualified Algebra.Morphism.Affine as A

toMath :: IO ()
toMath = do
  putStr "l0 = "
  maxima $ l0Expr
  putStr "s1 = "
  maxima $ s1Expr
  putStr "l1 = "
  maxima $ l1Expr

  putStr "l0 marginalised in X "
  maxima $ l0X
  putStr "l0 marginalised in Y "
  maxima $ l0Y
  putStr "l1 marginalised in X "
  maxima $ l1X
  putStr "l1 marginalised in Y "
  maxima $ l1Y

-- >>> toMath
-- l0 = charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-1/2*(20/7*(23/4 - x))^2)*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-1)
-- s1 = charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4)*(exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4) + exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4))^(-1)
-- l1 = charfun(-7 + y <= 0)*charfun(9/2 - y <= 0)*charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*charfun(-x + y <= 0)*8/7*(2*%pi)^(-1/2)*exp(-1/2*(20/7*(23/4 - x))^2)^5*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4)*(exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4) + exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4))^(-1)*(8/7*(2*%pi)^(-1/2)*integrate(exp(-1/2*(20/7*(23/4 - z))^2)^5*integrate(integrate(exp(-1/2*(20/7*(23/4 - v))^2), v, 9/2, 7)^(-4)*(charfun(u - z <= 0)*exp(-1/2*(20/7*(23/4 - z))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - v))^2), v, 9/2, 7)^(-4) + charfun(-u + z <= 0)*exp(-1/2*(20/7*(23/4 - z))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - v))^2), v, 9/2, 7)^(-4) + exp(-1/2*(20/7*(23/4 - z))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - v))^2), v, 9/2, 7)^(-4))^(-1), u, 9/2, 7), z, 9/2, 7))^(-1)
-- l0 marginalised in X charfun(-7 + x <= 0)*integrate(exp(-1/2*(20/7*(23/4 - y))^2)*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-1), y, x, 7)
-- l0 marginalised in Y charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*(x - 9/2)*exp(-1/2*(20/7*(23/4 - x))^2)*integrate(exp(-1/2*(20/7*(23/4 - y))^2), y, 9/2, 7)^(-1)
-- l1 marginalised in X charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*charfun(-7 + x <= 0)*8/7*(2*%pi)^(-1/2)*integrate(exp(-1/2*(20/7*(23/4 - y))^2)^5*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4)*(exp(-1/2*(20/7*(23/4 - y))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4) + exp(-1/2*(20/7*(23/4 - y))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4))^(-1)*(8/7*(2*%pi)^(-1/2)*integrate(exp(-1/2*(20/7*(23/4 - z))^2)^5*integrate(integrate(exp(-1/2*(20/7*(23/4 - v))^2), v, 9/2, 7)^(-4)*(charfun(u - z <= 0)*exp(-1/2*(20/7*(23/4 - z))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - v))^2), v, 9/2, 7)^(-4) + charfun(-u + z <= 0)*exp(-1/2*(20/7*(23/4 - z))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - v))^2), v, 9/2, 7)^(-4) + exp(-1/2*(20/7*(23/4 - z))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - v))^2), v, 9/2, 7)^(-4))^(-1), u, 9/2, 7), z, 9/2, 7))^(-1), y, x, 7)
-- l1 marginalised in Y charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*charfun(9/2 - x <= 0)*8/7*(2*%pi)^(-1/2)*(x - 9/2)*exp(-1/2*(20/7*(23/4 - x))^2)^5*integrate(exp(-1/2*(20/7*(23/4 - y))^2), y, 9/2, 7)^(-4)*(exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - y))^2), y, 9/2, 7)^(-4) + exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - y))^2), y, 9/2, 7)^(-4))^(-1)*(8/7*(2*%pi)^(-1/2)*integrate(exp(-1/2*(20/7*(23/4 - y))^2)^5*integrate(integrate(exp(-1/2*(20/7*(23/4 - u))^2), u, 9/2, 7)^(-4)*(charfun(z - y <= 0)*exp(-1/2*(20/7*(23/4 - y))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - u))^2), u, 9/2, 7)^(-4) + charfun(-z + y <= 0)*exp(-1/2*(20/7*(23/4 - y))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - u))^2), u, 9/2, 7)^(-4) + exp(-1/2*(20/7*(23/4 - y))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - u))^2), u, 9/2, 7)^(-4))^(-1), z, 9/2, 7), y, 9/2, 7))^(-1)

-- >>> plotData
-- l0...
-- s1...
-- l1...
-- l0x...
-- l0y...
-- l1x...
-- l1y...


domHi :: Rational
domHi = 7

domLo :: Rational
domLo = 4.5

plotOptions :: PlotOptions
plotOptions = PlotOptions {..} where
   plotDomainLo = fromRational domLo
   plotDomainHi = fromRational domHi
   plotResolution = 128

varsToSituation :: Exp a -> Exp b -> (Exp (a ':× b), Exp 'U)
varsToSituation x y = (Pair x y,isTall)
alpha :: Rational
alpha = 4
uu :: Int -> Exp 'U
uu = Con . Utt 
isTall :: Exp 'U
isTall = uu 1
isShort :: Exp 'U
isShort = uu 2
vaccuous :: Exp 'U
vaccuous = uu 3

utteranceDistribution :: Exp (('U ⟶ 'R) ⟶ 'R)
utteranceDistribution = Lam $ \k -> k @@ (uu 1) + k @@ (uu 2) + k @@ (uu 3)

linguisticParameterDistribution :: Exp (('R ⟶ 'R) ⟶ 'R)
linguisticParameterDistribution = uniform domLo domHi

interpU :: Exp 'U -> Exp 'R -> Exp 'R -> Exp 'T
interpU u θ h = Con ((Interp F.Z)) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                                       `Pair` θ
                                                       `Pair` (Lam $ \_ -> Con ((F.Tru)))
                                                       `Pair` (Lam $ \_ -> h)
                                                       `Pair` Con ((F.Entity 0)))

worldDistribution :: Exp (('R ⟶ 'R) ⟶ 'R)
worldDistribution = normal 5.75 0.35 ⋆ \h ->
           observe (h ≥ fromRational domLo) >>
           observe (fromRational domHi ≥ h) >>
           η h

contextDistribution :: Exp ((('R ':× 'R) ⟶ 'R) ⟶ 'R)
contextDistribution =
    worldDistribution ⋆ \h ->
    linguisticParameterDistribution ⋆ \θ ->
    η (θ `Pair` h)

asExpression :: Exp ('R ⟶ 'R ⟶ 'R) -> P ('Unit × 'R × 'R)
asExpression = simplifyFun2 [] . fromHoas

α :: Rational
α = alpha

-- s1 :: Exp context -> Exp (('U ⟶ 'R) ⟶ 'R)
s1 :: Exp ('R ':× 'R) -> Exp (('U ⟶ 'R) ⟶ 'R)
s1 ctx = utteranceDistribution ⋆ \u ->
           let θ = Fst ctx
               h = Snd ctx
           in factor ((distr (l0 θ u) h) ^/ α) >>
              η u

-- | Literal listener
-- l0 ::  Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)
l0 :: Exp 'R -> Exp 'U -> Exp (('R ⟶ 'R) ⟶ 'R)
l0 θ u = worldDistribution ⋆ \h ->
         observe (interpU u θ h) >>
         η h

-- | Pragmatic listener
-- l1 :: Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)

l1 :: Exp 'U -> Exp ((('R ':× 'R) ⟶ 'R) ⟶ 'R)
l1 u = contextDistribution ⋆ \ctx -> 
         factor (s1Distr u ctx) >>
         η ctx

-- l0Distr :: Exp 'U -> Exp context -> Exp 'R
l0Distr :: Exp 'U -> Exp ('R × 'R) -> Exp 'R
l0Distr u ctx = distr (l0 θ u) h
  where θ = Fst ctx
        h = Snd ctx

-- s1Distr :: Exp context -> Exp 'U -> Exp 'R
s1Distr :: Exp 'U -> Exp ('R ':× 'R) -> Exp 'R
s1Distr u ctx = distr (s1 ctx) u

-- l1Distr :: Exp 'U -> Exp context -> Exp 'R
l1Distr :: Exp 'U -> Exp ('R ':× 'R) -> Exp 'R
l1Distr u ctx = distr (l1 u) ctx

-- twoDimFunOf :: (Exp utterance -> Exp context -> Exp 'R) -> Exp ('R ⟶ 'R ⟶ 'R)
twoDimFunOf :: (Exp 'U -> Exp (a ':× b1) -> Exp b2) -> Exp (a ':-> (b1 ':-> b2))
twoDimFunOf f = Lam $ \x -> Lam $ \y ->
   let (h,u) = varsToSituation x y
   in f u h

utilityl0 :: Exp ('R ⟶ 'R ⟶ 'R)
utilityl0 = twoDimFunOf l0Distr

utilitys1 :: Exp ('R ⟶ 'R ⟶ 'R)
utilitys1 = twoDimFunOf s1Distr 

utilityl1 :: Exp ('R ⟶ 'R ⟶ 'R)
utilityl1 = twoDimFunOf l1Distr

l0Expr, l1Expr, s1Expr :: P (('Unit × 'R) × 'R)
l0Expr = asExpression utilityl0
l1Expr = asExpression utilityl1
s1Expr = asExpression utilitys1

l0Samples, l1Samples, s1Samples :: V.Vec (V.Vec Double)
l0Samples = approxTop plotOptions l0Expr
l1Samples = approxTop plotOptions l1Expr
s1Samples = approxTop plotOptions s1Expr

l0xSamples, l0ySamples, l1xSamples, l1ySamples :: V.Vec Double
l0xSamples = approxTop plotOptions l0X
l0ySamples = approxTop plotOptions l0Y
l1xSamples = approxTop plotOptions l1X
l1ySamples = approxTop plotOptions l1Y


integrateOnPlotDomain :: P (γ × 'R) -> P γ
integrateOnPlotDomain  = normalise . Integrate (Domain
                  [A.constant (fromRational (toRational plotDomainLo))]
                  [A.constant (fromRational (toRational plotDomainHi))])
 where PlotOptions{..} = plotOptions
                         
l0X,l0Y,l1X,l1Y :: P ('Unit × 'R)
l0X = integrateOnPlotDomain l0Expr
l1X = integrateOnPlotDomain l1Expr
l0Y = integrateOnPlotDomain $ swap2P $ l0Expr
l1Y = integrateOnPlotDomain $ swap2P $ l1Expr


plotData :: IO ()
plotData = do
  putStrLn "l0..." ; toGnuPlot plotOptions "l0.dat" l0Samples
  putStrLn "s1..." ; toGnuPlot plotOptions "s1.dat" s1Samples
  putStrLn "l1..." ; toGnuPlot plotOptions "l1.dat" l1Samples
  putStrLn "l0x..." ; toGnuPlot1d plotOptions "l0x.dat" l0xSamples
  putStrLn "l0y..." ; toGnuPlot1d plotOptions "l0y.dat" l0ySamples
  putStrLn "l1x..." ; toGnuPlot1d plotOptions "l1x.dat" l1xSamples
  putStrLn "l1y..." ; toGnuPlot1d plotOptions "l1y.dat" l1ySamples
    
