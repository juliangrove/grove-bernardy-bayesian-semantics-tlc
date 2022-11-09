{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Examples.Guy where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..), Floating(..))
import Models.Integrals
import Models.Integrals.Types (P(..), Domain(..), )
import TLC.HOAS
import qualified TLC.Terms as F
import qualified Algebra.Linear.Vector as V
import qualified Algebra.Morphism.Affine as A
import Examples.Utterances

toMath :: IO ()
toMath = do
  putStr "l0 = "
  maxima $ l0Expr
  putStr "s1 = "
  maxima $ s1Expr
  putStr "l1 = "
  maxima $ l1Expr

-- >>> toMath
-- l0 = charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-200/49*(23/4 - x)^2)*integrate(exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^(-1)
-- s1 = charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^(-4)*(16/625*(-9/2 + min(7, x))^4*exp(-200/49*(23/4 - x)^2)^4*625/16*integrate((-9/2 + min(7, y))*exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^(-4) + exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^(-4) + 16/625*(7 - max(9/2, x))^4*exp(-200/49*(23/4 - x)^2)^4*625/16*integrate((7 - max(9/2, y))*exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^(-4))^(-1)
-- l1 = charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-200/49*(23/4 - x)^2)^4*exp(-200/49*(23/4 - x)^2)*integrate(exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^(-4)*integrate(exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^4*integrate(exp(-200/49*(23/4 - y)^2)^4*exp(-200/49*(23/4 - y)^2)*(16/625*(-9/2 + min(7, y))^4*exp(-200/49*(23/4 - y)^2)^4*625/16*integrate((-9/2 + min(7, z))*exp(-200/49*(23/4 - z)^2), z, 9/2, 7)^(-4) + exp(-200/49*(23/4 - y)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, 9/2, 7)^(-4) + 16/625*(7 - max(9/2, y))^4*exp(-200/49*(23/4 - y)^2)^4*625/16*integrate((7 - max(9/2, z))*exp(-200/49*(23/4 - z)^2), z, 9/2, 7)^(-4))^(-1), y, 9/2, 7)^(-1)*(16/625*(-9/2 + min(7, x))^4*exp(-200/49*(23/4 - x)^2)^4*625/16*integrate((-9/2 + min(7, y))*exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^(-4) + exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^(-4) + 16/625*(7 - max(9/2, x))^4*exp(-200/49*(23/4 - x)^2)^4*625/16*integrate((7 - max(9/2, y))*exp(-200/49*(23/4 - y)^2), y, 9/2, 7)^(-4))^(-1)

-- >>> plotData
-- s1...
-- l0y...
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

alpha :: Rational
alpha = 4

plottedUtt :: Exp F.U
plottedUtt = isTall


utteranceDistribution :: Exp ((F.U ⟶ F.R) ⟶ F.R)
utteranceDistribution = tallShortOrSilence α

-- distribution for θ 
linguisticParameterDistribution :: Exp ((F.R ⟶ F.R) ⟶ F.R)
linguisticParameterDistribution = uniform (fromRational domLo) (fromRational domHi)

interpU :: Exp F.U -> Exp F.R -> Exp F.R -> Exp F.T
interpU u θ h = Con (Interp F.Z) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                             `Pair` θ
                                             `Pair` (Lam $ \_ -> Con (F.Tru))
                                             `Pair` (Lam $ \_ -> h)
                                             `Pair` Con (F.Entity 0))

-- Distribution over height (w in Good-Lass)
worldDistribution :: Exp ((F.R ⟶ F.R) ⟶ F.R)
worldDistribution = normal 5.75 0.35 ⋆ \h ->
           observe (h ≥ fromRational domLo) >>
           observe (fromRational domHi ≥ h) >>
           η h


asExpression :: Exp (F.R ⟶ F.R ⟶ F.R) -> P (F.Unit × F.R × F.R)
asExpression = simplifyFun2 [] . fromHoas

asExpression1 :: Exp (F.R ⟶ F.R) -> P (F.Unit × F.R)
asExpression1 = simplifyFun [] . fromHoas

α :: Rational
α = alpha

-- | Literal listener (posterior distribution over worlds)
-- l0 ::  Exp F.U -> Exp ((context ⟶ F.R) ⟶ F.R)
l0 :: Exp F.U -> Exp ((F.R ⟶ F.R) ⟶ F.R)
l0 u = worldDistribution ⋆ \h ->
       linguisticParameterDistribution ⋆ \θ -> 
         observe (interpU u θ h) >> -- filter incompatible worlds
         η h

-- s1 :: Exp context -> Exp ((F.U ⟶ F.R) ⟶ F.R)
s1 :: Exp F.R -> Exp ((F.U ⟶ F.R) ⟶ F.R)
s1 h = utteranceDistribution ⋆ \u ->
       factor ((distr (l0 u) h) ^/ α) >>
              η u

-- | Pragmatic listener
-- l1 :: Exp F.U -> Exp ((context ⟶ F.R) ⟶ F.R)

l1 :: Exp F.U -> Exp ((F.R ⟶ F.R) ⟶ F.R)
l1 u =
  worldDistribution ⋆ \h ->
  -- linguisticParameterDistribution ⋆ \θ -> -- useless because it isn't passed to s1
  factor (s1Distr u h) >>
  η h

-- l0Distr :: Exp F.U -> Exp context -> Exp F.R
l0Distr :: Exp F.U -> Exp (F.R) -> Exp F.R
l0Distr u h = distr (l0 u) h

-- s1Distr :: Exp context -> Exp F.U -> Exp F.R
s1Distr :: Exp F.U -> Exp F.R -> Exp F.R
s1Distr u h = distr (s1 h) u

-- l1Distr :: Exp F.U -> Exp context -> Exp F.R
l1Distr :: Exp F.U -> (Exp F.R) -> Exp F.R
l1Distr u h = distr (l1 u) h

utilityl0 :: Exp (F.R ⟶ F.R)
utilityl0 = Lam (l0Distr plottedUtt)

utilitys1 :: Exp (F.R ⟶ F.R)
utilitys1 = Lam (s1Distr plottedUtt) 

utilityl1 :: Exp (F.R ⟶ F.R)
utilityl1 = Lam (l1Distr plottedUtt) 

l1Expr, s1Expr,l0Expr :: P (F.Unit × F.R)
l0Expr = asExpression1 utilityl0
l1Expr = asExpression1 utilityl1
s1Expr = asExpression1 utilitys1

s1ySamples,l0ySamples, l1ySamples :: V.Vec Double
s1ySamples = approxTop plotOptions s1Expr
l0ySamples = approxTop plotOptions l0Expr
l1ySamples = approxTop plotOptions l1Expr

integrateOnPlotDomain :: P (γ × F.R) -> P γ
integrateOnPlotDomain  = normalise . Integrate (Domain
                  [A.constant (fromRational (toRational plotDomainLo))]
                  [A.constant (fromRational (toRational plotDomainHi))])
 where PlotOptions{..} = plotOptions
                         


plotData :: IO ()
plotData = do
  putStrLn "------------ Averaging "
  putStrLn "l0y..." ; toGnuPlot1d plotOptions "goodlass-avg-l0y.1d.dat" l0ySamples
  putStrLn "s1..."  ; toGnuPlot1d plotOptions "goodlass-avg-s1y.1d.dat" s1ySamples
  putStrLn "l1y..." ; toGnuPlot1d plotOptions "goodlass-avg-l1y.1d.dat" l1ySamples
    
