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
isTall :: Exp 'U
isTall = Con $ Utt $ F.MergeRgt F.Vl F.IsTall
isShort :: Exp 'U
isShort = Con $ Utt $ F.MergeRgt F.Vl F.IsShort
vaccuous :: Exp 'U
vaccuous = Con $ Silence
plottedUtt :: Exp 'U
plottedUtt = isTall

cost :: Double -> Exp 'R
cost x = Con (F.Incl (toRational (exp (- x) :: Double))) 

tallShortOrSilence = Lam $ \k -> cost 2 * (k @@ isTall) + k @@ vaccuous  

utteranceDistribution :: Exp (('U ⟶ 'R) ⟶ 'R)
utteranceDistribution = tallShortOrSilence

-- distribution for θ 
linguisticParameterDistribution :: Exp (('R ⟶ 'R) ⟶ 'R)
linguisticParameterDistribution = uniform domLo domHi

interpU :: Exp 'U -> Exp 'R -> Exp 'R -> Exp 'T
interpU u θ h = Con (Interp F.Z) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                             `Pair` θ
                                             `Pair` (Lam $ \_ -> Con (F.Tru))
                                             `Pair` (Lam $ \_ -> h)
                                             `Pair` Con (F.Entity 0))

-- Distribution over height (w in Good-Lass)
worldDistribution :: Exp (('R ⟶ 'R) ⟶ 'R)
worldDistribution = normal 5.75 0.35 ⋆ \h ->
           observe (h ≥ fromRational domLo) >>
           observe (fromRational domHi ≥ h) >>
           η h


asExpression :: Exp ('R ⟶ 'R ⟶ 'R) -> P ('Unit × 'R × 'R)
asExpression = simplifyFun2 [] . fromHoas

asExpression1 :: Exp ('R ⟶ 'R) -> P ('Unit × 'R)
asExpression1 = simplifyFun [] . fromHoas

α :: Rational
α = alpha

-- | Literal listener (posterior distribution over worlds)
-- l0 ::  Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)
l0 :: Exp 'U -> Exp (('R ⟶ 'R) ⟶ 'R)
l0 u = worldDistribution ⋆ \h ->
       linguisticParameterDistribution ⋆ \θ -> 
         observe (interpU u θ h) >> -- filter incompatible worlds
         η h

-- s1 :: Exp context -> Exp (('U ⟶ 'R) ⟶ 'R)
s1 :: Exp 'R -> Exp (('U ⟶ 'R) ⟶ 'R)
s1 h = utteranceDistribution ⋆ \u ->
       factor ((distr (l0 u) h) ^/ α) >>
              η u

-- | Pragmatic listener
-- l1 :: Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)

l1 :: Exp 'U -> Exp (('R ⟶ 'R) ⟶ 'R)
l1 u =
  worldDistribution ⋆ \h ->
  -- linguisticParameterDistribution ⋆ \θ -> -- useless because it isn't passed to s1
  factor (s1Distr u h) >>
  η h

-- l0Distr :: Exp 'U -> Exp context -> Exp 'R
l0Distr :: Exp 'U -> Exp ('R) -> Exp 'R
l0Distr u h = distr (l0 u) h

-- s1Distr :: Exp context -> Exp 'U -> Exp 'R
s1Distr :: Exp 'U -> Exp 'R -> Exp 'R
s1Distr u h = distr (s1 h) u

-- l1Distr :: Exp 'U -> Exp context -> Exp 'R
l1Distr :: Exp 'U -> (Exp 'R) -> Exp 'R
l1Distr u h = distr (l1 u) h

utilityl0 :: Exp ('R ⟶ 'R)
utilityl0 = Lam (l0Distr plottedUtt)

utilitys1 :: Exp ('R ⟶ 'R)
utilitys1 = Lam (s1Distr plottedUtt) 

utilityl1 :: Exp ('R ⟶ 'R)
utilityl1 = Lam (l1Distr plottedUtt) 

l1Expr, s1Expr,l0Expr :: P ('Unit × 'R)
l0Expr = asExpression1 utilityl0
l1Expr = asExpression1 utilityl1
s1Expr = asExpression1 utilitys1

s1ySamples,l0ySamples, l1ySamples :: V.Vec Double
s1ySamples = approxTop plotOptions s1Expr
l0ySamples = approxTop plotOptions l0Expr
l1ySamples = approxTop plotOptions l1Expr

integrateOnPlotDomain :: P (γ × 'R) -> P γ
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
    
