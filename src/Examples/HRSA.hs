{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Examples.HRSA where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..), Floating(..))
import Models.Integrals
import Models.Integrals.Types (P(..),Domain(..),swap2P)
import TLC.HOAS
import qualified TLC.Terms as F
import qualified Algebra.Linear.Vector as V
import qualified Algebra.Morphism.Affine as A
import Examples.Utterances

-- ∃γ. ∃u. (... × .. Exp ((γ ⟶ F.R) ⟶ F.R))
data RSAIn = forall context utterance. (Equality context, Equality utterance) => RSAIn {
    prefix :: String,
    alpha :: Rational,
    contextDistribution    :: Exp ((context ⟶ F.R) ⟶ F.R),
    utteranceDistribution  :: Exp ((utterance ⟶ F.R) ⟶ F.R),
    interpU :: Exp utterance -> Exp context -> Exp F.T,

    varsToSituation :: Exp F.R -> Exp F.R -> (Exp context, Exp utterance),
    plotOptions :: PlotOptions
  }

data RSAOut = RSAOut {
    l0Expr, l1Expr, s1Expr :: P (F.Unit × F.R × F.R),

    l0X,l0Y :: P (F.Unit × F.R),
    l0Samples, l1Samples, s1Samples :: V.Vec (V.Vec Double),
    l0xSamples,l0ySamples :: V.Vec Double,
    plotData :: IO ()
    }

toMath :: RSAOut -> IO ()
toMath RSAOut {..} = do
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

-- >>> toMath (exampleCookies 1)
-- l0 = charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(-x <= 0)*exp(-2*(-4 + x))*integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, max(0, y), 7)^(-1)*(1 + exp(-2*(-4 + x)))^(-2)
-- s1 = charfun(-y <= 0)*charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(-x <= 0)*exp(-2*(-4 + x))^(-1)*exp(-2*(-4 + x))*integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, y, 7)^(-1)*(1 + exp(-2*(-4 + x)))^(-2)*(1 + exp(-2*(-4 + x)))^2*integrate(integrate(exp(-2*(-4 + u))*(1 + exp(-2*(-4 + u)))^(-2), u, z, 7)^(-1), z, 0, x)^(-1)
-- l1 = charfun(-y <= 0)*charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(-x <= 0)*exp(-2*(-4 + x))^(-1)*exp(-2*(-4 + x))*exp(-2*(-4 + x))*integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, y, 7)*integrate(integrate(exp(-2*(-4 + u))*(1 + exp(-2*(-4 + u)))^(-2), u, z, 7)^(-1), z, 0, x)^(-1)*integrate(exp(-2*(-4 + z))^(-1)*exp(-2*(-4 + z))*exp(-2*(-4 + z))*integrate(integrate(exp(-2*(-4 + v))*(1 + exp(-2*(-4 + v)))^(-2), v, u, 7)^(-1), u, 0, z)^(-1)*(1 + exp(-2*(-4 + z)))^(-2)*(1 + exp(-2*(-4 + z)))^(-2)*(1 + exp(-2*(-4 + z)))^2, z, y, 7)^(-1)*integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, y, 7)^(-1)*(1 + exp(-2*(-4 + x)))^(-2)*(1 + exp(-2*(-4 + x)))^(-2)*(1 + exp(-2*(-4 + x)))^2
-- l0 marginalised in X charfun(-7 + x <= 0)*integrate(exp(-2*(-4 + y))*(1 + exp(-2*(-4 + y)))^(-2), y, max(0, x), 7)^(-1)*integrate(exp(-2*(-4 + y))*(1 + exp(-2*(-4 + y)))^(-2), y, max(0, x), 7)
-- l0 marginalised in Y charfun(-7 + x <= 0)*charfun(-x <= 0)*exp(-2*(-4 + x))*(1 + exp(-2*(-4 + x)))^(-2)*integrate(integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, max(0, y), 7)^(-1), y, 0, min(7, x))

-- >>> plotData exampleCookies
-- l0...
-- s1...
-- l1...

exampleCookies :: Rational -> RSAOut
exampleCookies alpha = evaluate RSAIn {..} where
  prefix = ("cookies-continuous-" ++ show (fromRational alpha :: Double) ++ "-")
  varsToSituation y x = (x,y)
  plotOptions = PlotOptions {..}
  plotDomainLo = 0
  plotDomainHi = 7
  plotResolution = 128
  utteranceDistribution = uniform lo hi
  interpU u nCookies = nCookies ≥ u
  lo, hi :: forall a. Field a => a
  lo = fromRational (toRational plotDomainLo)
  hi = fromRational (toRational plotDomainHi)
  contextDistribution =
      normal (fromRational 4) (fromRational 1) ⋆ \nCookies ->
             observe (nCookies ≥ lo) >>
             observe (hi ≥ nCookies) >>
             η nCookies

exampleCookiesLogistic :: Rational -> RSAOut
exampleCookiesLogistic alpha = evaluate RSAIn {..} where
  prefix = ("cookies-logistic-" ++ show (fromRational alpha :: Double) ++ "-")
  varsToSituation y x = (x,y)
  plotOptions = PlotOptions {..}
  plotDomainLo = 0
  plotDomainHi = 7
  plotResolution = 128
  utteranceDistribution = lesbegue ⋆ \x -> observe (x ≥ zero) >> η x
  interpU u nCookies = nCookies ≥ u
  lo, hi :: forall a. Field a => a
  lo = fromRational (toRational plotDomainLo)
  hi = fromRational (toRational plotDomainHi)
  contextDistribution =
      logisticDistr (fromRational 4) (sqrt (fromRational 3) / pi) ⋆ \nCookies ->
             observe (nCookies ≥ lo) >>
             η nCookies

-- NOTE: The below can be simplified by Maxima with:
-- assume(x>0);
-- assume(z>0);
-- display2d: false;
-- for l1, the normalisation factor depends on y (utterance), but not on x, as expected. Can be deleted to get the effect explained in ISA.org

-- >>> toMath (exampleCookiesLogistic 1)
-- l0 = charfun(-x + y <= 0)*charfun(-x <= 0)*exp(-2*(-4 + x))*integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, max(0, y), inf)^(-1)*(1 + exp(-2*(-4 + x)))^(-2)
-- s1 = charfun(-y <= 0)*charfun(-x + y <= 0)*charfun(-x <= 0)*exp(-2*(-4 + x))^(-1)*exp(-2*(-4 + x))*integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, y, inf)^(-1)*(1 + exp(-2*(-4 + x)))^(-2)*(1 + exp(-2*(-4 + x)))^2*integrate(integrate(exp(-2*(-4 + u))*(1 + exp(-2*(-4 + u)))^(-2), u, z, inf)^(-1), z, 0, x)^(-1)
-- l1 = charfun(-y <= 0)*charfun(-x + y <= 0)*charfun(-x <= 0)*exp(-2*(-4 + x))^(-1)*exp(-2*(-4 + x))*exp(-2*(-4 + x))*integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, y, inf)*integrate(integrate(exp(-2*(-4 + u))*(1 + exp(-2*(-4 + u)))^(-2), u, z, inf)^(-1), z, 0, x)^(-1)*integrate(exp(-2*(-4 + z))^(-1)*exp(-2*(-4 + z))*exp(-2*(-4 + z))*integrate(integrate(exp(-2*(-4 + v))*(1 + exp(-2*(-4 + v)))^(-2), v, u, inf)^(-1), u, 0, z)^(-1)*(1 + exp(-2*(-4 + z)))^(-2)*(1 + exp(-2*(-4 + z)))^(-2)*(1 + exp(-2*(-4 + z)))^2, z, y, inf)^(-1)*integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, y, inf)^(-1)*(1 + exp(-2*(-4 + x)))^(-2)*(1 + exp(-2*(-4 + x)))^(-2)*(1 + exp(-2*(-4 + x)))^2
-- l0 marginalised in X charfun(-7 + x <= 0)*integrate(exp(-2*(-4 + y))*(1 + exp(-2*(-4 + y)))^(-2), y, max(0, x), inf)^(-1)*integrate(exp(-2*(-4 + y))*(1 + exp(-2*(-4 + y)))^(-2), y, max(0, x), 7)
-- l0 marginalised in Y charfun(-x <= 0)*exp(-2*(-4 + x))*(1 + exp(-2*(-4 + x)))^(-2)*integrate(integrate(exp(-2*(-4 + z))*(1 + exp(-2*(-4 + z)))^(-2), z, max(0, y), inf)^(-1), y, 0, min(7, x))

exampleTallThreshold :: RSAOut
exampleTallThreshold = evaluate RSAIn {..} where
  prefix = "vlad-is-tall"
  plotOptions = PlotOptions {..}
  plotDomainLo = 0
  plotDomainHi = 100
  plotResolution = 128
  varsToSituation x y = (Pair x y, isTall)
  alpha = 4
  utteranceDistribution :: Exp ((F.U ⟶ F.R) ⟶ F.R)
  utteranceDistribution = Lam $ \k -> k @@ isTall + k @@ isShort + k @@ vaccuous
  interpU :: Exp F.U -> Exp (F.R × F.R) -> Exp F.T
  interpU u ctx = Con (Interp F.Z) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                               `Pair` Fst ctx
                                               `Pair` (Lam $ \_ -> Con (F.Tru))
                                               `Pair` (Lam $ \_ -> Snd ctx)
                                               `Pair` Con (F.Entity 0))
  contextDistribution =
      normal 68 10 ⋆ \h ->
             observe (h ≥ fromInteger 0) >>
             observe (fromInteger 100 ≥ h) >>
      uniform (fromRational 0) (fromRational 100) ⋆ \θ ->
             η (θ `Pair` h)

exampleLassGood :: RSAOut
exampleLassGood = evaluate RSAIn {..} where
  prefix = "goodlass-std-"
  plotOptions = PlotOptions {..}
  plotDomainLo = 4.5
  plotDomainHi = 7
  plotResolution = 128
  varsToSituation x y = (Pair x y,isTall)
  alpha = 4
  utteranceDistribution :: Exp ((F.U ⟶ F.R) ⟶ F.R)
  utteranceDistribution = tallShortOrSilence alpha
  interpU :: Exp F.U -> Exp (F.R × F.R) -> Exp F.T
  interpU u ctx = Con (Interp F.Z) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                                         `Pair` Fst ctx
                                                         `Pair` (Lam $ \_ -> Con (F.Tru))
                                                         `Pair` (Lam $ \_ -> Snd ctx)
                                                         `Pair` Con (F.Entity 0))
  contextDistribution =
    normal 5.75 0.35 ⋆ \h ->
             observe (h ≥ fromRational 4.5) >>
             observe (fromInteger 7 ≥ h) >>
      uniform (fromRational 4.5) (fromRational 7) ⋆ \θ ->
             η (θ `Pair` h)


cost :: Double -> Exp F.R
cost x = Con (F.Incl (toRational (exp (- x) :: Double))) 
  
exampleLassGoodExtra :: RSAOut
exampleLassGoodExtra = evaluate RSAIn {..} where
  prefix = "goodlass-std-extra-"
  plotOptions = PlotOptions {..}
  plotDomainLo = 4.5
  plotDomainHi = 7
  plotResolution = 128
  varsToSituation x y = (Pair x y,isTall)
  alpha = 4
  utteranceDistribution :: Exp ((F.U ⟶ F.R) ⟶ F.R)
  utteranceDistribution = tallOrSilenceOrGiven alpha
  interpU :: Exp F.U -> Exp (F.R × F.R) -> Exp F.T
  interpU u ctx = Con (Interp F.Z) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                                         `Pair` Fst ctx
                                                         `Pair` (Lam $ \_ -> Con (F.Tru))
                                                         `Pair` (Lam $ \_ -> Snd ctx)
                                                         `Pair` Con (F.Entity 0))
  contextDistribution =
    normal 5.75 0.35 ⋆ \h ->
             observe (h ≥ fromRational 4.5) >>
             observe (fromInteger 7 ≥ h) >>
      uniform (fromRational 4.5) (fromRational 7) ⋆ \θ ->
             η (θ `Pair` h)

-- >>> plotData exampleLassGoodExtra
-- ----- goodlass-std-extra-
-- l0...
-- s1...
-- l1...
-- l0x...
-- l0y...
-- l1x...
-- l1y...


-- >>> toMath exampleLassGood
-- l0 = charfun(-7 + y <= 0)*charfun(9/2 - y <= 0)*charfun(-x + y <= 0)*charfun(-7 + x <= 0)*2/5*20/7*(2/5)^(-1)*(20/7)^(-1)*exp(-1/2*(20/7*(23/4 - x))^2)*integrate((min(z, 7) - 9/2)*exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-1)
-- s1 = charfun(-7 + y <= 0)*charfun(9/2 - y <= 0)*charfun(-x + y <= 0)*charfun(-7 + x <= 0)*exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate((min(z, 7) - 9/2)*exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4)*(exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate((min(z, 7) - 9/2)*exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4) + (5/2)^(-4)*exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4))^(-1)
-- l1 = charfun(-7 + y <= 0)*charfun(9/2 - y <= 0)*charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*charfun(-x + y <= 0)*20/7*2/5*(2*%pi)^(-1/2)*exp(-1/2*(20/7*(23/4 - x))^2)^5*integrate((min(z, 7) - 9/2)*exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4)*(exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate((min(z, 7) - 9/2)*exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4) + (5/2)^(-4)*exp(-1/2*(20/7*(23/4 - x))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-4))^(-1)*(20/7*2/5*(2*%pi)^(-1/2)*integrate((z - 9/2)*exp(-1/2*(20/7*(23/4 - z))^2)^5*integrate((min(u, 7) - 9/2)*exp(-1/2*(20/7*(23/4 - u))^2), u, 9/2, 7)^(-4)*(exp(-1/2*(20/7*(23/4 - z))^2)^4*integrate((min(u, 7) - 9/2)*exp(-1/2*(20/7*(23/4 - u))^2), u, 9/2, 7)^(-4) + (5/2)^(-4)*exp(-1/2*(20/7*(23/4 - z))^2)^4*integrate(exp(-1/2*(20/7*(23/4 - u))^2), u, 9/2, 7)^(-4))^(-1), z, 9/2, 7))^(-1)
-- l0 marginalised in X charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*2/5*20/7*(2/5)^(-1)*(20/7)^(-1)*integrate(exp(-1/2*(20/7*(23/4 - y))^2)*integrate((min(z, 7) - 9/2)*exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-1), y, max(x, 9/2), min(7, 7))
-- l0 marginalised in Y charfun(9/2 - x <= 0)*charfun(-7 + x <= 0)*2/5*20/7*(2/5)^(-1)*(20/7)^(-1)*(min(7, min(x, 7)) - 9/2)*exp(-1/2*(20/7*(23/4 - x))^2)*integrate((min(y, 7) - 9/2)*exp(-1/2*(20/7*(23/4 - y))^2), y, 9/2, 7)^(-1)

-- >>> plotData exampleLassGood
-- l0...
-- s1...
-- l1...

-- >>> plotMarginalisedData exampleLassGood
-- l0x...
-- l0y...


asExpression :: Exp (F.R ⟶ F.R ⟶ F.R) -> P (F.Unit × F.R × F.R)
asExpression = simplifyFun2 [] . fromHoas

evaluate :: RSAIn -> RSAOut
evaluate RSAIn{..} = RSAOut {..} where
  α = alpha
  
  -- s1 :: Exp context -> Exp ((F.U ⟶ F.R) ⟶ F.R)
  s1 ctx = utteranceDistribution ⋆ \u ->
              factor ((distr (l0 u) ctx) ^/ α) >>
              η u

  -- | Literal listener
  -- l0 ::  Exp F.U -> Exp ((context ⟶ F.R) ⟶ F.R)
  l0 u = contextDistribution ⋆ \ctx ->
         observe (interpU u ctx) >>
         η ctx

  -- | Pragmatic listener
  -- l1 :: Exp F.U -> Exp ((context ⟶ F.R) ⟶ F.R)
  l1 u = contextDistribution ⋆ \ctx -> 
           factor (s1Distr u ctx) >>
           η ctx

  -- l0Distr :: Exp F.U -> Exp context -> Exp F.R
  l0Distr u ctx = distr (l0 u) ctx

  -- s1Distr :: Exp context -> Exp F.U -> Exp F.R
  s1Distr u ctx = distr (s1 ctx) u

  -- l1Distr :: Exp F.U -> Exp context -> Exp F.R
  l1Distr u ctx = distr (l1 u) ctx

  -- twoDimFunOf :: (Exp utterance -> Exp context -> Exp F.R) -> Exp (F.R ⟶ F.R ⟶ F.R)
  twoDimFunOf f = Lam $ \x -> Lam $ \y ->
     let (h,u) = varsToSituation x y
     in f u h

  utilityl0 :: Exp (F.R ⟶ F.R ⟶ F.R)
  utilityl0 = twoDimFunOf l0Distr

  utilitys1 :: Exp (F.R ⟶ F.R ⟶ F.R)
  utilitys1 = twoDimFunOf s1Distr 

  utilityl1 :: Exp (F.R ⟶ F.R ⟶ F.R)
  utilityl1 = twoDimFunOf l1Distr

  l0Expr = asExpression utilityl0
  l1Expr = asExpression utilityl1
  s1Expr = asExpression utilitys1

  l0Samples = approxTop plotOptions l0Expr
  l1Samples = approxTop plotOptions l1Expr
  s1Samples = approxTop plotOptions s1Expr

  l0xSamples = approxTop plotOptions l0X
  l0ySamples = approxTop plotOptions l0Y
  l1xSamples = approxTop plotOptions l1X
  l1ySamples = approxTop plotOptions l1Y

  PlotOptions{..} = plotOptions

  integrateOnPlotDomain = Integrate (Domain
                    [A.constant (fromRational (toRational plotDomainLo))]
                    [A.constant (fromRational (toRational plotDomainHi))])
  l0X = normalise $ integrateOnPlotDomain l0Expr
  l0Y = normalise $ integrateOnPlotDomain $ swap2P $ l0Expr
  l1X = normalise $ integrateOnPlotDomain l1Expr
  l1Y = normalise $ integrateOnPlotDomain $ swap2P $ l1Expr


  -- P_{S₁}(u)
  s1Prior = utteranceDistribution ⋆ \u ->
            factor ((measure (contextDistribution ⋆ \w -> η (interpU u w))) ^/ α) >>
            η u

  -- P_{L₁}(w)
  l1Prior = contextDistribution ⋆ \w ->
            factor (recip (measure (s1Prior ⋆ \u -> η (interpU u w)))) >>
            η w

  plotData :: IO ()
  plotData = do
    putStrLn $ "----- " ++ prefix
    putStrLn "l0..."  ; toGnuPlot   plotOptions (prefix ++ "l0.2d.dat" ) l0Samples
    putStrLn "s1..."  ; toGnuPlot   plotOptions (prefix ++ "s1.2d.dat" ) s1Samples
    putStrLn "l1..."  ; toGnuPlot   plotOptions (prefix ++ "l1.2d.dat" ) l1Samples
    putStrLn "l0x..." ; toGnuPlot1d plotOptions (prefix ++ "l0x.1d.dat") l0xSamples
    putStrLn "l0y..." ; toGnuPlot1d plotOptions (prefix ++ "l0y.1d.dat") l0ySamples
    putStrLn "l1x..." ; toGnuPlot1d plotOptions (prefix ++ "l1x.1d.dat") l1xSamples
    putStrLn "l1y..." ; toGnuPlot1d plotOptions (prefix ++ "l1y.1d.dat") l1ySamples
    
