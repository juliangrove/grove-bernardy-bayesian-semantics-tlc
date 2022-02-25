{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Examples.HRSA where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Integrals
import Models.Integrals.Types (P(..),Domain(..),swap2P)
import TLC.HOAS
import qualified TLC.Terms as F
import qualified Algebra.Linear.Vector as V
import qualified Algebra.Morphism.Affine as A

-- ∃γ. ∃u. (... × .. Exp ((γ ⟶ 'R) ⟶ 'R))
data RSAIn = forall context utterance. (Equality context, Equality utterance) => RSAIn {
    alpha :: Rational,
    contextDistribution    :: Exp ((context ⟶ 'R) ⟶ 'R),
    utteranceDistribution  :: Exp ((utterance ⟶ 'R) ⟶ 'R),
    interpU :: Exp utterance -> Exp context -> Exp 'T,

    varsToSituation :: Exp 'R -> Exp 'R -> (Exp context, Exp utterance),
    plotOptions :: PlotOptions
  }

data RSAOut = RSAOut {
    l0Expr, l1Expr, s1Expr :: P ('Unit × 'R × 'R),
    l0X,l0Y :: P ('Unit × 'R),
    l0Samples, l1Samples, s1Samples :: V.Vec (V.Vec Double),
    l0xSamples,l0ySamples :: V.Vec Double,
    plotData :: String -> IO ()
    }

isTall :: Exp 'U
isTall = Con $ Utt $ F.MergeRgt F.Vl F.IsTall
isShort :: Exp 'U
isShort = Con $ Utt $ F.MergeRgt F.Vl F.IsShort
vaccuous :: Exp 'U
vaccuous = Con $ Silence

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

-- >>> toMath exampleCookies
-- l0 = charfun(-40 + y <= 0)*charfun(-y <= 0)*charfun(x - y <= 0)*exp(-1/2*(1/5*(40 - y))^2)*integrate(exp(-1/2*(1/5*(40 - z))^2), z, max(x, 0), 40)^(-1)
-- s1 = charfun(-40 + y <= 0)*charfun(-x <= 0)*charfun(-40 + x <= 0)*charfun(x - y <= 0)*integrate(integrate(exp(-1/2*(1/5*(40 - u))^2), u, z, 40)^(-4), z, 0, y)^(-1)*integrate(exp(-1/2*(1/5*(40 - z))^2), z, x, 40)^(-4)
-- l1 = charfun(-40 + y <= 0)*charfun(-x <= 0)*charfun(-40 + x <= 0)*charfun(x - y <= 0)*exp(-1/2*(1/5*(40 - y))^2)*integrate(exp(-1/2*(1/5*(40 - z))^2)*integrate(integrate(exp(-1/2*(1/5*(40 - v))^2), v, u, 40)^(-4), u, 0, z)^(-1)*integrate(exp(-1/2*(1/5*(40 - u))^2), u, x, 40)^(-4), z, x, 40)^(-1)*integrate(integrate(exp(-1/2*(1/5*(40 - u))^2), u, z, 40)^(-4), z, 0, y)^(-1)*integrate(exp(-1/2*(1/5*(40 - z))^2), z, x, 40)^(-4)

-- >>> plotData exampleCookies
-- l0...
-- s1...
-- l1...

exampleCookies :: RSAOut
exampleCookies = evaluate RSAIn {..} where
  varsToSituation y x = (x,y)
  plotOptions = PlotOptions {..}
  plotDomainLo = 0
  plotDomainHi = 40
  plotResolution = 128
  alpha = 4
  utteranceDistribution = uniform 0 40
  interpU u nCookies = nCookies ≥ u
  contextDistribution =
      normal 40 5 ⋆ \nCookies ->
             observe (nCookies ≥ fromInteger 0) >>
             observe (fromInteger 40 ≥ nCookies) >>
             η nCookies

exampleTallThreshold :: RSAOut
exampleTallThreshold = evaluate RSAIn {..} where
  plotOptions = PlotOptions {..}
  plotDomainLo = 0
  plotDomainHi = 100
  plotResolution = 128
  varsToSituation x y = (Pair x y, isTall)
  alpha = 4
  utteranceDistribution :: Exp (('U ⟶ 'R) ⟶ 'R)
  utteranceDistribution = Lam $ \k -> k @@ isTall + k @@ isShort + k @@ vaccuous
  interpU :: Exp 'U -> Exp ('R × 'R) -> Exp 'T
  interpU u ctx = Con (Interp F.Z) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                               `Pair` Fst ctx
                                               `Pair` (Lam $ \_ -> Con (F.Tru))
                                               `Pair` (Lam $ \_ -> Snd ctx)
                                               `Pair` Con (F.Entity 0))
  contextDistribution =
      normal 68 10 ⋆ \h ->
             observe (h ≥ fromInteger 0) >>
             observe (fromInteger 100 ≥ h) >>
      uniform 0 100 ⋆ \θ ->
             η (θ `Pair` h)

exampleLassGood :: RSAOut
exampleLassGood = evaluate RSAIn {..} where
  plotOptions = PlotOptions {..}
  plotDomainLo = 4.5
  plotDomainHi = 7
  plotResolution = 128
  varsToSituation x y = (Pair x y,isTall)
  alpha = 4
  utteranceDistribution :: Exp (('U ⟶ 'R) ⟶ 'R)
  utteranceDistribution = Lam $ \k -> k @@ isTall + k @@ isShort + k @@ vaccuous
  interpU :: Exp 'U -> Exp ('R × 'R) -> Exp 'T
  interpU u ctx = Con (Interp F.Z) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                                         `Pair` Fst ctx
                                                         `Pair` (Lam $ \_ -> Con (F.Tru))
                                                         `Pair` (Lam $ \_ -> Snd ctx)
                                                         `Pair` Con (F.Entity 0))
  contextDistribution =
    normal 5.75 0.35 ⋆ \h ->
             observe (h ≥ fromRational 4.5) >>
             observe (fromInteger 7 ≥ h) >>
      uniform 4.5 7 ⋆ \θ ->
             η (θ `Pair` h)


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


asExpression :: Exp ('R ⟶ 'R ⟶ 'R) -> P ('Unit × 'R × 'R)
asExpression = simplifyFun2 [] . fromHoas

evaluate :: RSAIn -> RSAOut
evaluate RSAIn{..} = RSAOut {..} where
  α = alpha
  
  -- s1 :: Exp context -> Exp (('U ⟶ 'R) ⟶ 'R)
  s1 ctx = utteranceDistribution ⋆ \u ->
              factor ((distr (l0 u) ctx) ^/ α) >>
              η u

  -- | Literal listener
  -- l0 ::  Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)
  l0 u = contextDistribution ⋆ \ctx ->
         observe (interpU u ctx) >>
         η ctx

  -- | Pragmatic listener
  -- l1 :: Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)
  l1 u = contextDistribution ⋆ \ctx -> 
           factor (s1Distr u ctx) >>
           η ctx

  -- l0Distr :: Exp 'U -> Exp context -> Exp 'R
  l0Distr u ctx = distr (l0 u) ctx

  -- s1Distr :: Exp context -> Exp 'U -> Exp 'R
  s1Distr u ctx = distr (s1 ctx) u

  -- l1Distr :: Exp 'U -> Exp context -> Exp 'R
  l1Distr u ctx = distr (l1 u) ctx

  -- twoDimFunOf :: (Exp utterance -> Exp context -> Exp 'R) -> Exp ('R ⟶ 'R ⟶ 'R)
  twoDimFunOf f = Lam $ \x -> Lam $ \y ->
     let (h,u) = varsToSituation x y
     in f u h

  utilityl0 :: Exp ('R ⟶ 'R ⟶ 'R)
  utilityl0 = twoDimFunOf l0Distr

  utilitys1 :: Exp ('R ⟶ 'R ⟶ 'R)
  utilitys1 = twoDimFunOf s1Distr 

  utilityl1 :: Exp ('R ⟶ 'R ⟶ 'R)
  utilityl1 = twoDimFunOf l1Distr

  l0Expr = asExpression utilityl0
  l1Expr = asExpression utilityl1
  s1Expr = asExpression utilitys1

  l0Samples = approxTop plotOptions l0Expr
  l1Samples = approxTop plotOptions l1Expr
  s1Samples = approxTop plotOptions s1Expr

  l0xSamples = approxTop plotOptions l0X
  l0ySamples = approxTop plotOptions l0Y

  PlotOptions{..} = plotOptions

  integrateOnPlotDomain = Integrate (Domain
                    [A.constant (fromRational (toRational plotDomainLo))]
                    [A.constant (fromRational (toRational plotDomainHi))])
  l0X = normalise $
        integrateOnPlotDomain
        l0Expr

  l0Y = normalise $
        integrateOnPlotDomain $
        swap2P $
        l0Expr
    

  plotData :: String -> IO ()
  plotData prefix = do
    putStrLn $ "----- " ++ prefix
    putStrLn "l0..."  ; toGnuPlot   plotOptions (prefix ++ "l0.2d.dat" ) l0Samples
    putStrLn "s1..."  ; toGnuPlot   plotOptions (prefix ++ "s1.2d.dat" ) s1Samples
    putStrLn "l1..."  ; toGnuPlot   plotOptions (prefix ++ "l1.2d.dat" ) l1Samples
    putStrLn "l0x..." ; toGnuPlot1d plotOptions (prefix ++ "l0x.1d.dat") l0xSamples
    putStrLn "l0y..." ; toGnuPlot1d plotOptions (prefix ++ "l0y.1d.dat") l0ySamples
    
