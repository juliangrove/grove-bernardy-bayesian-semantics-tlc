{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Examples.HRSA where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Integrals
import Models.Integrals.Types (P(..),Domain(..),swap2P)
import TLC.Terms (Context0)
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
    l0Expr, l1Expr, s1Expr :: P (('Unit × 'R) × 'R),
    l0X,l0Y :: P ('Unit × 'R),
    l0Samples, l1Samples, s1Samples :: V.Vec (V.Vec Double),
    l0xSamples,l0ySamples :: V.Vec Double,
    plotData, plotMarginalisedData :: IO ()
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
  alpha = 100
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
  varsToSituation x y = (Pair x y,isTall)
  alpha = 4
  uu = Con . General . Utt 
  utteranceDistribution :: Exp (('U ⟶ 'R) ⟶ 'R)
  isTall = uu 1
  utteranceDistribution = Lam $ \k -> k @@ (uu 1) + k @@ (uu 2) + k @@ (uu 3)
  interpU :: Exp 'U -> Exp ('R × 'R) -> Exp 'T
  interpU u ctx = Con (General (Interp F.Z)) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                                         `Pair` Fst ctx
                                                         `Pair` (Lam $ \_ -> Con (F.Logical (F.Tru)))
                                                         `Pair` (Lam $ \_ -> Snd ctx)
                                                         `Pair` Con (Special (F.Entity 0)))
  contextDistribution =
      normal 68 10 ⋆ \h ->
             observe (h ≥ fromInteger 0) >>
             observe (fromInteger 100 ≥ h) >>
      uniform 0 100 ⋆ \θ ->
             η (θ `Pair` h)


exampleLassGood :: RSAOut
exampleLassGood = evaluate RSAIn {..} where
  plotOptions = PlotOptions {..}
  plotDomainLo = 4
  plotDomainHi = 7
  plotResolution = 128
  varsToSituation x y = (Pair x y,isTall)
  alpha = 4
  uu = Con . General . Utt 
  isTall = uu 1
  utteranceDistribution :: Exp (('U ⟶ 'R) ⟶ 'R)
  utteranceDistribution = Lam $ \k -> k @@ (uu 1) + k @@ (uu 2) + k @@ (uu 3)
  interpU :: Exp 'U -> Exp ('R × 'R) -> Exp 'T
  interpU u ctx = Con (General (Interp F.Z)) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ≥ y)
                                                         `Pair` Fst ctx
                                                         `Pair` (Lam $ \_ -> Con (F.Logical (F.Tru)))
                                                         `Pair` (Lam $ \_ -> Snd ctx)
                                                         `Pair` Con (Special (F.Entity 0)))
  contextDistribution =
    normal 5.75 0.6 ⋆ \h ->
             observe (h ≥ fromInteger 0) >>
             observe (fromInteger 100 ≥ h) >>
      uniform 4 7 ⋆ \θ ->
             η (θ `Pair` h)


-- >>> toMath exampleLassGood
-- l0 = charfun(-7 + y <= 0)*charfun(4 - y <= 0)*charfun(-x + y <= 0)*charfun(-100 + x <= 0)*1/3*5/3*(1/3)^(-1)*(5/3)^(-1)*exp(-1/2*(5/3*(23/4 - x))^2)*integrate((min(z, 7) - 4)*exp(-1/2*(5/3*(23/4 - z))^2), z, 4, 100)^(-1)
-- s1 = charfun(-7 + y <= 0)*charfun(4 - y <= 0)*charfun(-x + y <= 0)*charfun(-100 + x <= 0)*exp(-1/2*(5/3*(23/4 - x))^2)^4*integrate((min(z, 7) - 4)*exp(-1/2*(5/3*(23/4 - z))^2), z, 4, 100)^(-4)*(exp(-1/2*(5/3*(23/4 - x))^2)^4*integrate((min(z, 7) - 4)*exp(-1/2*(5/3*(23/4 - z))^2), z, 4, 100)^(-4) + 3^(-4)*exp(-1/2*(5/3*(23/4 - x))^2)^4*integrate(exp(-1/2*(5/3*(23/4 - z))^2), z, 0, 100)^(-4))^(-1)
-- l1 = charfun(-7 + y <= 0)*charfun(4 - y <= 0)*charfun(-100 + x <= 0)*charfun(-x <= 0)*charfun(-x + y <= 0)*5/3*1/3*(2*%pi)^(-1/2)*exp(-1/2*(5/3*(23/4 - x))^2)^5*integrate((min(z, 7) - 4)*exp(-1/2*(5/3*(23/4 - z))^2), z, 4, 100)^(-4)*(exp(-1/2*(5/3*(23/4 - x))^2)^4*integrate((min(z, 7) - 4)*exp(-1/2*(5/3*(23/4 - z))^2), z, 4, 100)^(-4) + 3^(-4)*exp(-1/2*(5/3*(23/4 - x))^2)^4*integrate(exp(-1/2*(5/3*(23/4 - z))^2), z, 0, 100)^(-4))^(-1)*(5/3*1/3*(2*%pi)^(-1/2)*integrate((min(z, 7) - 4)^(-1)*exp(-1/2*(5/3*(23/4 - z))^2)^5*integrate((min(u, 7) - 4)*exp(-1/2*(5/3*(23/4 - u))^2), u, 4, 100)^(-4)*(exp(-1/2*(5/3*(23/4 - z))^2)^4*integrate((min(u, 7) - 4)*exp(-1/2*(5/3*(23/4 - u))^2), u, 4, 100)^(-4) + 3^(-4)*exp(-1/2*(5/3*(23/4 - z))^2)^4*integrate(exp(-1/2*(5/3*(23/4 - u))^2), u, 0, 100)^(-4))^(-1), z, 4, 100))^(-1)
-- l0 marginalised in X charfun(-100 + x <= 0)*charfun(-7 + x <= 0)*charfun(4 - x <= 0)*1/3*5/3*(1/3)^(-1)*(5/3)^(-1)*integrate(exp(-1/2*(5/3*(23/4 - y))^2)*integrate((min(z, 7) - 4)*exp(-1/2*(5/3*(23/4 - z))^2), z, 4, 100)^(-1), y, max(x, 4), min(100, 7))

-- >>> plotData exampleLassGood
-- l0...
-- s1...
-- l1...

-- >>> plotMarginalisedData exampleLassGood
-- l0x...
-- l0y...


example1 :: RSAOut
example1 = evaluate $ RSAIn {..} where
    varsToSituation y x = (heightToCtx x, toAtLeastHeight y)
    plotOptions = PlotOptions {..}
    plotDomainLo = 0
    plotDomainHi = 100
    plotResolution = 128
    alpha = 4
    utteranceDistribution = uniform 0 100 ⋆ (\x -> η (u' x)) 
    heightToCtx :: Exp 'R -> Exp Context0
    heightToCtx h = (Pair
                        (Pair
                         (Pair
                          (Pair
                           (Pair TT (toHoas (F.≥)))
                           zero)
                          (toHoas F.human))
                         (Lam (\_ -> h)))
                        (toHoas F.vlad))

    toAtLeastHeight :: Exp 'R -> Exp 'U
    toAtLeastHeight r = Con (General Utt') @@ r
    interpU = \u ctx -> Con (General (Interp F.Z)) @@ u @@ ctx
    contextDistribution =
        uniform 0 1 ⋆ \θ ->
        normal 68 3 ⋆ \h ->
               (observe (h ≥ fromInteger 00) >>
               (observe (fromInteger 100 ≥ h) >>
                 (η (Pair
                     (Pair
                      (Pair
                       (Pair
                        (Pair TT (toHoas (F.≥)))
                        θ)
                       (toHoas F.human))
                      (Lam $ \_ -> h))
                     (toHoas F.vlad)))))

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
    

  plotData :: IO ()
  plotData = do
    putStrLn "l0..." ; toGnuPlot plotOptions "l0.dat" l0Samples
    putStrLn "s1..." ; toGnuPlot plotOptions "s1.dat" s1Samples
    putStrLn "l1..." ; toGnuPlot plotOptions "l1.dat" l1Samples

  plotMarginalisedData = do
    putStrLn "l0x..." ; toGnuPlot1d plotOptions "l0x.dat" l0xSamples
    putStrLn "l0y..." ; toGnuPlot1d plotOptions "l0y.dat" l0ySamples
    
