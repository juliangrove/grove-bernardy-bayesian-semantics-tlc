{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Examples.GoodLassStd where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..), Floating(..))
import Models.Integrals
import Models.Integrals.Types (P(..), Domain(..), swap2P)
import TLC.HOAS
import qualified TLC.Terms as F
import qualified Algebra.Morphism.Affine as A
import qualified Algebra.Linear.Vector as V
import Examples.Utterances


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


-- >>> toMath
-- l0 = charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(-x <= 0)*exp(-1/2*(4 - x)^2)*integrate(exp(-1/2*(4 - z)^2), z, max(0, y), 7)^(-1)
-- s1 = charfun(-y <= 0)*charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(-x <= 0)*exp(-1/2*(4 - x)^2)^(-4)*exp(-1/2*(4 - x)^2)^4*integrate(integrate(exp(-1/2*(4 - u)^2), u, z, 7)^(-4), z, 0, x)^(-1)*integrate(exp(-1/2*(4 - z)^2), z, y, 7)^(-4)
-- l1 = charfun(-y <= 0)*charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(-x <= 0)*exp(-1/2*(4 - x)^2)^(-4)*exp(-1/2*(4 - x)^2)^4*exp(-1/2*(4 - x)^2)*integrate(integrate(exp(-1/2*(4 - u)^2), u, z, 7)^(-4), z, 0, x)^(-1)*integrate(exp(-1/2*(4 - z)^2), z, y, 7)^(-4)*integrate(exp(-1/2*(4 - z)^2), z, y, 7)^4*integrate(exp(-1/2*(4 - z)^2)^(-4)*exp(-1/2*(4 - z)^2)^4*exp(-1/2*(4 - z)^2)*integrate(integrate(exp(-1/2*(4 - v)^2), v, u, 7)^(-4), u, 0, z)^(-1), z, y, 7)^(-1)
-- l0 marginalised in X charfun(-7 + x <= 0)*integrate(exp(-1/2*(4 - y)^2), y, max(0, x), 7)^(-1)*integrate(exp(-1/2*(4 - y)^2), y, max(0, x), 7)
-- l0 marginalised in Y charfun(-7 + x <= 0)*charfun(-x <= 0)*exp(-1/2*(4 - x)^2)*integrate(integrate(exp(-1/2*(4 - z)^2), z, max(0, y), 7)^(-1), y, 0, min(7, x))


plotOptions :: PlotOptions
plotOptions = PlotOptions {
  plotDomainLo=domLo,
  plotDomainHi=domHi,..}
  where plotResolution = 128
alpha :: Rational
alpha = 4

prefix = ("cookies-continuous-" ++ show (fromRational alpha :: Double) ++ "-")
varsToSituation y x = (x,y)
domLo = 30
domHi = 37
plotResolution = 128
utteranceDistribution = uniform lo hi
interpU u nCookies = nCookies ≥ u
lo, hi :: forall a. Field a => a
lo = fromRational (toRational domLo)
hi = fromRational (toRational domHi)
contextDistribution =
    normal 4 1 ⋆ \nCookies ->
           observe (nCookies ≥ lo) >>
           observe (hi ≥ nCookies) >>
           η nCookies

cost :: Double -> Exp F.R
cost x = Con (F.Incl (toRational (exp (- x) :: Double))) 
  
asExpression :: Exp (F.R ⟶ F.R ⟶ F.R) -> P ('Unit × F.R × F.R)
asExpression = simplifyFun2 [] . fromHoas

asExpression1 :: (Exp F.R -> Exp F.R) -> P ('Unit × F.R)
asExpression1 = simplifyFun [] . fromHoas . Lam

α :: Rational
α = alpha

-- s1 :: Exp context -> Exp (('U ⟶ F.R) ⟶ F.R)
s1 ctx = utteranceDistribution ⋆ \u ->
            factor ((distr (l0 u) ctx) ^/ α) >>
            η u

-- | Literal listener
-- l0 ::  Exp 'U -> Exp ((context ⟶ F.R) ⟶ F.R)
l0 u = contextDistribution ⋆ \ctx ->
       observe (interpU u ctx) >>
       η ctx

-- | Pragmatic listener
-- l1 :: Exp 'U -> Exp ((context ⟶ F.R) ⟶ F.R)
l1 u = contextDistribution ⋆ \ctx -> 
         factor (s1Distr u ctx) >>
         η ctx

-- l0Distr :: Exp 'U -> Exp context -> Exp F.R
l0Distr u ctx = distr (l0 u) ctx

-- s1Distr :: Exp context -> Exp 'U -> Exp F.R
s1Distr u ctx = distr (s1 ctx) u

-- l1Distr :: Exp 'U -> Exp context -> Exp F.R
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


integrateOnPlotDomain = Integrate (Domain
                  [A.constant (fromRational (toRational domLo))]
                  [A.constant (fromRational (toRational domHi))])
l0X = normalise $ integrateOnPlotDomain l0Expr
l0Y = normalise $ integrateOnPlotDomain $ swap2P $ l0Expr
l1X = normalise $ integrateOnPlotDomain l1Expr
l1Y = normalise $ integrateOnPlotDomain $ swap2P $ l1Expr

measureTrue :: PP F.T -> Exp F.R
measureTrue p = (p @@ (Lam (\x -> (Con Indi @@ x))))

-- P_{S₁}(u)
s1Prior :: PP F.R
s1Prior = utteranceDistribution ⋆ \u ->
          factor (recip (measureTrue ((contextDistribution ⋆ \w -> η (interpU u w))) ^/ α)) >>
          η u

s1PriorExpr :: P ('Unit × F.R)
s1PriorExpr = asExpression1 $ {-log .  .  . -}  distr s1Prior
s1PriorSamples :: V.Vec Double
s1PriorSamples = approxTop plotOptions s1PriorExpr

-- >>> maxima s1PriorExpr
-- charfun(-7 + x <= 0)*charfun(-x <= 0)*integrate(integrate(exp(-1/2*(4 - z)^2), z, y, 7)^(-4), y, 0, 7)^(-1)*integrate(exp(-1/2*(4 - y)^2), y, x, 7)^(-4)

-- P_{L₁}(w)
l1Prior :: PP F.R
l1Prior = contextDistribution ⋆ \w ->
          factor (recip (measureTrue (s1Prior ⋆ \u -> η (interpU u w)))) >>
          η w

l1PriorExpr :: P ('Unit × F.R)
l1PriorExpr = asExpression1 $ \x -> {-log-}(distr l1Prior x)
l1PriorSamples :: V.Vec Double
l1PriorSamples = approxTop plotOptions l1PriorExpr

-- >>> maxima l1PriorExpr
-- charfun(50 - x <= 0)*charfun(-57 + x <= 0)*exp(-(-4 + x)^2)*integrate(integrate(exp(-(-4 + z)^2), z, y, 57)^(-4), y, 50, x)^(-1)*integrate(exp(-(-4 + y)^2)*integrate(integrate(exp(-(-4 + u)^2), u, z, 57)^(-4), z, 50, y)^(-1), y, 50, 57)^(-1)

plotData :: IO ()
plotData = do
  putStrLn $ "----- " ++ prefix
  putStrLn "l0..."  ; toGnuPlot   plotOptions (prefix ++ "l0.2d.dat" ) l0Samples
  putStrLn "s1..."  ; toGnuPlot1d plotOptions (prefix ++ "s1.1d.dat" ) s1PriorSamples
  putStrLn "s1..."  ; toGnuPlot   plotOptions (prefix ++ "s1.2d.dat" ) s1Samples
  putStrLn "l1..."  ; toGnuPlot   plotOptions (prefix ++ "l1.2d.dat" ) l1Samples
  putStrLn "l1..."  ; toGnuPlot1d plotOptions (prefix ++ "l1.1d.dat" ) l1PriorSamples
  putStrLn "l0x..." ; toGnuPlot1d plotOptions (prefix ++ "l0x.1d.dat") l0xSamples
  putStrLn "l0y..." ; toGnuPlot1d plotOptions (prefix ++ "l0y.1d.dat") l0ySamples
  putStrLn "l1x..." ; toGnuPlot1d plotOptions (prefix ++ "l1x.1d.dat") l1xSamples
  putStrLn "l1y..." ; toGnuPlot1d plotOptions (prefix ++ "l1y.1d.dat") l1ySamples

-- >>> plotData
-- ----- cookies-continuous-4.0-
-- l0...
-- s1...
-- s1...
-- l1...
-- l1...
-- l0x...
-- l0y...
-- l1x...
-- l1y...
