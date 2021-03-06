{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Examples.GoodLass  (moreUtterances, saltPaperSetup) where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..), Floating(..))
import Models.Integrals
import Models.Integrals.Types (P(..), Domain(..), swap2P)
import TLC.HOAS
import qualified TLC.Terms as F
import qualified Algebra.Linear.Vector as V
import qualified Algebra.Morphism.Affine as A
import Examples.Utterances

alpha :: Rational
alpha = 4

-- >>> toMath
-- l0 = charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-200/49*(23/4 - x)^2)*integrate(exp(-200/49*(23/4 - z)^2), z, max(9/2, y), 7)^(-1)
-- s1 = charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, max(9/2, y), 7)^(-4)*(exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, max(9/2, y), 7)^(-4) + exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, 9/2, 7)^(-4))^(-1)
-- l1 = charfun(9/2 - y <= 0)*charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-200/49*(23/4 - x)^2)^4*exp(-200/49*(23/4 - x)^2)*integrate(exp(-200/49*(23/4 - z)^2), z, y, 7)^(-4)*(exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, y, 7)^(-4) + exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, 9/2, 7)^(-4))^(-1)*integrate(exp(-200/49*(23/4 - z)^2)^4*exp(-200/49*(23/4 - z)^2)*integrate(integrate(exp(-200/49*(23/4 - v)^2), v, u, 7)^(-4)*(exp(-200/49*(23/4 - z)^2)^4*integrate(exp(-200/49*(23/4 - v)^2), v, u, 7)^(-4) + exp(-200/49*(23/4 - z)^2)^4*integrate(exp(-200/49*(23/4 - v)^2), v, 9/2, 7)^(-4))^(-1), u, 9/2, z), z, 9/2, 7)^(-1)
-- l0 marginalised in X charfun(-7 + x <= 0)*integrate(exp(-200/49*(23/4 - y)^2), y, max(9/2, x), 7)^(-1)*integrate(exp(-200/49*(23/4 - y)^2), y, max(9/2, x), 7)
-- l0 marginalised in Y charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-200/49*(23/4 - x)^2)*integrate(integrate(exp(-200/49*(23/4 - z)^2), z, max(9/2, y), 7)^(-1), y, 9/2, min(7, x))
-- l1 marginalised in X charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*integrate(exp(-200/49*(23/4 - y)^2), y, x, 7)^(-4)*integrate(exp(-200/49*(23/4 - y)^2)^4*exp(-200/49*(23/4 - y)^2)*integrate(integrate(exp(-200/49*(23/4 - u)^2), u, z, 7)^(-4)*(exp(-200/49*(23/4 - y)^2)^4*integrate(exp(-200/49*(23/4 - u)^2), u, z, 7)^(-4) + exp(-200/49*(23/4 - y)^2)^4*integrate(exp(-200/49*(23/4 - u)^2), u, 9/2, 7)^(-4))^(-1), z, 9/2, y), y, 9/2, 7)^(-1)*integrate(exp(-200/49*(23/4 - y)^2)^4*exp(-200/49*(23/4 - y)^2)*(exp(-200/49*(23/4 - y)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, x, 7)^(-4) + exp(-200/49*(23/4 - y)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, 9/2, 7)^(-4))^(-1), y, max(9/2, x), 7)
-- l1 marginalised in Y charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-200/49*(23/4 - x)^2)^4*exp(-200/49*(23/4 - x)^2)*integrate(exp(-200/49*(23/4 - y)^2)^4*exp(-200/49*(23/4 - y)^2)*integrate(integrate(exp(-200/49*(23/4 - u)^2), u, z, 7)^(-4)*(exp(-200/49*(23/4 - y)^2)^4*integrate(exp(-200/49*(23/4 - u)^2), u, z, 7)^(-4) + exp(-200/49*(23/4 - y)^2)^4*integrate(exp(-200/49*(23/4 - u)^2), u, 9/2, 7)^(-4))^(-1), z, 9/2, y), y, 9/2, 7)^(-1)*integrate(integrate(exp(-200/49*(23/4 - z)^2), z, y, 7)^(-4)*(exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, y, 7)^(-4) + exp(-200/49*(23/4 - x)^2)^4*integrate(exp(-200/49*(23/4 - z)^2), z, 9/2, 7)^(-4))^(-1), y, 9/2, min(7, x))

-- >>> plotData
-- ---------- Goodlassl0...
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


-- distribution for ?? 
linguisticParameterDistribution :: Exp (('R ??? 'R) ??? 'R)
linguisticParameterDistribution = uniform (fromRational domLo) (fromRational domHi)

interpU :: Exp 'U -> Exp 'R -> Exp 'R -> Exp 'T
interpU u ?? h = Con (Interp F.Z) @@ u @@ (TT `Pair` (Lam $ \x -> Lam $ \y -> x ??? y)
                                             `Pair` ??
                                             `Pair` (Lam $ \_ -> Con (F.Tru))
                                             `Pair` (Lam $ \_ -> h)
                                             `Pair` Con (F.Entity 0))

-- Distribution over height (w in Good-Lass)
worldDistribution :: Exp (('R ??? 'R) ??? 'R)
worldDistribution = normal 5.75 0.35 ??? \h ->
           observe (h ??? fromRational domLo) >>
           observe (fromRational domHi ??? h) >>
           ?? h

asExpression :: Exp ('R ??? 'R ??? 'R) -> P ('Unit ?? 'R ?? 'R)
asExpression = simplifyFun2 [] . fromHoas

?? :: Rational
?? = alpha

-- | Literal listener (posterior distribution over worlds)
-- l0 ::  Exp 'U -> Exp ((context ??? 'R) ??? 'R)
l0 :: Exp 'R -> Exp 'U -> Exp (('R ??? 'R) ??? 'R)
l0 ?? u = worldDistribution ??? \h ->
         observe (interpU u ?? h) >> -- filter incompatible worlds
         ?? h


-- l0Distr :: Exp 'U -> Exp context -> Exp 'R
l0Distr :: Exp 'U -> Exp ('R ?? 'R) -> Exp 'R
l0Distr u ctx = distr (l0 ?? u) h
  where ?? = Fst ctx
        h = Snd ctx

l0X,l0Y :: P ('Unit ?? 'R)
l0X = integrateOnPlotDomain l0Expr
l0Y = integrateOnPlotDomain $ swap2P $ l0Expr

-- twoDimFunOf :: (Exp utterance -> Exp context -> Exp 'R) -> Exp ('R ??? 'R ??? 'R)
twoDimFunOf :: (Exp 'U -> Exp (a ':?? b1) -> Exp b2) -> Exp (a ':-> (b1 ':-> b2))
twoDimFunOf f = Lam $ \?? -> Lam $ \h -> f isTall (Pair ?? h)

utilityl0 :: Exp ('R ??? 'R ??? 'R)
utilityl0 = twoDimFunOf l0Distr

l0Expr :: P (('Unit ?? 'R) ?? 'R)
l0Expr = asExpression utilityl0

l0Samples :: V.Vec (V.Vec Double)
l0Samples = approxTop plotOptions l0Expr

l0ySamples,l0xSamples :: V.Vec Double
l0xSamples = approxTop plotOptions l0X

l0ySamples = approxTop plotOptions l0Y

integrateOnPlotDomain :: P (?? ?? 'R) -> P ??
integrateOnPlotDomain  = normalise . Integrate (Domain
                  [A.constant (fromRational (toRational plotDomainLo))]
                  [A.constant (fromRational (toRational plotDomainHi))])
 where PlotOptions{..} = plotOptions
                         

asExpression1 :: Exp ('R ??? 'R) -> P ('Unit ?? 'R)
asExpression1 = simplifyFun [] . fromHoas

    
runAll :: String -> Exp (('U ??? 'R) ??? 'R) -> IO ()
runAll prefix utteranceDistribution = do
  -- toMath
  plotData
  where

  -- s1 :: Exp context -> Exp (('U ??? 'R) ??? 'R)
  s1 :: Exp 'R -> Exp 'R -> Exp (('U ??? 'R) ??? 'R)
  s1 ?? h = utteranceDistribution ??? \u ->
           factor ((distr (l0 ?? u) h) ^/ ??) >>
           ?? u
  -- | Pragmatic listener
  -- l1 :: Exp 'U -> Exp ((context ??? 'R) ??? 'R)

  l1 :: Exp 'U -> Exp ((('R ':?? 'R) ??? 'R) ??? 'R)
  l1 u = worldDistribution ??? \h ->
         linguisticParameterDistribution ??? \?? ->
         factor (distr (s1 ?? h) u) >>
         ?? (?? `Pair` h)

  -- s1Distr :: Exp context -> Exp 'U -> Exp 'R
  s1Distr :: Exp 'U -> Exp ('R ':?? 'R) -> Exp 'R
  s1Distr u ctx = distr (s1 (Fst ctx) (Snd ctx)) u

  -- l1Distr :: Exp 'U -> Exp context -> Exp 'R
  l1Distr :: Exp 'U -> Exp ('R ':?? 'R) -> Exp 'R
  l1Distr u ctx = distr (l1 u) ctx

  utilitys1 :: Exp ('R ??? 'R ??? 'R)
  utilitys1 = twoDimFunOf s1Distr 

  utilityl1 :: Exp ('R ??? 'R ??? 'R)
  utilityl1 = twoDimFunOf l1Distr

  l1Expr = asExpression utilityl1
  s1Expr = asExpression utilitys1
  l1Samples = approxTop plotOptions l1Expr
  s1Samples = approxTop plotOptions s1Expr
  
  l1X = integrateOnPlotDomain l1Expr
  l1Y = integrateOnPlotDomain $ swap2P $ l1Expr

  l1xSamples = approxTop plotOptions l1X
  l1ySamples = approxTop plotOptions l1Y

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

  plotData :: IO ()
  plotData = do
    putStr ("---------- " ++ prefix)
    putStrLn "l0..."  ; toGnuPlot   plotOptions (prefix <> "l0.2d.dat") l0Samples
    putStrLn "s1..."  ; toGnuPlot   plotOptions (prefix <> "s1.2d.dat") s1Samples
    putStrLn "l1..."  ; toGnuPlot   plotOptions (prefix <> "l1.2d.dat") l1Samples
    putStrLn "l0x..." ; toGnuPlot1d plotOptions (prefix <> "l0x.1d.dat") l0xSamples
    putStrLn "l0y..." ; toGnuPlot1d plotOptions (prefix <> "l0y.1d.dat") l0ySamples
    putStrLn "l1x..." ; toGnuPlot1d plotOptions (prefix <> "l1x.1d.dat") l1xSamples
    putStrLn "l1y..." ; toGnuPlot1d plotOptions (prefix <> "l1y.1d.dat") l1ySamples
    toGnuPlot1d plotOptions "goodlass-height-prior.1d.dat" $ approxTop plotOptions (asExpression1 (Lam (distr (worldDistribution))))
    toGnuPlot1d plotOptions "goodlass-thres-prior.1d.dat" $ approxTop plotOptions (asExpression1 (Lam (distr (linguisticParameterDistribution))))

saltPaperSetup :: IO ()
saltPaperSetup = runAll "goodlass-" (tallShortOrSilence ??)

moreUtterances :: IO ()
moreUtterances = runAll "goodlass-extra-" (tallOrSilenceOrGiven ??)
