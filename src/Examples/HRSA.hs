{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Examples.HRSA where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Integrals
import TLC.Terms (Context0)
import TLC.HOAS
import qualified TLC.Terms as F
import qualified Algebra.Linear.Vector as V


data RSAIn = forall context utterance. (Equality context, Equality utterance) => RSAIn {
    alpha :: Rational,
    contextDistribution    :: Exp ((context ⟶ 'R) ⟶ 'R),
    utteranceDistribution  ::  Exp ((utterance ⟶ 'R) ⟶ 'R),
    realToCtx :: Exp 'R -> Exp context,
    realToU ::  Exp 'R -> Exp utterance,
    interpU :: Exp utterance -> Exp context -> Exp 'T,
    plotOptions :: PlotOptions
  }

data RSAOut = RSAOut {
    l0Expr, l1Expr, s1Expr :: P (('Unit × 'R) × 'R),
    l0Samples, l1Samples, s1Samples :: V.Vec (V.Vec Double),
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

-- >>> toMath exampleCookies
-- l0 = charfun(-x + y <= 0)*charfun(-40 + x <= 0)*charfun(-x <= 0)*exp(-1/2*(1/5*(10 - x))^2)*integrate(exp(-1/2*(1/5*(10 - z))^2), z, max(y, 0), 40)^(-1)
-- s1 = charfun(-y <= 0)*charfun(-40 + y <= 0)*charfun(-x + y <= 0)*charfun(-40 + x <= 0)*integrate(integrate(exp(-1/2*(1/5*(10 - u))^2), u, z, 40)^(-4), z, 0, x)^(-1)*integrate(exp(-1/2*(1/5*(10 - z))^2), z, y, 40)^(-4)
-- l1 = charfun(-y <= 0)*charfun(-40 + y <= 0)*charfun(-x + y <= 0)*charfun(-40 + x <= 0)*exp(-1/2*(1/5*(10 - x))^2)*integrate(exp(-1/2*(1/5*(10 - z))^2)*integrate(integrate(exp(-1/2*(1/5*(10 - v))^2), v, u, 40)^(-4), u, 0, z)^(-1)*integrate(exp(-1/2*(1/5*(10 - u))^2), u, y, 40)^(-4), z, y, 40)^(-1)*integrate(integrate(exp(-1/2*(1/5*(10 - u))^2), u, z, 40)^(-4), z, 0, x)^(-1)*integrate(exp(-1/2*(1/5*(10 - z))^2), z, y, 40)^(-4)

-- >>> plotData exampleCookies
-- l0...
-- s1...
-- l1...

exampleCookies :: RSAOut
exampleCookies = evaluate RSAIn {..} where
  realToCtx = id
  realToU = id
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

example1 :: RSAOut
example1 = evaluate $ RSAIn {realToCtx=heightToCtx,realToU=toAtLeastHeight,..} where
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

asExpression :: Exp ('R ⟶ ('R ⟶ 'R)) -> P (('Unit × 'R) × 'R)
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
           factor (s1Distr ctx u) >>
           η ctx

  -- l0Distr :: Exp 'U -> Exp context -> Exp 'R
  l0Distr u ctx = distr (l0 u) ctx

  -- s1Distr :: Exp context -> Exp 'U -> Exp 'R
  s1Distr ctx u = distr (s1 ctx) u

  -- l1Distr :: Exp 'U -> Exp context -> Exp 'R
  l1Distr u ctx = distr (l1 u) ctx

  utilityl0 :: Exp ('R ⟶ 'R ⟶ 'R)
  utilityl0 = Lam $ \h -> Lam $ \u -> l0Distr (realToU h) (realToCtx u)

  utilitys1 :: Exp ('R ⟶ 'R ⟶ 'R)
  utilitys1 = Lam $ \h -> Lam $ \u -> s1Distr (realToCtx u) (realToU h) 

  utilityl1 :: Exp ('R ⟶ 'R ⟶ 'R)
  utilityl1 = Lam $ \h -> Lam $ \u -> l1Distr (realToU h) (realToCtx u)

  l0Expr = asExpression utilityl0
  l1Expr = asExpression utilityl1
  s1Expr = asExpression utilitys1

  l0Samples = approxTop plotOptions l0Expr
  l1Samples = approxTop plotOptions l1Expr
  s1Samples = approxTop plotOptions s1Expr

  plotData :: IO ()
  plotData = do
    putStrLn "l0..." ; toGnuPlot plotOptions "l0.dat" l0Samples
    putStrLn "s1..." ; toGnuPlot plotOptions "s1.dat" s1Samples
    putStrLn "l1..." ; toGnuPlot plotOptions "l1.dat" l1Samples

