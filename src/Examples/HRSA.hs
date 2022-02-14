{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Examples.HRSA where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Integrals
import TLC.Terms (Context0)
import TLC.HOAS
import qualified TLC.Terms as F
import qualified Algebra.Linear.Vector as V

-- ∃γ. ∃u. (... × .. Exp ((γ ⟶ 'R) ⟶ 'R))
data RSAIn = forall context utterance. (Equality context, Equality utterance) => RSAIn {
    alpha :: Rational,
    contextDistribution    :: Exp ((context ⟶ 'R) ⟶ 'R),
    utteranceDistribution  :: Exp ((utterance ⟶ 'R) ⟶ 'R),
    interpU :: Exp utterance -> Exp context -> Exp 'T,

    -- realToCtx :: Exp 'R -> Exp context,
    -- realToU ::  Exp 'R -> Exp utterance,
    varsToSituation :: Exp 'R -> Exp 'R -> (Exp context, Exp utterance),
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
  utteranceDistribution :: Exp ((('R ⟶ 'R ⟶ 'T) ⟶ 'R) ⟶ 'R)
  isTall = (Lam $ \θ -> Lam $ \ h -> h ≥ θ)
  utteranceDistribution = Lam $ \k -> k @@ (Lam $ \θ -> Lam $ \ h -> θ ≥ h)
                                + k @@ isTall
                                + k @@ (Lam $ \θ -> Lam $ \ h -> Con $ Logical F.Tru)
  interpU :: Exp ('R ⟶ 'R ⟶ 'T) -> Exp ('R × 'R) -> Exp 'T
  interpU u ctx = u @@ Fst ctx @@ Snd ctx
  contextDistribution =
      normal 68 3 ⋆ \h ->
      uniform 0 100 ⋆ \θ ->
             -- observe (nCookies ≥ fromInteger 0) >>
             -- observe (fromInteger 40 ≥ nCookies) >>
             η (θ `Pair` h)

-- >>> toMath exampleTallThreshold
-- l0 = charfun(-100 + y <= 0)*charfun(-y <= 0)*charfun(-x + y <= 0)*1/100*1/3*(1/100)^(-1)*(1/3)^(-1)*exp(-1/2*(1/3*(68 - x))^2)*integrate(min(z, 100)*exp(-1/2*(1/3*(68 - z))^2), z, 0, inf)^(-1)
-- s1 = *** Exception: src/TLC/Terms.hs:104:3-56: Non-exhaustive patterns in function equals


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

  plotData :: IO ()
  plotData = do
    putStrLn "l0..." ; toGnuPlot plotOptions "l0.dat" l0Samples
    putStrLn "s1..." ; toGnuPlot plotOptions "s1.dat" s1Samples
    putStrLn "l1..." ; toGnuPlot plotOptions "l1.dat" l1Samples

