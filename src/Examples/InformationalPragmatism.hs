{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Examples.InformationalPragmatism where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..), (^))
import Models.Integrals
import Models.Integrals.Types (P(..),Domain(..),swap2P)
import TLC.HOAS
import qualified TLC.Terms as F
import qualified Algebra.Linear.Vector as V

toMath :: IO ()
toMath = do
  putStr "l0 = "
  maxima $ l0Expr
  putStr "l1 = "
  maxima $ l1Expr

-- >>> toMath
-- l0 = charfun(-7 + y <= 0)*charfun(9/2 - y <= 0)*charfun(x - y <= 0)*exp(-1/2*(20/7*(23/4 - y))^2)*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, max(9/2, x), 7)^(-1)
-- l1 = *** Exception: evalP': don't know how to handle: *** Exception: src/TLC/Terms.hs:(308,3)-(350,32): Non-exhaustive patterns in function show

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


linguisticParameterDistribution :: Exp (('R ⟶ 'R) ⟶ 'R)
linguisticParameterDistribution = uniform domLo domHi

interpU :: Exp 'R -> Exp 'R -> Exp 'T
interpU θ h = h ≥ θ

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

asExpression1 :: Exp ('R ⟶ 'R) -> P ('Unit × 'R)
asExpression1 = simplifyFun [] . fromHoas

-- asExpression :: Exp (('R ⟶ 'R) ⟶ 'R) -> P ('Unit × 'R)
-- asExpression = asExpression' . Lam . distr

-- asExpression' :: Exp ('R ⟶ 'R) -> P ('Unit × 'R)
-- asExpression' = simplifyFun [] . fromHoas

α :: Rational
α = alpha

-- | Literal listener
-- l0 ::  Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)
l0 :: Exp 'R -> Exp (('R ⟶ 'R) ⟶ 'R)
l0 θ = worldDistribution `marginBy` (observe . (interpU θ))

-- | Pragmatic listener
-- l1 :: Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)

type Θ = 'R
type W = 'R

infoGain :: Exp ((W ⟶ 'R) ⟶ 'R) -> Exp ((W ⟶ 'R) ⟶ 'R) -> Exp 'R
infoGain p q = average (p ⋆ \w -> factor (Con Log @@ ((dp w) / (dq w) )) >> η w)
  where dp = distr p
        dq = distr q

(∘) :: Exp (a1 ⟶ b) -> Exp (a2 ⟶ a1) -> Exp (a2 ⟶ b)
f ∘ g = Lam $ \x -> f @@ (g @@ x)

expectedBits :: Exp 'R -> Exp 'R
expectedBits x = Con Exp @@ (negate x ^ fromInteger 2)

marginBy :: Exp ((β ⟶ r) ⟶ r) -> (Exp β -> Exp (('Unit ⟶ r) ⟶ r)) -> Exp ((β ⟶ r) ⟶ r)
p `marginBy` f = p ⋆ \x -> f x >> η x

l1 :: Exp ((Θ ⟶ 'R) ⟶ 'R)
l1 = linguisticParameterDistribution ⋆ \θ -> 
         factor (expectedBits (infoGain (l0 θ)
                               worldDistribution)) >>
         η θ

l0Expr :: P (('Unit × 'R) × 'R)
l0Expr = asExpression (Lam $ \h -> Lam $ \θ -> distr (l0 θ) h)

l1Expr :: P ('Unit × 'R)
l1Expr = asExpression1 (Lam $ \θ -> distr l1 θ)

l0Samples :: V.Vec (V.Vec Double)
l0Samples = approxTop plotOptions l0Expr

l1xSamples :: V.Vec Double
l1xSamples = approxTop plotOptions l1Expr


plotData :: IO ()
plotData = do
  putStrLn "l0..."
  toGnuPlot plotOptions "l0.dat" l0Samples
  putStrLn "l1x..."
  toGnuPlot1d plotOptions "l1x.dat" l1xSamples
    
