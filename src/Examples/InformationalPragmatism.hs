{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeOperators #-}

module Examples.InformationalPragmatism where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..), (^))
import Models.Integrals
-- import Models.Integrals.Types (P(..), Domain(..), swap2P)
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
-- l0 = charfun(-x + y <= 0)*charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*exp(-1/2*(20/7*(23/4 - x))^2)*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, max(9/2, y), 7)^(-1)
-- l1 = charfun(-7 + x <= 0)*charfun(9/2 - x <= 0)*integrate(exp(-1/2*(20/7*(23/4 - y))^2)*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-1), y, x, 7)^7*(1 - integrate(exp(-1/2*(20/7*(23/4 - y))^2)*integrate(exp(-1/2*(20/7*(23/4 - z))^2), z, 9/2, 7)^(-1), y, x, 7))*integrate(integrate(exp(-1/2*(20/7*(23/4 - z))^2)*integrate(exp(-1/2*(20/7*(23/4 - u))^2), u, 9/2, 7)^(-1), z, y, 7)^7*(1 - integrate(exp(-1/2*(20/7*(23/4 - z))^2)*integrate(exp(-1/2*(20/7*(23/4 - u))^2), u, 9/2, 7)^(-1), z, y, 7)), y, 9/2, 7)^(-1)


-- >>> plotData
-- l0...
-- l1x...


domHi :: Rational
domHi = 7

domLo :: Rational
domLo = 4.5

plotOptions :: PlotOptions
plotOptions = PlotOptions {..} where
   plotDomainLo = fromRational domLo
   plotDomainHi = fromRational domHi
   plotResolution = 128

isTall :: Exp 'U
isTall = Con $ Utt $ F.MergeRgt F.Vl F.IsTall

varsToSituation :: Exp a -> Exp b -> (Exp (a ':× b), Exp 'U)
varsToSituation x y = (Pair x y,isTall)

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

-- | Literal listener
-- l0 ::  Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)
l0 :: Exp 'R -> Exp (('R ⟶ 'R) ⟶ 'R)
l0 θ = worldDistribution `marginBy'` (observe . interpU θ)

-- | Pragmatic listener
-- l1 :: Exp 'U -> Exp ((context ⟶ 'R) ⟶ 'R)

type Θ = 'R
type W = 'R

-- -- information gain from q to p.
-- infoGain :: Exp ((W ⟶ 'R) ⟶ 'R) -> Exp ((W ⟶ 'R) ⟶ 'R) -> Exp 'R
-- infoGain p q = average (p ⋆ \w -> factor (log ((dp w) / (dq w) )) >> η w)
--   where dp = distr p
--         dq = distr q

-- Theorem 1: infoGain (q `marginBy` f) q = infoGain' q f

-- Proof sketch: let P(x) = f(x) . Q(x)
-- D(P|Q)
--  = ∫ P(x) (log (P(x) / Q(x))) dx
--  = ∫ P(x) (log (f(x) P(x) / P(x))) dx
--  = ∫ P(x) (log (f(x))) dx
--  = ∫ P(x) log(f(x)) dx


-- infoGain' :: Exp ((W ⟶ 'R) ⟶ 'R) -> (Exp W -> Exp 'R) -> Exp 'R
-- infoGain' p f = average (p ⋆ \w -> factor (f w) >> η (negate (log (f w))))


-- Theorem 2: infoGain' q (indicator ∘ f) = infoGain'' q f
-- Corrolary 3: infoGain (q `marginBy` f) q = infoGain'' q f

-- infoGain'' :: Exp ((W ⟶ 'R) ⟶ 'R) -> (Exp W -> Exp 'T) -> Exp 'R
-- infoGain'' p f = log (measure p) - log (measure (p `marginBy'` (observe . f)))

-- as infoGain'', but in probability rather than logits
probGain :: Exp ((W ⟶ 'R) ⟶ 'R) -> (Exp W -> Exp 'T) -> Exp 'R
probGain p f = measure (p `marginBy'` (observe . f)) / measure p

-- example
-- expectedBits :: Exp 'R -> Exp 'R
-- expectedBits x = exp (negate x ^ fromInteger 2)

-- | Beta distribution with mean (μ) and sample size (ν)
betaμν :: (Algebraic a) => Rational -> Rational -> a -> a
betaμν μ ν = beta (μ*ν) ((1-μ)*ν)

-- | Beta distribution with mode (ω) and concentration (κ).  (High concentration means low variance)
betaωκ :: (Algebraic a) => Rational -> Rational -> a -> a
betaωκ ω κ = beta (ω*(κ-2)+1) ((1-ω)*(κ-2)+1)

-- example
beta :: (Roots a, Group a) => Rational -> Rational -> a -> a
beta α β x = (x ^/ (α-one)) * ((one-x) ^/ (β-one))

expectProb :: Algebraic a => a -> a
-- expectProb = beta 0.5 0.5 -- favour nothing (fisher prior for beta distribution)
-- expectProb = betaμν 0.5 10 -- favour 1 bit of information
expectProb = betaμν 0.8 10 -- favour more probable statements (smaller info gain)
-- expectProb = betaμν 0.25 10 -- expect 2 bits of information (with some variance)

marginBy :: Exp ((β ⟶ 'R) ⟶ 'R) -> (Exp β -> Exp 'R) -> Exp ((β ⟶ 'R) ⟶ 'R)
p `marginBy` f = p `marginBy'` (factor . f)

marginBy' :: Exp ((β ⟶ r) ⟶ r) -> (Exp β -> Exp (('Unit ⟶ r) ⟶ r)) -> Exp ((β ⟶ r) ⟶ r)
p `marginBy'` f = p ⋆ \x -> (f x) >> η x

l1 :: Exp ((Θ ⟶ 'R) ⟶ 'R)
l1 = linguisticParameterDistribution ⋆ \θ -> 
         -- factor (expectedBits (infoGain (l0 θ) worldDistribution)) >>
         -- factor (expectedBits (infoGain'' worldDistribution (interpU θ))) >>
         factor (expectProb (probGain worldDistribution (interpU θ))) >>
         η θ

l0Expr :: P (('Unit × 'R) × 'R)
l0Expr = asExpression (Lam $ \θ -> Lam $ \h -> distr (l0 θ) h)

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
    
