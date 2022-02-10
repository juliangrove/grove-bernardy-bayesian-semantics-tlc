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


test :: P (('Unit × 'R) × 'R)
test = simplifyFun2 [] $ fromHoas (utilitys1 4)

-- >>> maxima test
-- charfun(50 - y <= 0)*charfun(-80 + y <= 0)*charfun(50 - x <= 0)*charfun(-80 + x <= 0)*charfun(-x + y <= 0)*integrate(integrate(exp(-1/2*(1/3*(68 - u))^2), u, z, 80)^(-4), z, 50, x)^(-1)*integrate(exp(-1/2*(1/3*(68 - z))^2), z, y, 80)^(-4)

testSamples :: V.Vec (V.Vec Double)
testSamples = approxTop test

-- >>> toGnuPlot "test.dat" testSamples

k :: Exp ((Context0 ⟶ 'R) ⟶ 'R)
k = uniform 0 1 ⋆ \θ ->
    normal 68 3 ⋆ \h ->
           (observe (h ≥ fromInteger 50) >>
           (observe (fromInteger 80 ≥ h) >>
             (η (Pair
                 (Pair
                  (Pair
                   (Pair
                    (Pair TT (toHoas (F.≥)))
                    θ)
                   (toHoas F.human))
                  (Lam $ \_ -> h))
                 (toHoas F.vlad)))))

utts'' :: Exp (('U ⟶ 'R) ⟶ 'R)
utts'' = uniform 50 80 ⋆ (\x -> η (u' x)) 

-- | Pragmatic speaker
s1 :: Integer -> Exp Context0 -> Exp (('U ⟶ 'R) ⟶ 'R)
s1 α ctx = utts'' ⋆ \u ->
            factor ((distr (l0 u) ctx) ^+ α) >>
            η u

s1Distr :: Integer -> Exp Context0 -> Exp 'U -> Exp 'R
s1Distr α ctx u = distr (s1 α ctx) u

-- | Literal listener
l0 ::  Exp 'U -> Exp ((Context0 ⟶ 'R) ⟶ 'R)
l0 u = k ⋆ \ctx ->
       observe (Con (General (Interp F.Z)) @@ u @@ ctx) >>
       η ctx

-- | Pragmatic listener
l1 :: Integer -> Exp 'U -> Exp ((Context0 ⟶ 'R) ⟶ 'R)
l1 α u = k ⋆ \ctx -> 
         factor (s1Distr α ctx u) >>
         η ctx

l0Distr :: Exp 'U -> Exp Context0 -> Exp 'R
l0Distr u ctx = distr (l0 u) ctx

l1Distr :: Integer -> Exp 'U -> Exp Context0 -> Exp 'R
l1Distr α u ctx = distr (l1 α u) ctx


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
  
toAtLeastHeight :: Exp ('R ⟶ 'U)
toAtLeastHeight = Con (General Utt')  

utilityl0 :: Exp ('R ⟶ 'R ⟶ 'R)
utilityl0 = Lam $ \h -> Lam $ \u -> l0Distr (toAtLeastHeight @@ h) (heightToCtx u)

utilitys1 :: Integer -> Exp ('R ⟶ 'R ⟶ 'R)
utilitys1 α = Lam $ \h -> Lam $ \u -> s1Distr α (heightToCtx u) (toAtLeastHeight @@ h) 

utilityl1 :: Integer -> Exp ('R ⟶ 'R ⟶ 'R)
utilityl1 α = Lam $ \h -> Lam $ \u -> l1Distr α (toAtLeastHeight @@ h) (heightToCtx u)

