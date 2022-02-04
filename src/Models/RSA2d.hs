{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RebindableSyntax #-}
module Models.RSA2d where

import Prelude (Double,Int, ($), (.), fmap, Ord(..), toRational, putStrLn, IO,String,show,unwords,unlines,writeFile)
import Algebra.Linear.Chebyshev
import Algebra.Linear
import Algebra.Linear.Vector
import Algebra.Classes
import Data.Complex
import Text.Pretty.Math
import Data.Foldable

type Ivl = (Double,Double)

type F2 a = Double -> Double -> a
type P2 a = Polynomial (Polynomial a)
type S2 a = Samples (Samples a)

type C = Complex Double

normal :: Transcendental a => a -> a -> a -> a
normal μ σ x = recip (σ * sqrt (2 * pi)) * exp (-0.5 * ((μ - x) / σ) ^+ 2)

groundFun :: (Ord t, Transcendental t) => t -> t -> t
groundFun h u = if h < u then 0 else
                normal 68 3 h 

size__ = 128

ivl = (68-10, 68+10)

ground :: S2 Double
ground = sample2d size__ ivl ivl (groundFun)

sample2d :: Int -> Ivl -> Ivl -> F2 Double -> S2 Double
sample2d n (lo1,h1) (l2,h2) f = sample @Double n lo1 h1 $ \x ->
                               sample @Double n l2 h2 $ \y ->
                               f x y

fit2 :: S2 Double -> P2 Double
fit2 = fmap (fmap realPart) . samplesToPoly @C  . fmap (samplesToPoly @C . fmap (:+ 0) )

get :: Int -> Int -> Samples (Samples a) -> a
get i j m = fromSamples (fromSamples m ! i) ! j

pts :: Vec Double
pts = chebPoints size__

dump :: String -> Samples (Samples Double) -> IO ()
dump fn x = writeFile fn
            $   unlines $ fmap (unwords . fmap show) $
            (0 : (toList pts)) :
            [ (pts ! i) : toList (fromSamples x ! i)  | i <- [0..size__] ]


normalizeH = xpose . fmap normalizeS . xpose
normalizeU = fmap normalizeS

l0 :: Samples (Samples Double)
l0 = normalizeH ground

xpose :: Samples (Samples Double) -> Samples (Samples Double)
xpose m = Samples $ generate (size__+1)  $ \i -> Samples $ generate (size__+1) $ \ j -> get j i m

s1 :: Samples (Samples Double)
s1 =  normalizeU l0

lo1 :: Samples (Samples Double)
lo1 =  normalizeH s1

-- >>> dump "ground.dat" ground
-- >>> dump "l0.dat" l0
-- >>> dump "s1.dat" s1
-- >>> dump "lo1.dat" lo1



normalizeS :: Samples Double -> Samples Double
normalizeS v = (recip (integralUnitIvl @Double $ fmap realPart $ samplesToPoly @C $ fmap (:+ 0) v)) *^ v



