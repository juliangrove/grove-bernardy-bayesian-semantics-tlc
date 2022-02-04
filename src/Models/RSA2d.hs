{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RebindableSyntax #-}
module Models.RSA2d where

import Prelude (Double,Int, ($), (.), fmap, Ord(..), toRational, putStrLn, IO,String,show,unwords,unlines,writeFile,Integer)
import Algebra.Linear.Chebyshev
import Algebra.Linear.Vector
import Algebra.Classes
import Data.Complex
import Data.Foldable
import Control.Applicative

type Ivl = (Double,Double)

type F2 a = Double -> Double -> a
type S2 a = Samples (Samples a)
-- type P2 a = Polynomial (Polynomial a)

type C = Complex Double

normal :: Transcendental a => a -> a -> a -> a
normal μ σ x = recip (σ * sqrt (2 * pi)) * exp (-0.5 * ((μ - x) / σ) ^+ 2)

prior :: Transcendental a => a -> p -> a
prior h u = normal 68 3 h

groundFun :: (Ord t, Transcendental t) => t -> t -> t
groundFun h u = if h < u then 0 else prior h u
                 

size__ :: Int
size__ = 256

ivlH :: (Double, Double)
ivlH = (68-10, 68+10)

ivlU :: (Double, Double)
ivlU = (68-20, 68+10)

ground :: S2 Double
ground = sample' groundFun

sample' :: F2 Double -> S2 Double
sample' = sample2d size__ ivlH ivlU

sample2d :: Int -> Ivl -> Ivl -> F2 Double -> S2 Double
sample2d n (lo1,hi1) (lo2,hi2) f =
  sample @Double n lo1 hi1 $ \x ->
  sample @Double n lo2 hi2 $ \y ->
  f x y

normalizeS :: Samples Double -> Samples Double
normalizeS v = (recip (integralUnitIvl @Double $ fmap realPart $ samplesToPoly @C $ fmap (:+ 0) v)) *^ v

-- fit2 :: S2 Double -> P2 Double
-- fit2 = fmap (fmap realPart) . samplesToPoly @C  . fmap (samplesToPoly @C . fmap (:+ 0) )


get :: Samples (Samples a) -> Int -> Int -> a
get m i j = fromSamples (fromSamples m ! i) ! j

pts :: Vec Double
pts = chebPoints size__

toGnuPlot :: String -> Samples (Samples Double) -> IO ()
toGnuPlot fn x = writeFile fn
            $   unlines $ fmap (unwords . fmap show) $
            (0 : (toList pts)) :
            [ (pts ! i) : toList (fromSamples x ! i)  | i <- [0..size__] ]

normalizeH :: Samples (Samples Double) -> Samples (Samples Double)
normalizeH = xpose . fmap normalizeS . xpose
 where
  xpose :: Samples (Samples Double) -> Samples (Samples Double)
  xpose m = Samples $ generate (size__+1)  $ \i -> Samples $ generate (size__+1) $ \ j -> get m j i

mkSamples :: (Int -> Int -> a) -> Samples (Samples a)
mkSamples f = Samples $ generate (size__+1)  $ \i -> Samples $ generate (size__+1) $ \ j -> f i j

normalizeU :: Samples (Samples Double) -> Samples (Samples Double)
normalizeU = fmap normalizeS

l0 :: Samples (Samples Double)
l0 = normalizeH ground

α :: Natural
α = 40

s1 :: Samples (Samples Double)
s1 =  normalizeU (fmap (fmap (^+ α)) l0)

l1 :: Samples (Samples Double)
l1 = normalizeH $ mkSamples $ \h u -> get s1 h u * get (sample' $ prior) h u

-- >>> toGnuPlot "ground.dat" ground
-- >>> toGnuPlot "l0.dat" l0
-- >>> toGnuPlot "s1.dat" s1
-- >>> toGnuPlot "l1.dat" l1

-- To see this, in gnuplot, run:
-- set zrange [0:5]
-- splot 'l1.dat' nonuniform matrix with pm3d




