module Models.Gnuplot where

import Data.Foldable
import Algebra.Linear.Chebyshev
import Algebra.Linear.Vector


-- | 
-- To see output of this function, in gnuplot, run:
-- set zrange [0:5]
-- splot 'fn' nonuniform matrix with pm3d

toGnuPlot :: String -> Samples (Samples Double) -> IO ()
toGnuPlot fn x = writeFile fn
            $   unlines $ fmap (unwords . fmap show) $
            (0 : (toList pts)) :
            [ (pts ! i) : toList (fromSamples x ! i)  | i <- [0..sz] ]
    where sz = Data.Foldable.length x - 1
          pts = chebPoints sz

