{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}

import Examples.Anaphora (l1, p1', p2')
-- import Examples.HNaloma (l1)
-- import Examples.Naloma
import Models.Logical.FiniteLogical
import Prelude hiding (Num(..), Fractional(..))
import TLC.Distributions
import TLC.Terms
import Text.Pretty.Math
import Algebra.Classes
import qualified Algebra.Expression as E

main :: IO ()
main = test1

test0 :: IO ()
test0 = do
  let result = evalFL $ normalForm $ expectedValue $ (p1' ⋆ Lam (η (Con Indi `App` Var Get)))
    in print (E.eval id result :: Double)

test1 :: IO ()
test1 =
  do
  let result = evalFL $ normalForm $ expectedValue $ (p2' ⋆ Lam (η (Con Indi `App` Var Get)))
    in print (E.eval id result :: Double)

test2 :: IO ()
test2 = do
  putStrLn "temp:"
  temp <- getLine
  let n = S (S Z)
      α = toRational (read temp :: Double)
      result = evalFL $ normalForm $ expectedValue $
        l1 α n @@ Con (Utt (MergeRgt (Pn 0) IsPrepared)) ⋆
        Lam (η (hmorph n
                (Con EqGen `App`
                 (sel' 0 (upd' jp (upd' vlad emp)) `Pair` jp)) `App` Var Get))
  print (E.eval id result :: Double)

