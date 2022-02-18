{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import qualified Examples.Anaphora as A
-- import Examples.HNaloma (l1)
import Models.Logical.FiniteLogical
import Prelude hiding (Num(..), Fractional(..))
import TLC.Distributions
import TLC.Terms
import Text.Pretty.Math
import Algebra.Classes
import qualified Algebra.Expression as E

main :: IO ()
main = do
  putStrLn "temp:"
  temp <- getLine
  let n = S (S Z)
      α = toRational (read temp :: Double)
      result = evalFL $ normalForm $ expectedValue $
        A.l1 α n `App` nf_to_λ (u'' [Nothing]) ⋆
        Lam (η (hmorph n
                (Con EqGen `App`
                 (sel' 0 (upd' jp (upd' vlad emp)) `Pair` jp)) `App` Var Get))
  print (E.eval id result :: Double)
