{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Examples.Anaphora
-- import Examples.Naloma
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
        l1 α n `App` nf_to_λ (u'' [Nothing]) ⋆
        Lam (η (hmorph n
                (Con (General EqGen) `App`
                 (sel' 0 (upd' jp (upd' vlad emp)) `Pair` jp)) `App` Var Get))
  print (E.eval (\case) result :: Double)
