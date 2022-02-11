{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Examples.Anaphora
import Models.Logical.FiniteLogical
import TLC.Distributions
import TLC.Terms
import Text.Pretty.Math
import qualified Algebra.Expression as E

main :: IO ()
main = do
  -- let x = evalLF $ normalForm $ distr ((s1' (S (S Z)) 1) `App` (Pair (k1 0) (nf_to_λ $ u'' [Nothing]))) `App` (nf_to_λ $ u'' [Just JP])        
  let x = expectedValue $ App (l1 (S (S Z))) (nf_to_λ $ u'' [Nothing]) ⋆ Lam (η (App (hmorph (S (S Z)) (App (Con $ General EqGen) (Pair (sel' 0 (upd' jp (upd' vlad emp))) jp))) (Var Get)))
  -- print (E.eval (\case) x :: Doc)
  displayVs $ evalβ x
