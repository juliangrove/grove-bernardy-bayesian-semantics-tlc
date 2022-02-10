module Main where

import Examples.Anaphora
import Models.Logical.FiniteLogical
import TLC.Distributions
import TLC.Terms

main :: IO ()
main = do
  let x = evalLF $ normalForm $ App (distr (App (s1' (S (S Z)) 1) (Pair k1 (nf_to_λ $ u'' [Nothing])))) (nf_to_λ $ u'' [Just Vlad])
  -- let x = evalLF $ normalForm $ expectedValue $ App (l1 (S (S Z))) (nf_to_λ $ u'' [Nothing]) ⋆ Lam (η (App (hmorph (S (S Z)) (App (Con $ General EqGen) (Pair (sel' 0 (upd' jp (upd' vlad emp))) vlad))) (Var Get)))
  putStrLn $ show x
