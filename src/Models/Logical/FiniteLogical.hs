{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Models.Logical.FiniteLogical where

import Algebra.Classes
import Control.Monad.State
import qualified FOL.FOL as FOL
import FOL.Solver
import Models.Integrals.Conversion
import Models.Integrals.Types
import Prelude hiding (Num(..), Fractional(..), (>>), fromRational, sqrt, (/))
import TLC.Terms
import Text.Pretty.Math
import qualified Algebra.Expression as E



makeBernoulli :: γ ⊢ 'T -> γ ⊢ 'R -> γ ⊢ (('T ⟶ 'R) ⟶ 'R)
makeBernoulli φ x = Lam $ App (Var Get) (wkn φ) * (wkn x) +
                    App (Var Get) (Imp' (wkn φ) False') * (one - wkn x)

-- makeBernoulli φ x k = Bernoulli x (\t ->  k (if t then 𝟙(φ) else 𝟙(φ ⊢ ⊥))) 

tryProve' :: [FOL.Value] -> FOL.Value -> Status
tryProve' = tryProve 10

type Finite = E.Expr Double

evalFL :: NF γ 'R -> Finite
evalFL = \case
  NCon ((Incl x)) -> fromRational x
  Neu (NeuApp (NeuCon (Indi)) φ) ->
    case tryProve' [] (termToFol φ) of
      Contradiction -> zero
      _ -> one
  Mults (evalFL -> x) (evalFL -> y) -> x * y
  Adds (evalFL -> x) (evalFL -> y) -> x + y
  Divide (evalFL -> x) (evalFL -> y) -> x / y
  Expos (evalFL -> x) (evalFL -> y) -> x Algebra.Classes.** y
  t -> error ("evalFL: don't know how to handle: " ++ (show . nf_to_λ) t)

evalFLState' :: NF γ 'R -> State [NF γ 'T] Finite
evalFLState' = \case
  NCon ((Incl x)) -> pure $ fromRational x
  Neu (NeuApp (NeuCon (Indi)) ψ) -> state $ \φs ->
    case tryProve' (map termToFol φs) (termToFol ψ) of
      Contradiction -> (zero, [normalForm False'])
      _ -> (one, ψ:φs)
  Mults (evalFLState' -> x) (evalFLState' -> y) -> (*) <$> x <*> y
  Adds (evalState . evalFLState' -> x) (evalState . evalFLState' -> y) ->
    state $ \φs -> (x φs + y φs, φs)
  Divide (evalFLState' -> x) (evalState . evalFLState' -> y) ->
    flip (/) <$> state (\φs -> (y φs, φs)) <*> x
  Expos (evalFLState' -> x) (NCon ((Incl y))) ->
    fmap (Algebra.Classes.** (fromRational y)) x
  t -> error ("evalFLState': don't know how to handle: " ++ (show . nf_to_λ) t)

evalFLState :: NF 'Unit 'R -> Finite
evalFLState = flip evalState [] . evalFLState'

