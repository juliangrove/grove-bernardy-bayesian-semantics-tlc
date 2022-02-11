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


type ValueSubst = forall δ β. β ∈ δ -> FOL.Value

viewApp :: ValueSubst -> γ ⊢ α -> Maybe (String, [FOL.Value])
viewApp ρ = \case
  TLC.Terms.Con c -> Just (show c, [])
  App x y -> case viewApp ρ x of
               Just (f, args) -> Just (f, args ++ [termToFol' ρ y])
               _ -> Nothing
  _ -> Nothing

termToFol' :: ValueSubst -> γ ⊢ α -> FOL.Value
termToFol' ρ t =
  case t of
    Var i -> ρ i
    True' -> FOL.VTru
    False' -> FOL.VFal
    And' (termToFol' ρ -> φ) (termToFol' ρ -> ψ) -> FOL.VAnd φ ψ
    Imp' (termToFol' ρ -> φ) (termToFol' ρ -> ψ) -> FOL.VOr (FOL.VNot φ) ψ
    Or' (termToFol' ρ -> φ) (termToFol' ρ -> ψ) -> FOL.VOr φ ψ
    Forall' f -> FOL.VAll (\x -> termToFol' (\case
                                                Get -> x
                                                Weaken i -> ρ i)
                            (evalβ $ App (wkn f) (Var Get)))
    Exists' f -> FOL.VExi (\x -> termToFol' (\case
                                                Get -> x
                                                Weaken i -> ρ i)
                            (evalβ $ App (wkn f) (Var Get)))
    _ -> case viewApp ρ t of
                 Just (f, args) -> FOL.VApp f (args)
                 Nothing -> error $ "termToFol': viewApp produced Nothing"

termToFol :: NF γ α -> FOL.Value
termToFol = termToFol' (\case) . nf_to_λ 

makeBernoulli :: γ ⊢ 'T -> γ ⊢ 'R -> γ ⊢ (('T ⟶ 'R) ⟶ 'R)
makeBernoulli φ x = Lam $ App (Var Get) (wkn φ) * (wkn x) +
                    App (Var Get) (Imp' (wkn φ) False') * (one - wkn x)

-- makeBernoulli φ x k = Bernoulli x (\t ->  k (if t then 𝟙(φ) else 𝟙(φ ⊢ ⊥))) 

tryProve' :: [FOL.Value] -> FOL.Value -> Status
tryProve' = tryProve 10

type Finite = E.Expr Double

evalFL' :: NF γ 'R -> State [NF γ 'T] Finite
evalFL' = \case
  NCon (General (Incl x)) -> pure $ fromRational x
  Neu (NeuApp (NeuCon (General Indi)) ψ) -> state $ \φs ->
    case tryProve' (map termToFol φs) (termToFol ψ) of
      Contradiction -> (zero, [normalForm False'])
      _ -> (one, ψ:φs)
  Mults (evalFL' -> x) (evalFL' -> y) -> (*) <$> x <*> y
  Adds (evalState . evalFL' -> x) (evalState . evalFL' -> y) ->
    state $ \φs -> (x φs + y φs, φs)
  Divide (evalFL' -> x) (evalState . evalFL' -> y) ->
    flip (/) <$> state (\φs -> (y φs, φs)) <*> x
  Expos (evalFL' -> x) (NCon (General (Incl y))) ->
    fmap (Algebra.Classes.** (fromRational y)) x
  t -> error ("evalFL': don't know how to handle: " ++ (show . nf_to_λ) t)

evalFL :: NF 'Unit 'R -> Finite
evalFL = flip evalState [] . evalFL'

