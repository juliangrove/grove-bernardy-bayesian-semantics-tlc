{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Models.Logical.Logical where

import Algebra.Classes
import qualified FOL.FOL as FOL
import FOL.Solver
import Prelude hiding (Num(..), (>>))
import TLC.Terms

type ValueSubst = forall δ β. β ∈ δ -> FOL.Value

viewApp :: ValueSubst -> γ ⊢ α -> Maybe (String, [FOL.Value])
viewApp ρ = \case
  Con c -> Just (show c, [])
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
           Just (f, args) -> FOL.VApp f args
           Nothing ->  error $ "termToFol': unsupported input " ++ show t


-- >>> tryProve' $ termToFol False'
-- Contradiction

termToFol :: γ ⊢ α -> FOL.Value
termToFol = termToFol' (\case)

makeBernoulli :: γ ⊢ 'T -> γ ⊢ 'R -> γ ⊢ (('T ⟶ 'R) ⟶ 'R)
makeBernoulli φ x = Lam $ App (Var Get) (wkn φ) * (wkn x) +
                    App (Var Get) (Imp' (wkn φ) True') * (one - wkn x)

tryProve' :: FOL.Value -> Status
tryProve' = tryProve 10 []

-- >>> FOL.doQuote FOL.VFal
-- ⊥

-- >>> tryProve' $ termToFol (Con $ Logical Fal)
-- Contradiction
