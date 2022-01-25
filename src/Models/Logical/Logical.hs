{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Models.Logical.Logical where

import qualified FOL.FOL as FOL
import TLC.Terms


viewApp :: γ ⊢ α -> Maybe (String, [FOL.Value])
viewApp (Con c) = Just (show c, [])
viewApp (App x y) = case viewApp x of
  Just (f, args) -> Just (f, args ++ [termToFol y])
  _ -> Nothing
viewApp _ = Nothing

termToFol' :: (forall δ β. β ∈ δ -> FOL.Value) -> γ ⊢ α -> FOL.Value
termToFol' ρ t =
  case viewApp t of
    Just (f, args) -> FOL.VApp f args
    Nothing -> 
      case t of
        Var i -> ρ i
        True' -> FOL.VTru
        False' -> FOL.VFal
        And' (termToFol' ρ -> φ) (termToFol' ρ -> ψ) -> FOL.VAnd φ ψ
        Imp' (termToFol' ρ -> φ) (termToFol' ρ -> ψ) -> FOL.VOr (FOL.VNot φ) ψ
        Or' (termToFol' ρ -> φ) (termToFol' ρ -> ψ) -> FOL.VOr φ ψ
        Forall' f -> FOL.VAll (\x -> termToFol' (\case Get -> x; Weaken i -> ρ i)
                                (evalβ $ App (wkn f) (Var Get)))
        Exists' f -> FOL.VExi (\x -> termToFol' (\case Get -> x; Weaken i -> ρ i)
                                (evalβ $ App (wkn f) (Var Get)))
        _ -> error "termToFol': unsupported input"
             
termToFol :: γ ⊢ α -> FOL.Value
termToFol = termToFol' (\case)
