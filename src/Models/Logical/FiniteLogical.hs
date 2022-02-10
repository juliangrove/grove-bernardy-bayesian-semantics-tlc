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

-- >>> FOL.doQuote $ termToFol $ normalForm $ Exists' (Lam (App (App (rel 0) (Var Get)) jp))
-- ∃x. relation0(x,jp)

termToFol :: NF γ α -> FOL.Value
termToFol = termToFol' (\case) . nf_to_λ 

makeBernoulli :: γ ⊢ 'T -> γ ⊢ 'R -> γ ⊢ (('T ⟶ 'R) ⟶ 'R)
makeBernoulli φ x = Lam $ App (Var Get) (wkn φ) * (wkn x) +
                    App (Var Get) (Imp' (wkn φ) False') * (one - wkn x)

tryProve' :: [FOL.Value] -> FOL.Value -> Status
tryProve' = tryProve 10

type Finite = E.Expr Zero

-- >>> :t tryProve
-- tryProve :: Int -> [FOL.Value] -> FOL.Value -> Status

evalLF' :: NF γ 'R -> State [NF γ 'T] Finite
evalLF' = \case
  NCon (General (Incl x)) -> pure $ fromRational x
  Neu (NeuApp (NeuCon (General Indi)) ψ) -> state $ \φs ->
    case tryProve' (map termToFol φs) (termToFol ψ) of
      Contradiction -> (zero, ψ:φs)
      _ -> (one, ψ:φs)
  Mults (NCon (General (Incl 0))) _ -> pure zero
  Mults _ (NCon (General (Incl 0))) -> pure zero
  Mults (evalLF' -> x) (evalLF' -> y) -> (*) <$> x <*> y
  Adds (evalState . evalLF' -> x) (evalState . evalLF' -> y) ->
    state $ \φs -> (x φs + y φs, φs)
  Divide (NCon (General (Incl 0))) _ -> pure zero
  Divide (evalLF' -> x) (evalState . evalLF' -> y) ->
    flip (/) <$> state (\φs -> (y φs, φs)) <*> x
  Expos (evalLF' -> x) (NCon (General (Incl y))) ->
    fmap (Algebra.Classes.** (fromRational y)) x
  t -> error ("evalLF': don't know how to handle: " ++ (show . nf_to_λ) t)


-- evalLF' :: NF γ 'R -> State [NF γ 'T] (P γ)
-- evalLF' = \case
--   NNCon x -> pure $ retPoly $ constPoly (fromRational x)
--   Neu (NeuApp (NeuCon (General Indi)) ψ) -> state $ \φs ->
--     case tryProve' (map termToFol φs) (termToFol ψ) of
--       Contradiction -> (zero, ψ:φs)
--       _ -> (one, ψ:φs)
--   Neu (NeuApp (NeuApp (NeuCon (General EqRl))
--                (Adds (NNVar i) (NNVar j))) (NNVar k)) ->
--     pure $ Cond (IsZero $ A.var i + A.var j - A.var k) one
--   EqVars i j -> pure $ Cond (IsZero $ A.var i - A.var j) one
--   InEqVars i j -> pure $ Cond (IsNegative $ A.var j - A.var i) one
--   Equ (NNVar i) (NNCon x) ->
--     pure $ Cond (IsZero $ A.constant x - A.var i) one
--   InEq (NNVar i) (NNCon x) ->
--     pure $ Cond (IsNegative $ A.constant x - A.var i) one
--   InEq (NNCon x) (NNVar i) ->
--     pure $ Cond (IsNegative $ A.var i - A.constant x) one
--   Adds (evalState . evalLF' -> x) (evalState . evalLF' -> y) ->
--     state $ \φs -> (Add (x φs) (y φs), φs)
--   Mults (evalLF' -> x) (evalLF' -> y) -> (*) <$> x <*> y
--   -- Normal μ σ f -> Integrate full $ 
--       -- (retPoly $ constPoly (1 / (σ * sqrt (2 * Models.Field.Pi)))
--        -- * exponential (constPoly (-1/2)
--                        -- * (constPoly (1/σ) * (constPoly μ - varPoly Get)) ^+ 2))
--     -- * (evalLF' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
--   -- Cauchy x0 γ f -> Integrate full $
--     -- Div (evalLF' (map wknNF φs) $
--          -- normalForm $ App (wkn $ nf_to_λ f) (Var Get))  
--     -- (retPoly $ (constPoly (Models.Field.Pi * γ)
--                  -- * (one + (constPoly (one/γ)
--                             -- * (varPoly Get - constPoly x0)) ^+2)))
--   -- Quartic μ σ f -> Integrate (Domain [A.constant (μ - a)]
--                               -- [A.constant (μ + a)]) $
--     -- (retPoly $ (constPoly ((15 / 16) / (a ^+ 5)))
--      -- * ((varPoly Get - constPoly μ) - constPoly a) ^+ 2
--      -- * ((varPoly Get - constPoly μ) + constPoly a) ^+ 2)
--     -- * (evalLF' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
--     -- where a = sqrt 7 * σ
--   -- Uniform x y f -> Integrate (Domain [A.constant x] [A.constant y]) $ 
--     -- (retPoly $ constPoly (1 / (y - x))) *
--     -- (evalLF' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
--   -- Lesbegue f -> Integrate (Domain [] []) $
--                 -- (evalLF' (map wknNF φs) $
--                  -- normalForm $ App (wkn $ nf_to_λ f) (Var Get))
--   NNVar i -> pure $ retPoly $ varPoly i
--   Divide (evalLF' -> x) (evalState . evalLF' -> y) ->
--     flip Div <$> state (\φs -> (y φs, φs)) <*> x
--   t -> error ("evalLF': don't know how to handle: " ++ (show . nf_to_λ) t)

evalLF :: NF 'Unit 'R -> Finite
evalLF = flip evalState [] . evalLF'

-- >>> FOL.doQuote FOL.VFal
-- ⊥

-- >>> tryProve' $ termToFol (Con $ Logical Fal)
-- Contradiction
