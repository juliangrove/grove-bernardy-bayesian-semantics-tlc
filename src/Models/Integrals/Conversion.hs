{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}
module Models.Integrals.Conversion where

import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt, exp)
import TLC.Terms hiding ((>>), u, Con)
import Models.Integrals.Types
import qualified Algebra.Expression as E


--------------------------------------------------------------------------------
-- | Conversion from λ-terms

pattern App2 :: Neutral γ (α3 ⟶ (α2 ⟶ α)) -> NF γ α3 -> NF γ α2 -> NF γ α
pattern App2 f x y = Neu (NeuApp (NeuApp f x) y)
pattern NNVar :: Available (α) (γ) -> NF γ α
pattern NNVar i <- Neu (NeuVar (i))
pattern Equ :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Equ x y = App2 (NeuCon (General EqRl)) x y
pattern EqVars :: Available 'R (γ) -> Available 'R (γ)  -> NF γ 'R
pattern EqVars i j <- Equ (NNVar i) (NNVar j)
pattern Mults :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Mults x y = App2 (NeuCon (General Mult)) x y
pattern Adds :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Adds x y = App2 (NeuCon (General Addi)) x y
pattern InEqVars :: Available 'R (γ) -> Available 'R (γ) -> NF γ 'R
pattern InEqVars i j <- InEq (NNVar i) (NNVar j)
pattern InEq :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern InEq x y = Neu (NeuApp (NeuCon (General Indi))
                            (Neu (NeuApp (NeuApp (NeuCon (Special GTE))
                                          x) y)))
pattern Normal :: Field x=> x -> x -> NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Normal x y f <- Neu (NeuApp (NeuApp (NeuCon (General Nml))
                                    (NFPair (NNCon x) (NNCon y))) f)
pattern Cauchy :: Field x => x -> x ->NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Cauchy x y f <- Neu (NeuApp (NeuApp (NeuCon (General Cau))
                                    (NFPair (NNCon x) (NNCon y))) f)
pattern Quartic :: Field x => x -> x ->NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Quartic x y f <- Neu (NeuApp (NeuApp (NeuCon (General Qua))
                                    (NFPair (NNCon x) (NNCon y))) f)
pattern Uniform :: Field x => x -> x ->NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Uniform x y f <- Neu (NeuApp (NeuApp (NeuCon (General Uni))
                                     (NFPair (NNCon x) (NNCon y))) f)
pattern Lesbegue :: NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Lesbegue f = Neu (NeuApp (NeuCon (General Les)) f)
pattern Divide :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Divide x y = Neu (NeuApp (NeuApp (NeuCon (General Divi)) x) y)
pattern NNCon :: Field x => x -> NF γ 'R
pattern NNCon x <- Neu (NeuCon (General (Incl (fromRational -> x))))

retPoly :: Ret γ -> P γ
retPoly = Ret 

evalP :: NF 'Unit 'R -> P 'Unit
evalP = evalP'

evalP' :: NF γ 'R -> P (γ)
evalP' = \case
  NNCon x -> retPoly $ constPoly (fromRational x)
  Neu (NeuApp (NeuCon (General Indi)) (Neu (NeuCon (Logical Tru)))) -> one
  Neu (NeuApp (NeuApp (NeuCon (General EqRl))
               (Adds (NNVar i) (NNVar j))) (NNVar k)) ->
    Cond (IsZero $ A.var i + A.var j - A.var k) one
  EqVars i j -> Cond (IsZero $ A.var i - A.var j) one
  InEqVars i j -> Cond (IsNegative $ A.var j - A.var i) one
  Equ (NNVar i) (NNCon x) -> Cond (IsZero $ A.constant x - A.var i) one
  InEq (NNVar i) (NNCon x) -> Cond (IsNegative $ A.constant x - A.var i) one
  InEq (NNCon x) (NNVar i) -> Cond (IsNegative $ A.var i - A.constant x) one
  Adds (evalP' -> x) (evalP' -> y) -> Add x y
  Mults (evalP' -> x) (evalP' -> y) -> x * y
  Normal μ σ f -> Integrate full $
      (retPoly $ constPoly (1 / (σ * sqrt (2 * pi)))
       * exp (constPoly (-1/2)
                       * (constPoly (1/σ) * (constPoly μ - varPoly Get)) ^+ 2))
    * (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Cauchy x0 γ f -> Integrate full $
    Div (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))  
    (retPoly $ (constPoly (pi * γ)
                 * (one + (constPoly (one/γ)
                            * (varPoly Get - constPoly x0)) ^+2)))
  Quartic μ σ f -> Integrate (Domain [A.constant (μ - a)]
                              [A.constant (μ + a)]) $
    (retPoly $ (constPoly ((15 / 16) / (a ^+ 5)))
     * ((varPoly Get - constPoly μ) - constPoly a) ^+ 2
     * ((varPoly Get - constPoly μ) + constPoly a) ^+ 2)
    * (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
    where a = sqrt 7 * σ
  Uniform x y f -> Integrate (Domain [A.constant x] [A.constant y]) $ 
    (retPoly $ constPoly (1 / (y - x))) *
    (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Lesbegue f -> Integrate (Domain [] []) $
                (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  NNVar i -> retPoly $ varPoly i
  Divide x y -> Div (evalP' x) (evalP' y)
  t -> error ("evalP': don't know how to handle: " ++ (show . nf_to_λ) t)


