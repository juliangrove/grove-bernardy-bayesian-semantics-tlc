{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Models.Integrals.Conversion where

import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt, exp)
import TLC.Terms hiding ((>>), u, Con)
import Models.Integrals.Types
-- import qualified Algebra.Expression as E


--------------------------------------------------------------------------------
-- | Conversion from λ-terms

pattern App2 :: Neutral γ (α3 ⟶ (α2 ⟶ α)) -> NF γ α3 -> NF γ α2 -> NF γ α
pattern App2 f x y = Neu (NeuApp (NeuApp f x) y)
pattern NNVar :: Available (α) (γ) -> NF γ α
pattern NNVar i <- Neu (NeuVar (i))
pattern Equ :: NF γ R -> NF γ R -> NF γ R
pattern Equ x y = App2 (NeuCon (EqRl)) x y
pattern EqVars :: Available R (γ) -> Available R (γ)  -> NF γ R
pattern EqVars i j <- Equ (NNVar i) (NNVar j)
pattern Mults, Expos :: NF γ R -> NF γ R -> NF γ R
pattern Mults x y = App2 (NeuCon (Mult)) x y
pattern Expos x y = App2 (NeuCon (Expo)) x y
pattern Adds :: NF γ R -> NF γ R -> NF γ R
pattern Adds x y = App2 (NeuCon (Addi)) x y
pattern InEqVars :: Available R (γ) -> Available R (γ) -> NF γ R
pattern InEqVars i j <- InEq (NNVar i) (NNVar j)
pattern InEq :: NF γ R -> NF γ R -> NF γ R
pattern InEq x y = Neu (NeuApp (NeuCon (Indi))
                            (Neu (NeuApp (NeuApp (NeuCon (GTE))
                                          x) y)))
pattern Lesbegue :: NF γ (R ⟶ R) -> NF γ R
pattern Lesbegue f = Neu (NeuApp (NeuCon (Les)) f)
pattern Divide :: NF γ R -> NF γ R -> NF γ R
pattern Divide x y = Neu (NeuApp (NeuApp (NeuCon (Divi)) x) y)
pattern NNCon :: Field x => x -> NF γ R
pattern NNCon x <- Neu (NeuCon (Incl (fromRational -> x)))

retPoly :: Ret γ -> P γ
retPoly = Done

evalP :: NF 'Unit R -> P 'Unit
evalP = evalP'


evalP' :: forall γ. NF γ R -> P γ
evalP' = \case
  Neu (NeuApp (NeuCon (Indi)) (Neu (NeuCon (Tru)))) -> one
  Neu (NeuApp (NeuApp (NeuCon (EqRl))
               (Adds (NNVar i) (NNVar j))) (NNVar k)) ->
    Cond (IsZero $ A.var i + A.var j - A.var k) one
  EqVars i j -> Cond (IsZero $ A.var i - A.var j) one
  InEqVars i j -> Cond (IsNegative $ A.var j - A.var i) one
  Equ (NNVar i) t -> Cond (IsZero $ toAffine t - A.var i) one
  Equ t (NNVar i) -> Cond (IsZero $ toAffine t - A.var i) one
  InEq (NNVar i) (NNCon x) -> Cond (IsNegative $ A.constant x - A.var i) one
  InEq (NNCon x) (NNVar i) -> Cond (IsNegative $ A.var i - A.constant x) one
  Adds (evalP' -> x) (evalP' -> y) -> Add x y
  Mults (evalP' -> x) (evalP' -> y) -> x * y
  Divide x y -> evalP' x / evalP' y -- TODO: get rid of this and use * and recip
  Expos (evalP' -> x) (NNCon y) -> Power x y
  Lesbegue f -> Integrate (Domain [] []) $
                (evalP' $ λToNF $ App (wkn $ nfToλ f) (Var Get))
  t -> retPoly (evalRet t)
    -- error ("evalP': don't know how to handle: " ++ (show . nfToλ) t)

toAffine :: NF γ R -> A.Affine (Var γ) Rat
toAffine = \case
  NNCon x -> A.constant x
  NNVar v -> A.var v
  Adds (toAffine -> x) (toAffine -> y) -> x + y
  Mults (toRat -> x) (toAffine -> y) -> x *< y
  Divide (toAffine -> x) (toRat -> y) -> (one / y) *< x

toRat :: NF γ R -> Rat
toRat = \case
  NNCon x -> x
  Adds (toRat -> x) (toRat -> y) -> x + y
  Mults (toRat -> x) (toRat -> y) -> x * y
  Divide (toRat -> x) (toRat -> y) -> x / y

evalRet :: forall γ. NF γ R -> Ret γ
evalRet = \case
  NNCon x -> constPoly (fromRational x)
  Adds x y -> evalRet x + evalRet y
  Mults x y -> evalRet x * evalRet y
  Divide x y -> evalRet x / evalRet y
  Expos x (NNCon y) -> evalRet x ^/ y
  NNVar i -> varPoly i
  Neu (NeuApp (NeuCon Exp) x) -> exp (evalRet x)
  (Neu (NeuCon CircleConstant)) -> pi
  t -> error ("evalRet: don't know how to handle: " ++ (show . nfToλ) t)
