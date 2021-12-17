{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module RSA where

import Prelude hiding (Monad(..))
import TLC.RN
import TLC.Terms

factor :: γ ⊢ (R ⟶ ((Unit ⟶ R) ⟶ R))
factor = Lam (Lam (App (App (Con Mult) (Var (Weaken Get))) (App (Var Get) TT)))
factor' x = App factor x

observe :: γ ⊢ (T ⟶ ((Unit ⟶ R) ⟶ R))
observe = Lam (App factor (App (Con Indi) (Var Get)))
observe' φ = App observe φ
 
normal :: γ ⊢ ((R × R) ⟶ ((R ⟶ R) ⟶ R))
normal = Con Nml

height = Con Height
human = Con Human
θ = Con Theta
(≥) = Con GTE
emp = Con Empty
upd = Con Upd
sel = Con Sel

(/\) :: γ ⊢ T -> γ ⊢ T -> γ ⊢ T
p /\ q = App (App (Con And) p) q

exists :: γ ⊢ (α ⟶ T) -> γ ⊢ T
exists φ = App (Con Exists) φ

distr :: γ ⊢ ((α ⟶ R) ⟶ R) -> γ ⊢ (α ⟶ R)
distr p = App (Con Distr) p

k :: γ ⊢ ((Context ⟶ R) ⟶ R)
k = (App normal (Pair (Con $ Rl 68) (Con $ Rl 3))) >>= Lam (η (Pair height (Pair human (Pair (Var Get) (Pair (≥) (Pair emp (Pair upd (Pair sel TT))))))))

utts :: γ ⊢ ((U ⟶ R) ⟶ R)
utts = η (Con U1)

interp :: γ ⊢ U -> γ ⊢ T
interp (Con U1) = exists (Lam ((App human (Var Get)) /\ (App (App (≥) (App height (Var Get))) θ)))

-- | RSA

-- | Pragmatic listener
l1 :: γ ⊢ (U ⟶ ((Context ⟶ R) ⟶ R))
l1 = Lam (k >>= Lam (
             factor' (App (distr (App s1 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))

-- | Pragmatic speaker
s1 :: γ ⊢ (Context ⟶ ((U ⟶ R) ⟶ R))
s1 = Lam (utts >>= Lam (
             factor' (App (distr (App l0 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))

-- | Literal listener
l0 :: γ ⊢ (U ⟶ ((Context ⟶ R) ⟶ R))
l0 = Lam (k >>= Lam (
             observe' (App (hmorph (interp (Con U1))) (Var Get)) >>
             η (Var Get)))

