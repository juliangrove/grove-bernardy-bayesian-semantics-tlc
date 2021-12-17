{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module RSA where

import Prelude hiding (Monad(..))
import TLC.RN
import TLC.Terms

factor :: γ ⊢ (R ⟶ ((Unit ⟶ R) ⟶ R))
factor = Lam (Lam (App (App (Con (Rl Mult)) (Var (Weaken Get))) (App (Var Get) TT)))
factor' x = App factor x

observe :: γ ⊢ (T ⟶ ((Unit ⟶ R) ⟶ R))
observe = Lam (App factor (App (Con (Rl Indi)) (Var Get)))
observe' φ = App observe φ
 
normal :: γ ⊢ ((R × R) ⟶ ((R ⟶ R) ⟶ R))
normal = Con $ Rl Nml

height = Con $ Special Height
human = Con $ Special Human
θ = Con $ Special Theta
(≥) = Con $ Special GTE
emp = Con $ Special Empty
upd = Con $ Special Upd
sel = Con $ Special Sel

(/\) :: γ ⊢ T -> γ ⊢ T -> γ ⊢ T
p /\ q = App (App (Con (Logical And)) p) q

exists :: γ ⊢ (α ⟶ T) -> γ ⊢ T
exists φ = App (Con (Logical Exists)) φ

distr :: γ ⊢ ((α ⟶ R) ⟶ R) -> γ ⊢ (α ⟶ R)
distr p = App (Con (Rl Distr)) p

k :: γ ⊢ ((Context ⟶ R) ⟶ R)
k = (App normal (Pair (Con $ Rl $ Incl 68) (Con $ Rl $ Incl 3))) >>= Lam (η (Pair height (Pair human (Pair (Var Get) (Pair (≥) (Pair emp (Pair upd (Pair sel TT))))))))

utts :: γ ⊢ ((U ⟶ R) ⟶ R)
utts = η (Con (Special (Utt 1)))

interp :: γ ⊢ U -> γ ⊢ T
interp (Con (Special (Utt 1))) = exists (Lam ((App human (Var Get)) /\ (App (App (≥) (App height (Var Get))) θ)))

-- >>> interp (Con $ Special $ Utt 1)
-- ∃(λ(human(x) ∧ (height(x) ≥ θ)))

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
             observe' (App (hmorph (interp (Con (Special (Utt 1))))) (Var Get)) >>
             η (Var Get)))

