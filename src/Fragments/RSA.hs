{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Fragments.RSA where

import Prelude hiding (Monad(..))
import TLC.Terms

factor :: γ ⊢ (R ⟶ ((Unit ⟶ R) ⟶ R))
factor = Lam (Lam (App (App (Con (Rl Mult)) (Var (Weaken Get))) (App (Var Get) TT)))
factor' x = App factor x

observe :: γ ⊢ (T ⟶ ((Unit ⟶ R) ⟶ R))
observe = Lam (App factor (App (Con (Rl Indi)) (Var Get)))
observe' φ = App observe φ
 
normal :: Double -> Double -> γ ⊢ ((R ⟶ R) ⟶ R)
normal x y = App (Con $ Rl Nml) (Pair (Con $ Rl $ Incl x) (Con $ Rl $ Incl y))

uniform :: Double -> Double -> γ ⊢ ((R ⟶ R) ⟶ R)
uniform x y = App (Con $ Rl Uni) (Pair (Con $ Rl $ Incl x) (Con $ Rl $ Incl y))

u i = Con $ Special $ Utt i

vlad = Con $ Special Vlad
height = Con $ Special Height
human = Con $ Special Human
θ = Con $ Special Theta
(≥) = Con $ Special GTE
emp = Con $ Special Empty
upd = Con $ Special Upd
sel = Con $ Special Sel

(/\) :: γ ⊢ T -> γ ⊢ T -> γ ⊢ T
p /\ q = App (App (Con (Logical And)) p) q

(\/) :: γ ⊢ T -> γ ⊢ T -> γ ⊢ T
p \/ q = App (App (Con (Logical Or)) p) q

(-->) :: γ ⊢ T -> γ ⊢ T -> γ ⊢ T
p --> q = App (App (Con (Logical Imp)) p) q

exists :: γ ⊢ (α ⟶ T) -> γ ⊢ T
exists φ = App (Con (Logical Exists)) φ

distr :: γ ⊢ ((α ⟶ R) ⟶ R) -> γ ⊢ (α ⟶ R)
distr p = App (Con (Rl Distr)) p

k :: γ ⊢ ((Context ⟶ R) ⟶ R)
k = uniform 0 100 >>= Lam (normal 68 3 >>= Lam (η (Pair vlad (Pair (Lam (Var (Weaken Get))) (Pair human (Pair (Var (Weaken Get)) (Pair (≥) (Pair emp (Pair upd (Pair sel TT))))))))))

utts :: γ ⊢ ((U ⟶ R) ⟶ R)
utts = η (Con (Special (Utt 1)))

interp :: γ ⊢ U -> γ ⊢ T
interp (Con (Special (Utt 1))) = App (App (≥) (App height vlad)) θ

-- >>> interp (Con $ Special $ Utt 1)
-- ∃(λ((human(x) ∧ (height(x) ≥ θ))))

lower :: γ ⊢ ((R ⟶ R) ⟶ R) -> γ ⊢ R
lower m = App m (Lam (Var Get))

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



-- >>> evalβ $ lower $ App l1 (u 1) >>= Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Uniform(⟨0.0, 100.0⟩)(λ(Normal(⟨68.0, 3.0⟩)(λ((Distr(λ((Distr(λ(Uniform(⟨0.0, 100.0⟩)(λ(Normal(⟨68.0, 3.0⟩)(λ((𝟙((x ≥ x')) * x''(⟨v, ⟨λ(x'), ⟨human, ⟨x', ⟨(≥), ⟨ε, ⟨(∷), ⟨sel, ⋄⟩⟩⟩⟩⟩⟩⟩⟩))))))))(⟨v, ⟨λ(x''), ⟨human, ⟨x'', ⟨(≥), ⟨ε, ⟨(∷), ⟨sel, ⋄⟩⟩⟩⟩⟩⟩⟩⟩) * x(U1))))(U1) * x)))))
