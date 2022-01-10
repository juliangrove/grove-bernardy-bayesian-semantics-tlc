{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Examples.RSA where

import Prelude hiding (Monad(..))
import Models.Optimizer
import TLC.Terms

factor :: γ ⊢ (R ⟶ ((Unit ⟶ R) ⟶ R))
factor
  = Lam (Lam (App (App (Con (General Mult)) (Var (Weaken Get))) (App (Var Get) TT)))
factor' x = App factor x

observe :: γ ⊢ (T ⟶ ((Unit ⟶ R) ⟶ R))
observe = Lam (App factor (App (Con (General Indi)) (Var Get)))
observe' φ = App observe φ
 
normal :: Double -> Double -> γ ⊢ ((R ⟶ R) ⟶ R)
normal x y
  = App (Con $ General Nml) (Pair (Con $ General $ Incl x) (Con $ General $ Incl y))

uniform :: Double -> Double -> γ ⊢ ((R ⟶ R) ⟶ R)
uniform x y
  = App (Con $ General Uni) (Pair (Con $ General $ Incl x) (Con $ General $ Incl y))

distr :: Equality α => γ ⊢ ((α ⟶ R) ⟶ R) -> γ ⊢ (α ⟶ R)
distr p = Lam (App (wkn p) (Lam ((Var Get) ≐ (Var (Weaken Get)))))

k :: γ ⊢ ((Context ⟶ R) ⟶ R)
k = uniform 0 100
    ⋆ Lam (normal 68 3
           ⋆ Lam (
              η (Pair
                 (Pair
                  (Pair
                   (Pair
                    (Pair
                     (Pair
                      (Pair
                       (Pair TT sel)
                       upd)
                      emp)
                     (≥))
                    (Var (Weaken Get)))
                   human)
                  (Lam (Var (Weaken Get))))
                 vlad)))

utts :: γ ⊢ ((U ⟶ R) ⟶ R)
utts = η (Con (General (Utt 1)))

-- >>> interp (Con $ Special $ Utt 2)
-- ∃(λ((height(x) ≥ θ)))

lower :: γ ⊢ ((R ⟶ R) ⟶ R) -> γ ⊢ R
lower m = App m (Lam (Var Get))

measure :: γ ⊢ ((R ⟶ R) ⟶ R) -> γ ⊢ R
measure m = App m (Lam (Con $ General $ Incl 1))

expectedValue :: γ ⊢ ((R ⟶ R) ⟶ R) -> γ ⊢ R
expectedValue m = App (App (Con $ General $ Divi) (lower m)) (measure m)

-- | RSA

-- | Pragmatic listener
l1 :: γ ⊢ (U ⟶ ((Context ⟶ R) ⟶ R))
l1 = Lam (k ⋆ Lam (
             factor' (App (distr (App s1 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))
     
-- | Pragmatic speaker
s1 :: γ ⊢ (Context ⟶ ((U ⟶ R) ⟶ R))
s1 = Lam (utts ⋆ Lam (
             factor' (App (distr (App l0 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))

-- | Literal listener
l0 :: γ ⊢ (U ⟶ ((Context ⟶ R) ⟶ R))
l0 = Lam (k ⋆ Lam (
             observe'
             (App (App (Con (General Interp)) (Var (Weaken Get))) (Var Get)) >>
             η (Var Get)))



-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.(Uniform(⟨0.0, 100.0⟩)(λz.Normal(⟨68.0, 3.0⟩)(λu.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩ ≐ x)))) * y(U1))))

-- >>> displayVs $ evalβ $ clean $ evalβ $ measure $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Uniform(⟨0.0, 100.0⟩)(λx.Normal(⟨68.0, 3.0⟩)(λy.Uniform(⟨0.0, 100.0⟩)(λz.Normal(⟨68.0, 3.0⟩)(λu.(𝟙((u ≥ z)) * ((z ≐ x) * (u ≐ y)))))))

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1.0

-- >>> evalP $ normalForm $ evalβ $ clean $ evalβ $ measure $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- integrate(integrate(integrate(integrate(𝟙((-1.0 * u) + z ≤ 0) * (z + (-1.0 * x) ≐ 0) * (u + (-1.0 * y) ≐ 0) * (1.0e-4) * ((1.7683882565766154e-2 * exp(-513.7777777777778 + (-5.555555555555555e-2 * y*y) + (7.555555555555555 * y) + (-5.555555555555555e-2 * u^2.0) + (7.555555555555555 * u)))), u), z, max(0.0, -inf), min(100.0, inf)), y), x, max(0.0, -inf), min(100.0, inf))

-- >>> :set -XDataKinds
-- >>>  maxima $ expectedValue $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- (integrate(integrate(((1.0e-4 * y)) * ((1.7683882565766154e-2 * exp(-513.7777777777778 + (-5.555555555555555e-2 * y*y) + (7.555555555555555 * y) + (-5.555555555555555e-2 * y*y) + (7.555555555555555 * y)))), y, max(x, -inf), inf), x, max(0.0, max(0.0, -inf)), min(100.0, min(100.0, inf)))) / (integrate(integrate((1.0e-4) * ((1.7683882565766154e-2 * exp(-513.7777777777778 + (-5.555555555555555e-2 * y*y) + (7.555555555555555 * y) + (-5.555555555555555e-2 * y*y) + (7.555555555555555 * y)))), y, max(x, -inf), inf), x, max(0.0, max(0.0, -inf)), min(100.0, min(100.0, inf))))
