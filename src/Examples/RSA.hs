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
 
normal :: Rational -> Rational -> γ ⊢ ((R ⟶ R) ⟶ R)
normal x y
  = App (Con $ General Nml) (Pair (Con $ General $ Incl x) (Con $ General $ Incl y))

uniform :: Rational -> Rational -> γ ⊢ ((R ⟶ R) ⟶ R)
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
utts = η (Con (General (Utt 2)))

utts' :: γ ⊢ ((U ⟶ R) ⟶ R)
utts' = Lam
  (App
  (App (Con (General Addi)) (App (Var Get) (Con (General (Utt 1)))))
  (App (Var Get) (Con (General (Utt 2)))))

-- >>> interp (Con $ General $ Utt 2)
-- (θ ≥ height(v))

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
s1 = Lam (utts' ⋆ Lam (
             factor' (App (distr (App l0 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))

-- | Literal listener
l0 :: γ ⊢ (U ⟶ ((Context ⟶ R) ⟶ R))
l0 = Lam (k ⋆ Lam (
             observe'
             (App (App (Con (General Interp)) (Var (Weaken Get))) (Var Get)) >>
             η (Var Get)))



-- >>> displayVs $ evalβ $ clean $ evalβ $ App l0 (u 2)
-- (λx.Uniform(⟨0.0, 100.0⟩)(λy.Normal(⟨68.0, 3.0⟩)(λz.(𝟙((y ≥ z)) * x(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, y⟩, human⟩, (λu.z)⟩, v⟩)))))

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.((Uniform(⟨0.0, 100.0⟩)(λz.Normal(⟨68.0, 3.0⟩)(λu.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩ ≐ x)))) * y(U1)) + (Uniform(⟨0.0, 100.0⟩)(λz.Normal(⟨68.0, 3.0⟩)(λu.(𝟙(⟦U2⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩ ≐ x)))) * y(U2)))))

-- >>> displayVs $ evalβ $ clean $ evalβ $ lower $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Uniform(⟨0.0, 100.0⟩)(λx.Normal(⟨68.0, 3.0⟩)(λy.((Uniform(⟨0.0, 100.0⟩)(λz.Normal(⟨68.0, 3.0⟩)(λu.(𝟙((u ≥ z)) * ((z ≐ x) * (u ≐ y))))) + (Uniform(⟨0.0, 100.0⟩)(λz.Normal(⟨68.0, 3.0⟩)(λu.(𝟙((z ≥ u)) * ((z ≐ x) * (u ≐ y))))) * 0.0)) * y)))

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1.0

-- >>> normalise $ evalP $ normalForm $ clean $ evalβ $ lower $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- (integrate(integrate(((1.0e-4 * y)) * ((1.7683882565766154e-2 * exp(-513.7777777777778 + (-5.555555555555555e-2 * y*y) + (7.555555555555555 * y) + (-5.555555555555555e-2 * y*y) + (7.555555555555555 * y)))), y, max(x, -inf), inf), x, max(0.0, max(0.0, -inf)), min(100.0, min(100.0, inf)))) + (integrate(integrate(0, y, -inf, min(x, inf)), x, max(0.0, max(0.0, -inf)), min(100.0, min(100.0, inf))))

-- >>> mathematica $ expectedValue $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- ((Integrate[Integrate[((1 / 10000 * y)) * ((1 / 9 * Exp[((-4624) / 9 + ((-1) / 18 * y*y) + (68 / 9 * y) + ((-1) / 18 * y*y) + (68 / 9 * y))])), {y, Max[x, -Infinity], Infinity}], {x, Max[0 / 1, Max[0 / 1, -Infinity]], Min[100 / 1, Min[100 / 1, Infinity]]}]) + (Integrate[Integrate[0, {y, -Infinity, Min[x, Infinity]}], {x, Max[0 / 1, Max[0 / 1, -Infinity]], Min[100 / 1, Min[100 / 1, Infinity]]}])) / ((Integrate[Integrate[(1 / 10000) * ((1 / 9 * Exp[((-4624) / 9 + ((-1) / 18 * y*y) + (68 / 9 * y) + ((-1) / 18 * y*y) + (68 / 9 * y))])), {y, Max[x, -Infinity], Infinity}], {x, Max[0 / 1, Max[0 / 1, -Infinity]], Min[100 / 1, Min[100 / 1, Infinity]]}]) + (Integrate[Integrate[0, {y, -Infinity, Min[x, Infinity]}], {x, Max[0 / 1, Max[0 / 1, -Infinity]], Min[100 / 1, Min[100 / 1, Infinity]]}]))
