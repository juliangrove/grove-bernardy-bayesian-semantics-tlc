{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Examples.RSA where

import Data.Ratio
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

distr :: Equality α => γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ (α ⟶ 'R)
distr p = Lam (App (wkn p) (Lam ((Var Get) ≐ (Var (Weaken Get)))))

k :: γ ⊢ ((Context ⟶ R) ⟶ R)
k = uniform 80 90
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
  (App (Con (General Addi)) (App (App (Con (General Mult)) (Con (General (Incl (1 % 2))))) (App (Var Get) (Con (General (Utt 1))))))
  (App (App (Con (General Mult)) (Con (General (Incl (1 % 2))))) (App (Var Get) (Con (General (Utt 2))))))

-- >>> displayVs utts'
-- (λx.((3 / 4 * x(U1)) + (1 / 4 * x(U2))))

-- >>> interp (Con $ General $ Utt 1)
-- (height(v) ≥ θ)

lower :: γ ⊢ ((R ⟶ R) ⟶ R) -> γ ⊢ R
lower m = App m (Lam (Var Get))

measure :: γ ⊢ ((α ⟶ R) ⟶ R) -> γ ⊢ R
measure m = App m (Lam (Con $ General $ Incl 1))

recipr :: γ ⊢ R -> γ ⊢ R
recipr m = App (App (Con (General Divi)) (Con (General (Incl (1 % 1))))) m

normalize :: γ ⊢ ((α ⟶ R) ⟶ R) -> γ ⊢ ((α ⟶ R) ⟶ R)
normalize m = m ⋆ Lam (factor' (recipr $ measure $ wkn m) >> η (Var Get))

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

l0Distr :: γ ⊢ ('R ⟶ 'R)
l0Distr = distr $ App l0 (u 1) ⋆ Lam (η (App (hmorph (height `App` vlad)) (Var Get)))


-- >>>  displayVs $ evalβ l0Distr
-- (λx.Uniform(⟨80 / 1, 90 / 1⟩)(λy.Normal(⟨68 / 1, 3 / 1⟩)(λz.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, y⟩, human⟩, (λu.z)⟩, v⟩)) * (z ≐ x)))))

-- >>> mathematicaFun l0Distr
-- Integrate[(1 / 10) * ((1 / 3 * Exp[((-2312) / 9 + ((-1) / 18 * x*x) + (68 / 9 * x))])), {y, (80), Min[x, 90]}]


-- >>> displayVs $ evalβ $ l1
-- (λx.(λy.Uniform(⟨0 / 1, 100 / 1⟩)(λz.Normal(⟨68 / 1, 3 / 1⟩)(λu.((((1 / 1 / (1 / 1 + 1 / 1)) * (Uniform(⟨0 / 1, 100 / 1⟩)(λv.Normal(⟨68 / 1, 3 / 1⟩)(λw.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * ((1 / 1 / (((1 / 1 / (1 / 1 + 1 / 1)) * (Uniform(⟨0 / 1, 100 / 1⟩)(λv.Normal(⟨68 / 1, 3 / 1⟩)(λw.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * 1 / 1)) + ((1 / 1 / (1 / 1 + 1 / 1)) * (Uniform(⟨0 / 1, 100 / 1⟩)(λv.Normal(⟨68 / 1, 3 / 1⟩)(λw.(𝟙(⟦U2⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * 1 / 1)))) * (U1 ≐ x)))) + ((1 / 1 / (1 / 1 + 1 / 1)) * (Uniform(⟨0 / 1, 100 / 1⟩)(λv.Normal(⟨68 / 1, 3 / 1⟩)(λw.(𝟙(⟦U2⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * ((1 / 1 / (((1 / 1 / (1 / 1 + 1 / 1)) * (Uniform(⟨0 / 1, 100 / 1⟩)(λv.Normal(⟨68 / 1, 3 / 1⟩)(λw.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * 1 / 1)) + ((1 / 1 / (1 / 1 + 1 / 1)) * (Uniform(⟨0 / 1, 100 / 1⟩)(λv.Normal(⟨68 / 1, 3 / 1⟩)(λw.(𝟙(⟦U2⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * 1 / 1)))) * (U2 ≐ x))))) * y(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩))))))

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.(((1 / 1 / (1 / 1 + 1 / 1)) * (Uniform(⟨0 / 1, 100 / 1⟩)(λz.Normal(⟨68 / 1, 3 / 1⟩)(λu.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩ ≐ x)))) * y(U1))) + ((1 / 1 / (1 / 1 + 1 / 1)) * (Uniform(⟨0 / 1, 100 / 1⟩)(λz.Normal(⟨68 / 1, 3 / 1⟩)(λu.(𝟙(⟦U2⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩ ≐ x)))) * y(U2))))))

-- >>> displayVs $ evalβ $ clean $ evalβ $ lower $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Uniform(⟨0 / 1, 100 / 1⟩)(λx.Normal(⟨68 / 1, 3 / 1⟩)(λy.(((3 / 4 * Uniform(⟨0 / 1, 100 / 1⟩)(λz.Normal(⟨68 / 1, 3 / 1⟩)(λu.(𝟙((u ≥ z)) * ((z ≐ x) * (u ≐ y)))))) + (1 / 4 * (Uniform(⟨0 / 1, 100 / 1⟩)(λz.Normal(⟨68 / 1, 3 / 1⟩)(λu.(𝟙((z ≥ u)) * ((z ≐ x) * (u ≐ y))))) * 0 / 1))) * y)))

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1 / 1

-- >>> mathematica' $ evalP $ normalForm $ clean $ evalβ $ lower $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Integrate[Integrate[(Integrate[Integrate[𝟙(((-1) / 1 * u) + z ≤ 0) * (z + ((-1) / 1 * x) ≐ 0) * (u + ((-1) / 1 * y) ≐ 0) * ((1 / 20000 * y)) * ((1 / 9 * Exp[((-4624) / 9 + ((-1) / 18 * y*y) + (68 / 9 * y) + ((-1) / 18 * u^2 / 1) + (68 / 9 * u))])), {u}], {z, Max[0 / 1, -Infinity], Min[100 / 1, Infinity]}]) + (Integrate[Integrate[𝟙(((-1) / 1 * z) + u ≤ 0) * (z + ((-1) / 1 * x) ≐ 0) * (u + ((-1) / 1 * y) ≐ 0) * 0, {u}], {z, Max[0 / 1, -Infinity], Min[100 / 1, Infinity]}]), {y}], {x, Max[0 / 1, -Infinity], Min[100 / 1, Infinity]}]

-- >>> mathematica $ lower $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Integrate[Integrate[((1 / 100 * y)) * ((1 / 3 * Exp[((-2312) / 9 + ((-1) / 18 * y^2 / 1) + (68 / 9 * y))])), {y, Max[x, -Infinity], Infinity}], {x, Max[0 / 1, -Infinity], Min[100 / 1, Infinity]}]
