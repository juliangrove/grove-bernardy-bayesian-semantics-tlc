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
k = uniform (-1000) 1000
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

-- >>> interp (u 2)
-- (θ ≥ height(v))

test :: γ ⊢ ('R ⟶ 'R)
test = distr $ uniform 0 10 ⋆ Lam (uniform 0 10 ⋆ Lam (η ((Con (General Addi)) `App` (Var Get) `App` (Var (Weaken Get)))))

-- >>>  displayVs $ evalβ $ clean $ evalβ test
-- (λx.Uniform(⟨0, 10⟩)(λy.Uniform(⟨0, 10⟩)(λz.((z + y) ≐ x))))

-- >>> mathematicaFun test
-- 𝟙(-20 + x ≤ 0) * 𝟙(-10 + x + (-1 * x) ≤ 0) * 𝟙((-1 * x) ≤ 0) * Integrate[((1 / 100)), {y, Max[-10 + x, Max[0, -Infinity]], Min[x, Min[10, Infinity]]}]

-- >>> displayVs $ evalβ $ l1
-- (λx.(λy.Uniform(⟨50, 100⟩)(λz.Normal(⟨68, 3⟩)(λu.((((1 / 2) * (Uniform(⟨50, 100⟩)(λv.Normal(⟨68, 3⟩)(λw.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * (U1 ≐ x))) + ((1 / 2) * (Uniform(⟨50, 100⟩)(λv.Normal(⟨68, 3⟩)(λw.(𝟙(⟦U2⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * (U2 ≐ x)))) * y(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩))))))

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.(((1 / 2) * (Uniform(⟨50, 100⟩)(λz.Normal(⟨68, 3⟩)(λu.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩ ≐ x)))) * y(U1))) + ((1 / 2) * (Uniform(⟨50, 100⟩)(λz.Normal(⟨68, 3⟩)(λu.(𝟙(⟦U2⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩ ≐ x)))) * y(U2))))))

-- >>> mathematica $ expectedValue $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- (Integrate[Integrate[(((1 / 2000) * y)) * (((100000000000 / 751988482389) * Exp[((-2312 / 9) + ((-1 / 18) * y^2) + ((68 / 9) * y))])), {y, Max[x, -Infinity], Infinity}], {x, Max[-1000, -Infinity], Min[1000, Infinity]}]) / (Integrate[Integrate[((1 / 2000)) * (((100000000000 / 751988482389) * Exp[((-2312 / 9) + ((-1 / 18) * y^2) + ((68 / 9) * y))])), {y, Max[x, -Infinity], Infinity}], {x, Max[-1000, -Infinity], Min[1000, Infinity]}])

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1 / 1

-- >>> :set -XLambdaCase -XEmptyCase -XTypeApplications -XDataKinds
-- >>> mathematica $ expectedValue $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- ((Integrate[Integrate[(((1 / 8000000) * y)) * (((10000000000000000000000 / 565486677645711363147321) * Exp[((-4624 / 9) + ((-1 / 18) * y*y) + ((68 / 9) * y) + ((-1 / 18) * y*y) + ((68 / 9) * y))])), {y, Max[-1000, Max[x, -Infinity]], Infinity}], {x, Max[-1000, Max[-1000, -Infinity]], Min[1000, Min[1000, Infinity]]}]) + (Integrate[Integrate[0, {y, -Infinity, Min[1000, Min[x, Infinity]]}], {x, Max[-1000, Max[-1000, -Infinity]], Min[1000, Min[1000, Infinity]]}])) / ((Integrate[Integrate[((1 / 8000000)) * (((10000000000000000000000 / 565486677645711363147321) * Exp[((-4624 / 9) + ((-1 / 18) * y*y) + ((68 / 9) * y) + ((-1 / 18) * y*y) + ((68 / 9) * y))])), {y, Max[-1000, Max[x, -Infinity]], Infinity}], {x, Max[-1000, Max[-1000, -Infinity]], Min[1000, Min[1000, Infinity]]}]) + (Integrate[Integrate[0, {y, -Infinity, Min[1000, Min[x, Infinity]]}], {x, Max[-1000, Max[-1000, -Infinity]], Min[1000, Min[1000, Infinity]]}]))

-- >>> mathematicaFun $ distr $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- (Integrate[((1 / 8000000)) * (((10000000000000000000000 / 565486677645711363147321) * Exp[((-4624 / 9) + ((-1 / 18) * x*x) + ((68 / 9) * x) + ((-1 / 18) * x*x) + ((68 / 9) * x))])), {y, Max[-1000, Max[-1000, -Infinity]], Min[1000, Min[x, Min[1000, Infinity]]]}]) + (Integrate[0, {y, Max[-1000, Max[x, Max[-1000, -Infinity]]], Min[1000, Min[1000, Infinity]]}])

-- >>> mathematicaFun $ evalβ $ distr $ normal 0 10 ⋆ Lam (normal 0 10 ⋆ Lam (η (App (App (Con (General Addi)) (Var Get)) (Var (Weaken Get)))))
-- Integrate[(((100000000000000000000 / 62831853071745707016369) * Exp[(((-1 / 200) * y*y) + ((-1 / 200) * y*y) + ((1 / 200) * x*y) + ((1 / 200) * y*x) + ((-1 / 200) * x*x))])), {y}]

-- >>> distr $ normal 0 1
-- λ(Normal(⟨0, 1⟩)(λ((x ≐ x'))))
