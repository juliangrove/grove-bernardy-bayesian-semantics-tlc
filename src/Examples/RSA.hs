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

lesbegue :: γ ⊢ ((R ⟶ R) ⟶ R)
lesbegue = Con $ General Les

distr :: Equality α => γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ (α ⟶ 'R)
distr p = Lam (App (wkn p) (Lam ((Var Get) ≐ (Var (Weaken Get)))))

k :: γ ⊢ ((Context ⟶ R) ⟶ R)
k = normal 68 3
  ⋆ Lam (normal 68 3
         ⋆ Lam
          (η (Pair
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

utts' :: γ ⊢ ((U ⟶ R) ⟶ R)
utts' = Lam
  (App
  (App (Con (General Addi)) (App (App (Con (General Mult)) (Con (General (Incl (1 % 2))))) (App (Var Get) (Con (General (Utt 1))))))
  (App (App (Con (General Mult)) (Con (General (Incl (1 % 2))))) (App (Var Get) (Con (General (Utt 2))))))

-- utts'' :: γ ⊢ ((U ⟶ R) ⟶ R)
-- utts'' = uniform 0 100 ⋆ Lam (η (u (Var Get)))

updctx :: γ ⊢ Context -> γ ⊢ (R ⟶ Context)
updctx k = Lam (Pair
                (Pair (Fst (Fst $ wkn k))
                 (Lam (Var (Weaken Get))))
                (π Get $ wkn k))

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

l2 :: γ ⊢ (U ⟶ ((Context ⟶ 'R) ⟶ 'R))
l2 = Lam (k ⋆ Lam (
             factor' (App (distr (App s2 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))

l3 :: γ ⊢ (U ⟶ ((Context ⟶ 'R) ⟶ 'R))
l3 = Lam (k ⋆ Lam (
             factor' (App (distr (App s3 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))
 
     
-- | Pragmatic speaker
s1 :: γ ⊢ (Context ⟶ (('U ⟶ 'R) ⟶ 'R))
s1 = Lam (utts' ⋆ Lam (
             factor'
             (App (App (Con (General Mult)) (App (distr (App l0 (Var Get))) (Var (Weaken Get)))) (App (distr (App l0 (Var Get))) (Var (Weaken Get)))) >>
             η (Var Get)))

s2 :: γ ⊢ (Context ⟶ (('U ⟶ 'R) ⟶ 'R))
s2 = Lam (utts' ⋆ Lam (
             factor' (App (distr (App l1 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))

s3 :: γ ⊢ (Context ⟶ (('U ⟶ 'R) ⟶ 'R))
s3 = Lam (utts' ⋆ Lam (
             factor' (App (distr (App l2 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))

-- | Literal listener
l0 :: γ ⊢ ('U ⟶ ((Context ⟶ 'R) ⟶ 'R))
l0 = Lam (k ⋆ Lam (
             observe'
             (App (App (Con (General Interp)) (Var (Weaken Get))) (Var Get)) >>
             η (Var Get)))

l0Distr :: γ ⊢ ('R ⟶ 'R)
l0Distr = distr $ normalize $ App l0 (u 2) ⋆ Lam (η (App (hmorph (height `App` vlad)) (Var Get)))

l1Distr :: γ ⊢ ('R ⟶ 'R)
l1Distr = distr $ normalize $ App l1 (u 2) ⋆ Lam (η (App (hmorph (height `App` vlad)) (Var Get)))

-- >>> interp (u 2)
-- (θ ≥ height(v))

test :: γ ⊢ ('R ⟶ 'R)
test = distr $ uniform 0 10 ⋆ Lam (uniform 0 10 ⋆ Lam (η ((Con (General Addi)) `App` (Var Get) `App` (Var (Weaken Get)))))

-- >>>  displayVs $ evalβ $ clean $ evalβ test
-- (λx.Uniform(⟨0, 10⟩)(λy.Uniform(⟨0, 10⟩)(λz.((z + y) ≐ x))))

utility' :: γ ⊢ (Context ⟶ ('U ⟶ 'R))
utility' = Lam (distr $ normalize $ App s1 (Var Get))

utility :: Int -> γ ⊢ (Context ⟶ 'R)
utility n = Lam (App (App utility' (Var Get)) (u n))

exp1 = Lam (App k $ Lam (App (utility 1) (App (updctx (Var Get)) (Var (Weaken Get)))))

exp2 = Lam (App k $ Lam (App (utility 2) (App (updctx (Var Get)) (Var (Weaken Get)))))

-- >>> mathematicaFun exp2
-- Boole[-1000 ≤ 0] * Boole[-1000 ≤ 0] * Boole[-1000 ≤ 0] * Boole[-1000 + x ≤ 0] * Boole[-1000 + x ≤ 0] * Boole[-1000 + x ≤ 0] * Integrate[Integrate[((((5000000000000000 / 565486677645711363147321) * Exp[((-4624 / 9) + ((-1 / 18) * z^2) + ((68 / 9) * z) + ((-1 / 18) * x^2) + ((68 / 9) * x))]))) / ((Boole[(-1 * x) ≤ 0] * Boole[-1000 + y ≤ 0] * Boole[y + (-1 * x) ≤ 0] * Boole[(-1 * y) ≤ 0] * (((50000000 / 751988482389) * Exp[((-2312 / 9) + ((-1 / 18) * x^2) + ((68 / 9) * x))]))) + (Boole[-1000 + x ≤ 0] * Boole[-1000 + y ≤ 0] * Boole[(-1 * y) ≤ 0] * Boole[x + (-1 * y) ≤ 0] * (((50000000 / 751988482389) * Exp[((-2312 / 9) + ((-1 / 18) * x^2) + ((68 / 9) * x))])))), {z, -Infinity, Infinity}], {y, Max[x, Max[0, Max[0, -Infinity]]], Min[1000, Min[1000, Infinity]]}]

-- >>> displayVs $ evalβ $ l1
-- (λx.(λy.Normal(⟨50, 4⟩)(λz.Normal(⟨68, 3⟩)(λu.((((1 / 2) * (Normal(⟨50, 4⟩)(λv.Normal(⟨68, 3⟩)(λw.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * (U1 ≐ x))) + ((1 / 2) * (Normal(⟨50, 4⟩)(λv.Normal(⟨68, 3⟩)(λw.(𝟙(⟦U2⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, v⟩, human⟩, (λx1.w)⟩, v⟩ ≐ ⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λx1.u)⟩, v⟩)))) * (U2 ≐ x)))) * y(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩))))))

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.(((1 / 2) * (Uniform(⟨50, 100⟩)(λz.Normal(⟨68, 3⟩)(λu.(𝟙(⟦U1⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩ ≐ x)))) * y(U1))) + ((1 / 2) * (Uniform(⟨50, 100⟩)(λz.Normal(⟨68, 3⟩)(λu.(𝟙(⟦U2⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, z⟩, human⟩, (λv.u)⟩, v⟩ ≐ x)))) * y(U2))))))

someExample :: γ ⊢ ('R ⟶ 'R)
someExample = distr $ normalize $ App l1 (u 1) ⋆ Lam (η (App (hmorph (θ)) (Var Get)))

-- >>> :t someExample
-- someExample :: γ ⊢ ('R ⟶ 'R)
                                                    
-- >>> mathematicaFun $ distr $ normalize $ App l1 (u 1) ⋆ Lam (η (App (hmorph (θ)) (Var Get)))
-- Boole[-1000 ≤ 0] * Boole[(-1 * x) ≤ 0] * Boole[-1000 + x ≤ 0] * Boole[-1000 + x ≤ 0] * Boole[(-1 * x) ≤ 0] * Integrate[((((5000000000000000 / 565486677645711363147321) * Exp[((-4624 / 9) + ((-1 / 18) * y^2) + ((68 / 9) * y) + ((-1 / 18) * y^2) + ((68 / 9) * y))]))) / (Boole[-1000 ≤ 0] * Boole[-1000 ≤ 0] * Boole[-1000 ≤ 0] * Integrate[Integrate[(((5000000000000000 / 565486677645711363147321) * Exp[((-4624 / 9) + ((-1 / 18) * u^2) + ((68 / 9) * u) + ((-1 / 18) * u^2) + ((68 / 9) * u))])), {u, Max[0, Max[z, -Infinity]], Infinity}], {z, Max[0, Max[0, -Infinity]], Min[1000, Min[1000, Infinity]]}]), {y, Max[0, Max[x, -Infinity]], Infinity}]

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1 / 1

-- >>> :set -XLambdaCase -XEmptyCase -XTypeApplications -XDataKinds
-- >>> mathematicaFun $ distr $ normalize $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Integrate[((((10000000000000000000000 / 565486677645711363147321) * Exp[((-4624 / 9) + ((-1 / 18) * y^2) + ((68 / 9) * y) + ((-1 / 18) * x^2) + ((68 / 9) * x))]))) / (Integrate[Integrate[(((10000000000000000000000 / 565486677645711363147321) * Exp[((-4624 / 9) + ((-1 / 18) * z^2) + ((68 / 9) * z) + ((-1 / 18) * u^2) + ((68 / 9) * u))])), {u, Max[z, -Infinity], Infinity}], {z, -Infinity, Infinity}]), {y, -Infinity, Min[x, Infinity]}]

-- >>> mathematicaFun $ distr $ App l1 (u 1) ⋆ Lam (η (App (hmorph θ) (Var Get)))
-- Integrate[(((500000000000000000000000000000000000000000000000000000000000000000 / 180828605599075492739528986266187435349307646686115423640694328590157161) * Exp[((-4624 / 3) + ((-1 / 18) * x^2) + ((68 / 9) * x) + ((-1 / 18) * y^2) + ((68 / 9) * y) + ((-1 / 18) * x^2) + ((68 / 9) * x) + ((-1 / 18) * y^2) + ((68 / 9) * y) + ((-1 / 18) * x^2) + ((68 / 9) * x) + ((-1 / 18) * y^2) + ((68 / 9) * y))])), {y, Max[x, Max[x, -Infinity]], Infinity}]

-- >>> :set -XTypeOperators
-- >>> maximaPrint $ (expectedValue $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get))) :: 'Unit ⊢ 'R)
-- <interactive>:628:2-12: error:
--     Variable not in scope: maximaPrint :: ('Unit ⊢ 'R) -> t

-- >>> mathematicaFun $ evalβ $ distr $ normal 0 10 ⋆ Lam (normal 0 10 ⋆ Lam (η (App (App (Con (General Addi)) (Var Get)) (Var (Weaken Get)))))
-- Integrate[((100000000000000000000 / 62831853071745707016369)), {y, -Infinity, Infinity}]

-- >>> distr $ normal 0 1
-- λ(Normal(⟨0, 1⟩)(λ((x ≐ x'))))
