{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Examples.RSA where

import Data.Ratio
import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
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
k = uniform 0 100
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

utts'' :: γ ⊢ ((U ⟶ R) ⟶ R)
utts'' = uniform 0 100 ⋆ Lam (η (u' (Var Get)))

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

measure :: γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ 'R
measure m = App m (Lam one)

normalize :: γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ ((α ⟶ 'R) ⟶ 'R)
normalize m = m ⋆ Lam (factor' (recip $ measure $ wkn m) >> η (Var Get))

expectedValue :: γ ⊢ (('R ⟶ 'R) ⟶ 'R) -> γ ⊢ 'R
expectedValue m = lower m / measure m


-- | RSA

-- | Pragmatic listener
l1 :: γ ⊢ (U ⟶ ((Context ⟶ R) ⟶ R))
l1 = Lam (k ⋆ Lam (
             factor' (App (distr (App s1 (Var Get))) (Var (Weaken Get))) >>
             η (Var Get)))
    
-- | Pragmatic speaker
s1' :: Integer -> γ ⊢ (Context ⟶ (('U ⟶ 'R) ⟶ 'R))
s1' α = Lam (utts'' ⋆ Lam (
             factor'
             ((App (distr (App l0 (Var Get))) (Var (Weaken Get))) ^+ α) >>
             η (Var Get)))

s1 :: γ ⊢ (Context ⟶ (('U ⟶ 'R) ⟶ 'R))
s1 = s1' 1

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

-- >>> interp (u' (Con $ General $ Incl $ 2 % 23))
-- (height(v) ≥ (2 / 23))

test :: γ ⊢ ('R ⟶ 'R)
test = distr $ uniform 0 10 ⋆ Lam (uniform 0 10 ⋆ Lam (η ((Con (General Addi)) `App` (Var Get) `App` (Var (Weaken Get)))))

-- >>>  displayVs $ evalβ $ clean $ evalβ test
-- (λx.Uniform(⟨0, 10⟩)(λy.Uniform(⟨0, 10⟩)(λz.((z + y) ≐ x))))

utility' :: γ ⊢ (Context ⟶ ('U ⟶ 'R))
utility' = Lam (distr $ normalize $ App s1 (Var Get))

utility :: γ ⊢ ('R ⟶ ('R ⟶ 'R))
utility = Lam (Lam (expectedValue $ k ⋆ Lam (η $ App (distr $ App s1 (App (updctx (Var Get)) (Var (Weaken (Weaken Get))))) (u' (Var (Weaken Get))))))

-- exp1 = Lam (App k $ Lam (App (utility 1) (App (updctx (Var Get)) (Var (Weaken Get)))))

-- exp2 = Lam (App k $ Lam (App (utility 2) (App (updctx (Var Get)) (Var (Weaken Get)))))

-- >>> mathematicaFun' utility
-- Boole[-100 ≤ 0] * Boole[(-1 * x) ≤ 0] * Boole[-100 + x ≤ 0] * Boole[(-1 * y) + x ≤ 0] * (Integrate[Integrate[(((10000000000000000 / 565486677645711363147321) * Exp[((-4624 / 9) + ((-1 / 18) * u^2) + ((68 / 9) * u) + ((-1 / 18) * y^2) + ((68 / 9) * y))])), {u, -Infinity, Infinity}], {z, 0, 100}]) / (Integrate[Integrate[(((1000000000 / 751988482389) * Exp[((-2312 / 9) + ((-1 / 18) * u^2) + ((68 / 9) * u))])), {u, -Infinity, Infinity}], {z, 0, 100}])

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.Uniform(⟨0, 100⟩)(λz.(Uniform(⟨0, 100⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙(⟦U(z)⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩ ≐ x)))) * y(U(z))))))

test1 = mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))

-- >>> test1
-- Boole[65 + (-1 * x) ≤ 0] * Integrate[(((1000000000 / 751988482389) * Exp[((-2312 / 9) + ((-1 / 18) * x^2) + ((68 / 9) * x))])), {y, 0, 100}]
        
-- >>> mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Boole[65 + (-1 * x) ≤ 0] * Integrate[(((1000000000 / 751988482389) * Exp[((-2312 / 9) + ((-1 / 18) * x^2) + ((68 / 9) * x))])), {y, 0, 100}]

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1

-- >>> :set -XLambdaCase -XEmptyCase -XTypeApplications -XDataKinds
-- >>> latexFun $ distr $ normalize $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Boole[(-1 * x) ≤ 0] * \int_{0}^{Min[x, 100]}\frac{(((1000000000 / 751988482389) * e^{((-2312 / 9) + ((-1 / 18) * x^2) + ((68 / 9) * x))}))}{\int_{0}^{100}\int_{z}^{\infty}(((1000000000 / 751988482389) * e^{((-2312 / 9) + ((-1 / 18) * u^2) + ((68 / 9) * u))}))\,du\,dz}\,dy

-- >>> mathematicaFun $ distr $ App l1 (u 1) ⋆ Lam (η (App (hmorph θ) (Var Get)))
-- (0)

-- >>> mathematicaFun $ evalβ $ distr $ normal 0 10 ⋆ Lam (normal 0 10 ⋆ Lam (η (App (App (Con (General Addi)) (Var Get)) (Var (Weaken Get)))))
-- Integrate[(((100000000000000000000 / 62831853071745707016369) * Exp[(((-1 / 100) * y^2) + ((1 / 200) * y * x) + ((1 / 200) * x * y) + ((-1 / 200) * x^2))])), {y, -Infinity, Infinity}]
