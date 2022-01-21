{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Examples.RSA where

import Data.Ratio
import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Optimizer
import TLC.Terms
import TLC.Distributions


k :: γ ⊢ ((Context ⟶ R) ⟶ R)
k = uniform 0 100
<<<<<<< HEAD
  ⋆ Lam (normal 68 3
         ⋆ Lam
          (η (Pair
              (Pair
=======
    ⋆ Lam (cauchy 68 3
           ⋆ Lam
           (η (Pair
>>>>>>> 419efd9 (Split listener prob. function defs.)
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
  (App (Con (General Addi)) (App (App (Con (General Mult)) (Con (General (Incl (1 / 2))))) (App (Var Get) (Con (General (Utt 1))))))
  (App (App (Con (General Mult)) (Con (General (Incl (1 / 2))))) (App (Var Get) (Con (General (Utt 2))))))

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


-- | Pragmatic listener
l1 :: γ ⊢ (U ⟶ ((Context ⟶ R) ⟶ R))
l1 = Lam (k ⋆ Lam (
             factor' ((App (distr (App s1 (Var Get))) (Var (Weaken Get)))) >>
             η (Var Get)))

l1Distr :: γ ⊢ ('U ⟶ Context ⟶ 'R)
l1Distr = Lam (Lam (distr (l1 `App` Var (Weaken Get))) `App` Var Get)

-- | Pragmatic speaker
s1' :: Integer -> γ ⊢ (Context ⟶ (('U ⟶ 'R) ⟶ 'R))
s1' α = Lam (utts'' ⋆ Lam (
             factor'
             ((App (distr (App l0 (Var Get))) (Var (Weaken Get))) ^+ α) >>
             η (Var Get)))

s1 :: γ ⊢ (Context ⟶ ('U ⟶ 'R) ⟶ 'R)
s1 = s1' 2

s1Distr :: γ ⊢ (Context ⟶ 'U ⟶ 'R)
s1Distr = Lam (Lam (distr (s1 `App` Var (Weaken Get))) `App` Var Get)

-- | Literal listener
l0 :: γ ⊢ ('U ⟶ ((Context ⟶ 'R) ⟶ 'R))
l0 = Lam (k ⋆ Lam (
             observe'
             (App (App (Con (General Interp)) (Var (Weaken Get))) (Var Get)) >>
             η (Var Get)))

l0Distr :: γ ⊢ ('U ⟶ Context ⟶ 'R)
l0Distr = Lam (Lam (distr (l0 `App` Var (Weaken Get))) `App` Var Get)

-- l0DistrForFixedU2 :: γ ⊢ ('R ⟶ 'R)
-- l0DistrForFixedU2 = distr $ App l0 (u 2) ⋆ Lam (η (App (hmorph (height `App` vlad)) (Var Get)))

-- l1DistrForFixedU :: Int -> γ ⊢ ('R ⟶ 'R)
-- l1DistrForFixedU n = distr $ App l1 (u n) ⋆ Lam (η (App (hmorph (height `App` vlad)) (Var Get)))

test :: γ ⊢ ('R ⟶ 'R)
test = distr $ uniform 0 10 ⋆ Lam (uniform 0 10 ⋆ Lam (η ((Con (General Addi)) `App` (Var Get) `App` (Var (Weaken Get)))))

heightToCtx :: γ ⊢ ('R ⟶ Context)
heightToCtx = Lam ((Pair
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
                 (Con (General (Incl 0))))
                human)
               (Lam (Var (Weaken Get))))
              vlad))

toAtLeastHeight :: γ ⊢ ('R ⟶ 'U)
toAtLeastHeight = Con (General Utt')  

utilityl0 :: γ ⊢ ('R ⟶ 'R ⟶ 'R)
utilityl0 = Lam (Lam (l0Distr `App` (toAtLeastHeight `App` (Var (Weaken Get))) `App` (heightToCtx `App` Var Get)))

utilitys1 :: γ ⊢ ('R ⟶ 'R ⟶ 'R)
utilitys1 = Lam (Lam (s1Distr `App` (heightToCtx `App` Var Get) `App` (toAtLeastHeight `App` (Var (Weaken Get))) ))

utilityl1 :: γ ⊢ ('R ⟶ 'R ⟶ 'R)
utilityl1 = Lam (Lam (l1Distr `App` (toAtLeastHeight `App` (Var (Weaken Get))) `App` (heightToCtx `App` Var Get) ))

  -- Lam (Lam (expectedValue $ k ⋆ Lam (η $ App (distr $ App s1 (App (updctx (Var Get)) (Var (Weaken (Weaken Get))))) (u' (Var (Weaken Get))))))

-- exp1 = Lam (App k $ Lam (App (utility 1) (App (updctx (Var Get)) (Var (Weaken Get)))))

-- exp2 = Lam (App k $ Lam (App (utility 2) (App (updctx (Var Get)) (Var (Weaken Get)))))

<<<<<<< HEAD
-- >>> mathematicaFun' utilitys
-- Boole[-100 ≤ 0] * Boole[0 ≤ 0] * Boole[0 + (-1 * y) ≤ 0] * Boole[-100 + y ≤ 0] * Boole[0 + (-1 * x) + y ≤ 0] * (((1/10000*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*x + -1/18*x^2])) / (Integrate[Integrate[(1/100*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*u + -1/18*u^2]), {u, 0 + y, Infinity}], {z, 0, 100}])) / (Boole[-100 ≤ 0] * Boole[0 ≤ 0] * Boole[0 + (-1 * x) ≤ 0] * Integrate[((1/10000*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*x + -1/18*x^2])) / (Integrate[Integrate[(1/100*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*v + -1/18*v^2]), {v, 0 + z, Infinity}], {u, 0, 100}]), {z, 0, Min[0 + x, 100]}])

-- >>> mathematicaFun' utilitys
-- Boole[-100 ≤ 0] * Boole[0 ≤ 0] * Boole[0 + (-1 * y) ≤ 0] * Boole[-100 + y ≤ 0] * Boole[0 + (-1 * x) + y ≤ 0] * (((1/100*(1/100*(3*sqrt(pi))^(-1))*Exp[-2312/9 + 68/9*x + -1/18*x^2])) / (Integrate[Integrate[(1/100*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*u + -1/18*u^2]), {u, 0 + y, Infinity}], {z, 0, 100}])) / (Boole[-100 ≤ 0] * Boole[0 ≤ 0] * Boole[0 + (-1 * x) ≤ 0] * Integrate[((1/100*(1/100*(3*sqrt(pi))^(-1))*Exp[-2312/9 + 68/9*x + -1/18*x^2])) / (Integrate[Integrate[(1/100*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*v + -1/18*v^2]), {v, 0 + z, Infinity}], {u, 0, 100}]), {z, 0, Min[0 + x, 100]}])
=======
-- >>> mathematicaFun' utilitys1
-- Boole[(-100) / 1 ≤ 0] * Boole[0 / 1 ≤ 0] * Boole[0 / 1 + ((-1) / 1 * y) ≤ 0] * Boole[(-100) / 1 + y ≤ 0] * Boole[0 / 1 + ((-1) / 1 * x) + y ≤ 0] * (((Integrate[Integrate[(((1 / 1000000))) / (((14554998764081510969 / 3000000000000000) + (-53407075111026481 / 375000000000000)*u + (3141592653589793 / 3000000000000000)*u^2)), {u, 0 / 1 + y, Infinity}], {z, 0 / 1, 100 / 1}]) / (((14554998764081510969 / 3000000000000000) + (-53407075111026481 / 375000000000000)*x + (3141592653589793 / 3000000000000000)*x^2))) / (Boole[0 / 1 ≤ 0] * Boole[(-100) / 1 ≤ 0] * Boole[0 / 1 + ((-1) / 1 * x) + y ≤ 0] * (Integrate[Integrate[(((1 / 10000))) / (((14554998764081510969 / 3000000000000000) + (-53407075111026481 / 375000000000000)*u + (3141592653589793 / 3000000000000000)*u^2)), {u, 0 / 1 + y, Infinity}], {z, 0 / 1, 100 / 1}]) / (((14554998764081510969 / 3000000000000000) + (-53407075111026481 / 375000000000000)*x + (3141592653589793 / 3000000000000000)*x^2)))) / (Boole[(-100) / 1 ≤ 0] * Boole[0 / 1 ≤ 0] * Boole[0 / 1 + ((-1) / 1 * x) ≤ 0] * Integrate[((Integrate[Integrate[(((1 / 1000000))) / (((14554998764081510969 / 3000000000000000) + (-53407075111026481 / 375000000000000)*v + (3141592653589793 / 3000000000000000)*v^2)), {v, 0 / 1 + z, Infinity}], {u, 0 / 1, 100 / 1}]) / (((14554998764081510969 / 3000000000000000) + (-53407075111026481 / 375000000000000)*x + (3141592653589793 / 3000000000000000)*x^2))) / (Boole[(-100) / 1 ≤ 0] * Boole[0 / 1 ≤ 0] * Boole[0 / 1 + ((-1) / 1 * x) + z ≤ 0] * (Integrate[Integrate[(((1 / 10000))) / (((14554998764081510969 / 3000000000000000) + (-53407075111026481 / 375000000000000)*v + (3141592653589793 / 3000000000000000)*v^2)), {v, 0 / 1 + z, Infinity}], {u, 0 / 1, 100 / 1}]) / (((14554998764081510969 / 3000000000000000) + (-53407075111026481 / 375000000000000)*x + (3141592653589793 / 3000000000000000)*x^2))), {z, 0 / 1, Min[0 / 1 + x, 100 / 1]}])
>>>>>>> 419efd9 (Split listener prob. function defs.)

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.Uniform(⟨0, 100⟩)(λz.(((Uniform(⟨0, 100⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙(⟦U(z)⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩ ≐ x)))) * 1) * 1) * y(U(z))))))

test1 = mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))

-- >>> test1
-- Boole[65 + (-1 * x) ≤ 0] * (Integrate[(1/100*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*x + -1/18*x^2]), {y, 0, 100}]) / (Integrate[Integrate[(1/100*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*z + -1/18*z^2]), {z, 65, Infinity}], {y, 0, 100}])
        
-- >>> mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Boole[65 + (-1 * x) ≤ 0] * (Integrate[(1/100*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*x + -1/18*x^2]), {y, 0, 100}]) / (Integrate[Integrate[(1/100*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*z + -1/18*z^2]), {z, 65, Infinity}], {y, 0, 100}])

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1

-- >>> mathematica $ expectedValue $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- (Integrate[Integrate[(1/100*(3*sqrt(pi))^(-1)*y*Exp[-2312/9 + 68/9*y + -1/18*y^2]), {y, 0 + x, Infinity}], {x, 0, 100}]) / (Integrate[Integrate[(1/100*(3*sqrt(pi))^(-1)*Exp[-2312/9 + 68/9*y + -1/18*y^2]), {y, 0 + x, Infinity}], {x, 0, 100}])

-- >>> mathematicaFun $ distr $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Boole[-100 ≤ 0] * Boole[(-1 * x) ≤ 0] * (Integrate[((((500000000000000000 / 565486677645711363147321)*Exp[(-2312 / 9) + (68 / 9)*x + (-1 / 18)*x^2]^2)) / (Integrate[Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*u + (-1 / 18)*u^2]), {u, z, Infinity}], {z, 0, 100}])) / ((Boole[(-1 * x) ≤ 0] * Boole[(-1 * y) ≤ 0] * Boole[y + (-1 * x) ≤ 0] * Boole[-100 + y ≤ 0] * (((500000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*x + (-1 / 18)*x^2])) / (Integrate[Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*u + (-1 / 18)*u^2]), {u, z, Infinity}], {z, 0, 100}])) + (Boole[-100 + x ≤ 0] * Boole[x + (-1 * y) ≤ 0] * Boole[(-1 * y) ≤ 0] * Boole[-100 + y ≤ 0] * (((500000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*x + (-1 / 18)*x^2])) / (Integrate[Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*u + (-1 / 18)*u^2]), {u, -Infinity, z}], {z, 0, 100}]))), {y, 0, Min[100, x]}]) / (Boole[-100 ≤ 0] * Integrate[Integrate[((((500000000000000000 / 565486677645711363147321)*Exp[(-2312 / 9) + (68 / 9)*z + (-1 / 18)*z^2]^2)) / (Integrate[Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*v + (-1 / 18)*v^2]), {v, u, Infinity}], {u, 0, 100}])) / ((Boole[-100 + y ≤ 0] * Boole[(-1 * y) ≤ 0] * Boole[(-1 * z) ≤ 0] * Boole[y + (-1 * z) ≤ 0] * (((500000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*z + (-1 / 18)*z^2])) / (Integrate[Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*v + (-1 / 18)*v^2]), {v, u, Infinity}], {u, 0, 100}])) + (Boole[-100 + y ≤ 0] * Boole[(-1 * y) ≤ 0] * Boole[-100 + z ≤ 0] * Boole[z + (-1 * y) ≤ 0] * (((500000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*z + (-1 / 18)*z^2])) / (Integrate[Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*v + (-1 / 18)*v^2]), {v, -Infinity, u}], {u, 0, 100}]))), {z, Max[0, y], Infinity}], {y, 0, 100}])

-- >>> mathematicaFun $ evalβ $ distr $ normal 0 10 ⋆ Lam (normal 0 10 ⋆ Lam (η ((Var Get) + (Var (Weaken Get)))))
-- (Integrate[((10*sqrt(pi))^(-2)*Exp[1/100*y*x + -1/200*y^2 + -1/200*x^2]*Exp[-1/200*y^2]), {y, -Infinity, Infinity}]) / (Integrate[Integrate[((10*sqrt(pi))^(-2)*Exp[-1/200*z^2]*Exp[-1/200*y^2]), {z, -Infinity, Infinity}], {y, -Infinity, Infinity}])

-- >>> mathematicaFun $ evalβ $ distr $ quartic 68 3
-- Boole[3003137303341 / 50000000000 + ((-1) / 1 * x) ≤ 0] * Boole[(-3796862696659) / 50000000000 + x ≤ 0] * (((2031515722656444751221424720214330661729615786296265625000000 / 3281558422976331182873957633672710068762668234936188562433) + (-121151562500005807096275764375000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x + (899023437500014233079107265625000000000000000000000000000 / 1093852807658777060957985877890903356254222744978729520811)*x^2 + (-26562500000000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x^3 + (97656250000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x^4)) / (Integrate[((2031515722656444751221424720214330661729615786296265625000000 / 3281558422976331182873957633672710068762668234936188562433) + (-121151562500005807096275764375000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*y + (899023437500014233079107265625000000000000000000000000000 / 1093852807658777060957985877890903356254222744978729520811)*y^2 + (-26562500000000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*y^3 + (97656250000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*y^4), {y, 3003137303341 / 50000000000, 3796862696659 / 50000000000}])
