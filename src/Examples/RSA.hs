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
    ⋆ Lam (quartic 68 3
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
s1 = s1' 1

s1Distr :: γ ⊢ (Context ⟶ 'U ⟶ 'R)
s1Distr = Lam (Lam (distr (s1 `App` Var (Weaken Get))) `App` Var Get)

-- | Literal listener
l0 :: γ ⊢ ('U ⟶ ((Context ⟶ 'R) ⟶ 'R))
l0 = Lam (k ⋆ Lam (
             observe'
             (App (App (Con (General Interp)) (Var (Weaken Get))) (Var Get)) >>
             η (Var Get)))

-- l0DistrForFixedU2 :: γ ⊢ ('R ⟶ 'R)
-- l0DistrForFixedU2 = distr $ App l0 (u 2) ⋆ Lam (η (App (hmorph (height `App` vlad)) (Var Get)))

-- l1DistrForFixedU :: Int -> γ ⊢ ('R ⟶ 'R)
-- l1DistrForFixedU n = distr $ App l1 (u n) ⋆ Lam (η (App (hmorph (height `App` vlad)) (Var Get)))


test :: γ ⊢ ('R ⟶ 'R)
test = distr $ uniform 0 10 ⋆ Lam (uniform 0 10 ⋆ Lam (η ((Con (General Addi)) `App` (Var Get) `App` (Var (Weaken Get)))))

utilityl :: γ ⊢ ('R ⟶ 'R ⟶ 'R)
utilityl = Lam (Lam (l1Distr `App` (toAtLeastHeight `App` (Var (Weaken Get))) `App` (heightToCtx `App` Var Get) ))

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

utilitys :: γ ⊢ ('R ⟶ 'R ⟶ 'R)
utilitys = Lam (Lam (s1Distr `App` (heightToCtx `App` Var Get) `App` (toAtLeastHeight `App` (Var (Weaken Get))) ))
  -- Lam (Lam (expectedValue $ k ⋆ Lam (η $ App (distr $ App s1 (App (updctx (Var Get)) (Var (Weaken (Weaken Get))))) (u' (Var (Weaken Get))))))

-- exp1 = Lam (App k $ Lam (App (utility 1) (App (updctx (Var Get)) (Var (Weaken Get)))))

-- exp2 = Lam (App k $ Lam (App (utility 2) (App (updctx (Var Get)) (Var (Weaken Get)))))

-- >>> mathematicaFun' utilitys
-- Boole[-100 ≤ 0] * Boole[0 ≤ 0] * Boole[(-1 * y) ≤ 0] * Boole[-100 + y ≤ 0] * Boole[(-1 * x) + y ≤ 0] * Boole[(3003137303341 / 50000000000) + (-1 * x) ≤ 0] * Boole[(-3796862696659 / 50000000000) + x ≤ 0] * ((((203151572265644475122142472021433066172961578629626562500 / 3281558422976331182873957633672710068762668234936188562433) + (-12115156250000580709627576437500000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x + (89902343750001423307910726562500000000000000000000000 / 1093852807658777060957985877890903356254222744978729520811)*x^2 + (-2656250000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x^3 + (9765625000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x^4)) / (Boole[(-3796862696659 / 50000000000) + y ≤ 0] * Integrate[Integrate[((20315157226564447512214247202143306617296157862962656250000 / 3281558422976331182873957633672710068762668234936188562433) + (-1211515625000058070962757643750000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*u + (8990234375000142330791072656250000000000000000000000000 / 1093852807658777060957985877890903356254222744978729520811)*u^2 + (-265625000000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*u^3 + (976562500000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*u^4), {u, Max[y, (3003137303341 / 50000000000)], (3796862696659 / 50000000000)}], {z, 0, 100}])) / (Boole[-100 ≤ 0] * Boole[0 ≤ 0] * Boole[(-1 * x) ≤ 0] * Boole[(3003137303341 / 50000000000) + (-1 * x) ≤ 0] * Boole[(-3796862696659 / 50000000000) + x ≤ 0] * Integrate[(((203151572265644475122142472021433066172961578629626562500 / 3281558422976331182873957633672710068762668234936188562433) + (-12115156250000580709627576437500000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x + (89902343750001423307910726562500000000000000000000000 / 1093852807658777060957985877890903356254222744978729520811)*x^2 + (-2656250000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x^3 + (9765625000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x^4)) / (Boole[(-3796862696659 / 50000000000) + z ≤ 0] * Integrate[Integrate[((20315157226564447512214247202143306617296157862962656250000 / 3281558422976331182873957633672710068762668234936188562433) + (-1211515625000058070962757643750000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*v + (8990234375000142330791072656250000000000000000000000000 / 1093852807658777060957985877890903356254222744978729520811)*v^2 + (-265625000000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*v^3 + (976562500000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*v^4), {v, Max[z, (3003137303341 / 50000000000)], (3796862696659 / 50000000000)}], {u, 0, 100}]), {z, 0, Min[x, 100]}])

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.Uniform(⟨0, 100⟩)(λz.(((Uniform(⟨0, 100⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙(⟦U(z)⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩ ≐ x)))) * 1) * 1) * y(U(z))))))

test1 = mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))

-- >>> test1
-- Boole[65 + (-1 * x) ≤ 0] * (Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*x + (-1 / 18)*x^2]), {y, 0, 100}]) / (Integrate[Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*z + (-1 / 18)*z^2]), {z, 65, Infinity}], {y, 0, 100}])
        
-- >>> mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Boole[65 + (-1 * x) ≤ 0] * (Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*x + (-1 / 18)*x^2]), {y, 0, 100}]) / (Integrate[Integrate[((1000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*z + (-1 / 18)*z^2]), {z, 65, Infinity}], {y, 0, 100}])

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1

-- >>> mathematica $ expectedValue $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- (Integrate[Integrate[((100000000000 / 751988482389)*y*Exp[(-2312 / 9) + (68 / 9)*y + (-1 / 18)*y^2]), {y, x, Infinity}], {x, -Infinity, Infinity}]) / (Integrate[Integrate[((100000000000 / 751988482389)*Exp[(-2312 / 9) + (68 / 9)*y + (-1 / 18)*y^2]), {y, x, Infinity}], {x, -Infinity, Infinity}])

-- >>> mathematicaFun $ distr $ App l1 (u' 65) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- <interactive>:182:38-39: error:
--     • No instance for (GHC.Num.Num ('Unit ⊢ 'R))
--         arising from the literal ‘65’
--     • In the first argument of ‘u'’, namely ‘65’
--       In the second argument of ‘App’, namely ‘(u' 65)’
--       In the first argument of ‘(⋆)’, namely ‘App l1 (u' 65)’

-- >>> mathematicaFun $ evalβ $ distr $ normal 0 10 ⋆ Lam (normal 0 10 ⋆ Lam (η ((Var Get) + (Var (Weaken Get)))))
-- Integrate[(((100000000000000000000 / 62831853071745707016369)*Exp[(1 / 100)*y*x + (-1 / 200)*y^2 + (-1 / 200)*x^2]*Exp[(-1 / 200)*y^2])) / (Integrate[Integrate[((100000000000000000000 / 62831853071745707016369)*Exp[(-1 / 200)*u^2]*Exp[(-1 / 200)*z^2]), {u, -Infinity, Infinity}], {z, -Infinity, Infinity}]), {y, -Infinity, Infinity}]

-- >>> mathematicaFun $ evalβ $ distr $ quartic 68 3
-- Boole[(3003137303341 / 50000000000) + (-1 * x) ≤ 0] * Boole[(-3796862696659 / 50000000000) + x ≤ 0] * (((2031515722656444751221424720214330661729615786296265625000000 / 3281558422976331182873957633672710068762668234936188562433) + (-121151562500005807096275764375000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x + (899023437500014233079107265625000000000000000000000000000 / 1093852807658777060957985877890903356254222744978729520811)*x^2 + (-26562500000000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x^3 + (97656250000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*x^4)) / (Integrate[((2031515722656444751221424720214330661729615786296265625000000 / 3281558422976331182873957633672710068762668234936188562433) + (-121151562500005807096275764375000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*y + (899023437500014233079107265625000000000000000000000000000 / 1093852807658777060957985877890903356254222744978729520811)*y^2 + (-26562500000000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*y^3 + (97656250000000000000000000000000000000000000000000000 / 3281558422976331182873957633672710068762668234936188562433)*y^4), {y, (3003137303341 / 50000000000), (3796862696659 / 50000000000)}])

