{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module Examples.RSA where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Optimizer
import TLC.Terms
import TLC.Distributions


k :: γ ⊢ ((Context ⟶ 'R) ⟶ 'R)
k = uniform 0 1000
    ⋆ Lam (normal 68 3
            ⋆ Lam
           (observe' ((≥) `App` Var Get `App`  (Con (General (Incl 50)))) >>
           (observe' ((≥) `App` (Con (General (Incl 80))) `App`  Var Get) >>
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
               vlad)))))

makeUtts :: [γ ⊢ 'U] -> γ ⊢ (('U ⟶ 'R) ⟶ 'R)
makeUtts us = Lam $ foldr1 addi $ map (App (Var Get) . wkn) us
  where addi :: γ ⊢ 'R -> γ ⊢ 'R -> γ ⊢ 'R
        addi x y = (Con $ General Addi) `App` x `App` y

utts123 :: γ ⊢ (('U ⟶ 'R) ⟶ 'R)
utts123 = makeUtts [u 1, u 2, u 3]

utts'' :: γ ⊢ (('U ⟶ 'R) ⟶ 'R)
utts'' = uniform 50 80 ⋆ Lam (η (u' (Var Get)))

updctx :: γ ⊢ Context -> γ ⊢ ('R ⟶ Context)
updctx k = Lam (Pair
                (Pair (Fst (Fst $ wkn k))
                 (Lam (Var (Weaken Get))))
                (π Get $ wkn k))

-- >>> displayVs utts'
-- (λx.((3 / 4 * x(U1)) + (1 / 4 * x(U2))))

-- >>> interp (Con $ General $ Utt 1)
-- (height(v) ≥ θ)


-- | Pragmatic listener
l1 :: γ ⊢ ('U ⟶ ((Context ⟶ 'R) ⟶ 'R))
l1 = Lam (k ⋆ Lam (
             factor' ((App (distr (App s1 (Var Get))) (Var (Weaken Get)))) >>
             η (Var Get)))

l1Distr :: γ ⊢ ('U ⟶ Context ⟶ 'R)
l1Distr = Lam (Lam (distr (l1 `App` Var (Weaken Get))) `App` Var Get)

-- | Pragmatic speaker
s1' :: Integer -> γ ⊢ (Context ⟶ ('U ⟶ 'R) ⟶ 'R)
s1' α = Lam (-- utts123
             utts''
             ⋆ Lam (
             factor'
             ((App (distr (App l0 (Var Get))) (Var (Weaken Get))) ^+ α) >>
             η (Var Get)))

s1 :: γ ⊢ (Context ⟶ ('U ⟶ 'R) ⟶ 'R)
s1 = s1' 1

s1Distr :: γ ⊢ (Context ⟶ 'U ⟶ 'R)
s1Distr = Lam (Lam (distr (s1 `App` Var (Weaken Get))) `App` Var Get)

-- | Literal listener
l0 :: γ ⊢ ('U ⟶ (Context ⟶ 'R) ⟶ 'R)
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

-- >>> maxima $ simplifyFun2 utilityl0
-- charfun(50 - x <= 0) * charfun(-80 + x <= 0) * charfun(-x + y <= 0) * (((3 * sqrt(2 * %pi))^(-1) * (1/1000)*exp((-2312/9) + (68/9)*x + (-1/18)*x^2))/(1)) / (charfun(-80 + y <= 0) * integrate(integrate(((3 * sqrt(2 * %pi))^(-1) * (1/1000)*exp((-2312/9) + (68/9)*u + (-1/18)*u^2))/(1), u, max(50, y), 80), z, 0, 1000))

-- >>> approximateIntegralsAny 8 $ simplifyFun2 utilitys1
-- Boole[50.0*1 - y ≤ 0] * Boole[-80.0*1 + y ≤ 0] * Boole[-80.0*1 + x ≤ 0] * Boole[50.0*1 - x ≤ 0] * Boole[-x + y ≤ 0] * (((4.432692004460363e-6*Exp[-256.8888888888889*1 + 7.555555555555555*1*x - 5.555555555555555e-2*1*x^2])/(1)) / ((2.8323857304737654e-5*1 + 8.443222865638789e-2*Exp[-256.8888888888889*1 + 7.555555555555555*1*y - 5.555555555555555e-2*1*y^2] + 0.777770684739406*Exp[-234.3986432096956*1 + 6.9425524352499135*1*y - 5.140711743910898e-2*1*y^2] + 1.4860072243524263*Exp[-175.99551054765925*1 + 5.337958951149179*1*y - 4.0475188366292984e-2*1*y^2] + 1.924060632265006*Exp[-104.1958590860313*1 + 3.3266854320608417*1*y - 2.6552964918568126e-2*1*y^2] + 2.093919270678419*Exp[-43.55555555555557*1 + 1.5555555555555554*1*y - 1.3888888888888885e-2*1*y^2] + 1.924060632265006*Exp[-8.95020480849783*1 + 0.43529949863571904*1*y - 5.292774231618703e-3*1*y^2] + 0.777770684739406*Exp[-4.455292895775358*1 - 3.7870699279808295e-2*1*y - 8.04767440375035e-5*1*y^2] + 1.4860072243524263*Exp[-4.4894523408061104e-3*1 - 4.625617815846139e-3*1*y - 1.1914783003736794e-3*1*y^2] - 3.5404821630922066e-7*1 - 1.0554028582048488e-3*Exp[-256.8888888888889*1 + 7.555555555555555*1*y - 5.555555555555555e-2*1*y^2] - 9.722133559242575e-3*Exp[-234.3986432096956*1 + 6.9425524352499135*1*y - 5.140711743910898e-2*1*y^2] - 1.857509030440533e-2*Exp[-175.99551054765925*1 + 5.337958951149179*1*y - 4.0475188366292984e-2*1*y^2] - 2.4050757903312573e-2*Exp[-104.1958590860313*1 + 3.3266854320608417*1*y - 2.6552964918568126e-2*1*y^2] - 2.6173990883480238e-2*Exp[-43.55555555555557*1 + 1.5555555555555554*1*y - 1.3888888888888885e-2*1*y^2] - 2.4050757903312573e-2*Exp[-8.95020480849783*1 + 0.43529949863571904*1*y - 5.292774231618703e-3*1*y^2] - 9.722133559242575e-3*Exp[-4.455292895775358*1 - 3.7870699279808295e-2*1*y - 8.04767440375035e-5*1*y^2] - 1.857509030440533e-2*Exp[-4.4894523408061104e-3*1 - 4.625617815846139e-3*1*y - 1.1914783003736794e-3*1*y^2]*y)/(1))) / ((0)/(0))

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.Uniform(⟨50, 80⟩)(λz.((((Uniform(⟨0, 1000⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙((v ≥ 50)) * (𝟙((80 ≥ v)) * (𝟙(⟦U(z)⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩)) * (⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩ ≐ x)))))) / Uniform(⟨0, 1000⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙((v ≥ 50)) * (𝟙((80 ≥ v)) * (𝟙(⟦U(z)⟧(⟨⟨⟨⟨⟨⟨⟨⟨⋄, sel⟩, (∷)⟩, ε⟩, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩)) * 1)))))) * 1) * 1) * y(U(z))))))

test1 :: P ((), Rat) Rat
test1 = simplifyFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))

-- >>> test1
-- \mathbb{1}(65 + (-x) \leq 0) * \frac{\int_{0}^{1000}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}x + \frac{-1}{18}x^2}}\,dy}{\int_{0}^{1000}\int_{65}^{\infty}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}z + \frac{-1}{18}z^2}}\,dz\,dy}
        
-- >>> simplifyFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- \mathbb{1}(65 + (-x) \leq 0) * \frac{\int_{0}^{1000}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}x + \frac{-1}{18}x^2}}\,dy}{\int_{0}^{1000}\int_{65}^{\infty}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}z + \frac{-1}{18}z^2}}\,dz\,dy}

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1

-- >>> :set -XAllowAmbiguousTypes
-- >>> :set -XTypeApplications
-- >>> :set -XDataKinds
-- >>> simplify @'Unit $ expectedValue $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*y*Exp[(-34/9) + (1/18)*y])/(1), {y, x, Infinity}], {x, 0, 1000}]) / (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*y])/(1), {y, x, Infinity}], {x, 0, 1000}])

-- >>> simplifyFun $ distr $ App l1 (u 1) ⋆ Lam (η (App (hmorph θ) (Var Get)))
-- Boole[-x ≤ 0] * Boole[-1000 + x ≤ 0] * Boole[-1000 + x ≤ 0] * Boole[-x ≤ 0] * (Integrate[((((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000) * (3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*y]^2)/(1)) / (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*u])/(1), {u, z, Infinity}], {z, 0, 1000}])) / ((Boole[-1000 + x ≤ 0] * Boole[-x ≤ 0] * Boole[-y ≤ 0] * Boole[-y + x ≤ 0] * (((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*y])/(1)) / (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*u])/(1), {u, z, Infinity}], {z, 0, 1000}])) + ((Boole[-1000 + x ≤ 0] * Boole[-x ≤ 0] * Boole[-1000 + y ≤ 0] * Boole[y - x ≤ 0] * (((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*y])/(1)) / (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*u])/(1), {u, -Infinity, z}], {z, 0, 1000}])) + (Boole[-1000 + x ≤ 0] * Boole[-x ≤ 0] * (((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*y])/(1)) / (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*u])/(1), {u, -Infinity, Infinity}], {z, 0, 1000}])))), {y, Max[0, x], Infinity}]) / (Integrate[Integrate[((((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000) * (3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*z]^2)/(1)) / (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*v])/(1), {v, u, Infinity}], {u, 0, 1000}])) / ((Boole[-y ≤ 0] * Boole[-1000 + y ≤ 0] * Boole[-z + y ≤ 0] * Boole[-z ≤ 0] * (((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*z])/(1)) / (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*v])/(1), {v, u, Infinity}], {u, 0, 1000}])) + ((Boole[-y ≤ 0] * Boole[-1000 + y ≤ 0] * Boole[z - y ≤ 0] * Boole[-1000 + z ≤ 0] * (((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*z])/(1)) / (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*v])/(1), {v, -Infinity, u}], {u, 0, 1000}])) + (Boole[-y ≤ 0] * Boole[-1000 + y ≤ 0] * (((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*z])/(1)) / (Integrate[Integrate[((3 * Sqrt[2 * pi])^((-1) % 1) * (1/1000)*Exp[(-34/9) + (1/18)*v])/(1), {v, -Infinity, Infinity}], {u, 0, 1000}])))), {z, Max[0, y], Infinity}], {y, 0, 1000}])

-- >>> simplifyFun $ distr $ normal 0 10 ⋆ Lam (normal 0 10 ⋆ Lam (η ((Var Get) + (Var (Weaken Get)))))
-- (Integrate[((10 * Sqrt[2 * pi])^((-2) % 1)*Exp[(-1/200)*y + (1/200)*x]*Exp[(1/200)*y])/(1), {y, -Infinity, Infinity}]) / (Integrate[Integrate[((10 * Sqrt[2 * pi])^((-2) % 1)*Exp[(1/200)*z]*Exp[(1/200)*y])/(1), {z, -Infinity, Infinity}], {y, -Infinity, Infinity}])

-- >>> :set -XAllowAmbiguousTypes
-- >>> :set -XTypeApplications
-- >>> :set -XDataKinds
-- >>> simplify @'Unit $ evalβ $ measure $ normal 68 3
-- Integrate[((3 * Sqrt[2 * pi])^((-1) % 1)*Exp[(-34/9) + (1/18)*x])/(1), {x, -Infinity, Infinity}]
