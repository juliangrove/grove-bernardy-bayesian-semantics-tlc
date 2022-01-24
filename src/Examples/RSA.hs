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
k = uniform 0 1000
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

makeUtts :: [γ ⊢ U] -> γ ⊢ ((U ⟶ R) ⟶ R)
makeUtts us = Lam $ foldr1 addi $ map (App (Var Get) . wkn) us
  where addi :: γ ⊢ R -> γ ⊢ R -> γ ⊢ R
        addi x y = (Con $ General Addi) `App` x `App` y

utts123 :: γ ⊢ ((U ⟶ R) ⟶ R)
utts123 = makeUtts [u 1, u 2, u 3]

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
s1' α = Lam (utts123 ⋆ Lam (
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

-- >>> mathematicaFun' utilityl0
-- Boole[0 ≤ 0] * Boole[-100 ≤ 0] * Boole[0 + (-1 * x) + y ≤ 0] * (((1/100)) / (Pi * 3 * (4633/9) + Pi * 3 * (-136/9)*x + Pi * 3 * (1/9)*x^2)) / (Integrate[Integrate[((1/100)) / (Pi * 3 * (4633/9) + Pi * 3 * (-136/9)*u + Pi * 3 * (1/9)*u^2), {u, 0 + y, Infinity}], {z, 0, 100}])

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.Uniform(⟨0, 100⟩)(λz.(((((Uniform(⟨0, 100⟩)(λu.*** Exception: /tmp/danters3hnN.hs:(236,3)-(248,20): Non-exhaustive patterns in function show

test1 = mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))

-- >>> test1
-- Boole[65 + (-1 * x) ≤ 0] * (Integrate[(1/1000) * (3 * Sqrt[%pi])^(-1)*Exp[(-2312/9) + (68/9)*x + (-1/18)*x^2], {y, 0, 1000}]) / (Integrate[Integrate[(1/1000) * (3 * Sqrt[%pi])^(-1)*Exp[(-2312/9) + (68/9)*z + (-1/18)*z^2], {z, 65, Infinity}], {y, 0, 1000}])
        
-- >>> mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- Boole[65 + (-1 * x) ≤ 0] * (Integrate[(1/1000) * (3 * Sqrt[%pi])^(-1)*Exp[(-2312/9) + (68/9)*x + (-1/18)*x^2], {y, 0, 1000}]) / (Integrate[Integrate[(1/1000) * (3 * Sqrt[%pi])^(-1)*Exp[(-2312/9) + (68/9)*z + (-1/18)*z^2], {z, 65, Infinity}], {y, 0, 1000}])

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1

-- >>> mathematica $ expectedValue $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- \frac{\int_{0}^{1000}\int_{0 + x}^{\infty}\frac{1}{1000} * (3 * \sqrt{\pi})^{-1}ye^{\frac{-2312}{9} + \frac{68}{9}y + \frac{-1}{18}y^2}\,dy\,dx}{\int_{0}^{1000}\int_{0 + x}^{\infty}\frac{1}{1000} * (3 * \sqrt{\pi})^{-1}e^{\frac{-2312}{9} + \frac{68}{9}y + \frac{-1}{18}y^2}\,dy\,dx}

-- >>> mathematicaFun $ distr $ App l1 (u 1) ⋆ Lam (η (App (hmorph θ) (Var Get)))
-- \mathbb{1}(-1000 \leq 0) * \mathbb{1}((-x) \leq 0) * \mathbb{1}(-1000 + x \leq 0) * \mathbb{1}(-1000 + x \leq 0) * \mathbb{1}((-x) \leq 0) * \frac{\int_{Max[0, x]}^{\infty}\frac{\frac{\frac{1}{1000} * (3\sqrt{2\pi})^{-1} * \frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}y + \frac{-1}{18}y^2}}^2}{\int_{0}^{1000}\int_{z}^{\infty}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}u + \frac{-1}{18}u^2}}\,du\,dz}}{(\mathbb{1}(-1000 + x \leq 0) * \mathbb{1}((-x) \leq 0) * \mathbb{1}((-y) \leq 0) * \mathbb{1}(x + (-y) \leq 0) * \frac{\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}y + \frac{-1}{18}y^2}}}{\int_{0}^{1000}\int_{z}^{\infty}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}u + \frac{-1}{18}u^2}}\,du\,dz}) + ((\mathbb{1}(-1000 + x \leq 0) * \mathbb{1}((-x) \leq 0) * \mathbb{1}(-1000 + y \leq 0) * \mathbb{1}(y + (-x) \leq 0) * \frac{\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}y + \frac{-1}{18}y^2}}}{\int_{0}^{1000}\int_{-\infty}^{z}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}u + \frac{-1}{18}u^2}}\,du\,dz}) + (\mathbb{1}(-1000 + x \leq 0) * \mathbb{1}((-x) \leq 0) * \frac{\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}y + \frac{-1}{18}y^2}}}{\int_{0}^{1000}\int_{-\infty}^{\infty}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}u + \frac{-1}{18}u^2}}\,du\,dz}))}\,dy}{\mathbb{1}(-1000 \leq 0) * \int_{0}^{1000}\int_{Max[0, y]}^{\infty}\frac{\frac{\frac{1}{1000} * (3\sqrt{2\pi})^{-1} * \frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}z + \frac{-1}{18}z^2}}^2}{\int_{0}^{1000}\int_{u}^{\infty}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}v + \frac{-1}{18}v^2}}\,dv\,du}}{(\mathbb{1}(-1000 + y \leq 0) * \mathbb{1}((-y) \leq 0) * \mathbb{1}((-z) \leq 0) * \mathbb{1}(y + (-z) \leq 0) * \frac{\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}z + \frac{-1}{18}z^2}}}{\int_{0}^{1000}\int_{u}^{\infty}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}v + \frac{-1}{18}v^2}}\,dv\,du}) + ((\mathbb{1}(-1000 + y \leq 0) * \mathbb{1}((-y) \leq 0) * \mathbb{1}(-1000 + z \leq 0) * \mathbb{1}(z + (-y) \leq 0) * \frac{\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}z + \frac{-1}{18}z^2}}}{\int_{0}^{1000}\int_{-\infty}^{u}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}v + \frac{-1}{18}v^2}}\,dv\,du}) + (\mathbb{1}(-1000 + y \leq 0) * \mathbb{1}((-y) \leq 0) * \frac{\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}z + \frac{-1}{18}z^2}}}{\int_{0}^{1000}\int_{-\infty}^{\infty}\frac{1}{1000} * (3\sqrt{2\pi})^{-1}{e^{\frac{-2312}{9} + \frac{68}{9}v + \frac{-1}{18}v^2}}\,dv\,du}))}\,dz\,dy}

-- >>> mathematicaFun $ evalβ $ distr $ normal 0 10 ⋆ Lam (normal 0 10 ⋆ Lam (η ((Var Get) + (Var (Weaken Get)))))
-- \frac{\int_{-\infty}^{\infty}(10 * \sqrt{\pi})^{-2}{e^{\frac{1}{100}yx + \frac{-1}{200}y^2 + \frac{-1}{200}x^2}}{e^{\frac{-1}{200}y^2}}\,dy}{\int_{-\infty}^{\infty}\int_{-\infty}^{\infty}(10 * \sqrt{\pi})^{-2}{e^{\frac{-1}{200}z^2}}{e^{\frac{-1}{200}y^2}}\,dz\,dy}

-- >>> mathematicaFun $ evalβ $ distr $ normal 68 3
-- \frac{(3 * \sqrt{\pi})^{-1}*e^{\frac{-2312}{9} + \frac{68}{9}*x + \frac{-1}{18}*x^2}}{\int_{-\infty}^{\infty}(3 * \sqrt{\pi})^{-1}*e^{\frac{-2312}{9} + \frac{68}{9}*y + \frac{-1}{18}*y^2}\,dy}
