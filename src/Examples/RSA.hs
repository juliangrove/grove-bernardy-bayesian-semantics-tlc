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
    ⋆ Lam (cauchy 68 3
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

-- >>> mathematicaFun' utilityl0
-- \mathbb{1}(0 \leq 0) * \mathbb{1}(-100 \leq 0) * \mathbb{1}(0 + (-1 * x) + y \leq 0) * \frac{\frac{\frac{1}{100}}{\pi * 3 * \frac{4633}{9} + \pi * 3 * \frac{-136}{9}*x + \pi * 3 * \frac{1}{9}*x^2}}{\int_{0}^{100}\int_{0 + y}^{\infty}\frac{\frac{1}{100}}{\pi * 3 * \frac{4633}{9} + \pi * 3 * \frac{-136}{9}*u + \pi * 3 * \frac{1}{9}*u^2}\,du\,dz}

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.Uniform(⟨0, 100⟩)(λz.(((((Uniform(⟨0, 100⟩)(λu.*** Exception: /tmp/danters3hnN.hs:(236,3)-(248,20): Non-exhaustive patterns in function show

test1 = mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))

-- >>> test1
-- \mathbb{1}(65 + (-1 * x) \leq 0) * \frac{\int_{0}^{100}\frac{\frac{1}{100}}{\pi * 3 * \frac{4633}{9} + \pi * 3 * \frac{-136}{9}*x + \pi * 3 * \frac{1}{9}*x^2}\,dy}{\int_{0}^{100}\int_{65}^{\infty}\frac{\frac{1}{100}}{\pi * 3 * \frac{4633}{9} + \pi * 3 * \frac{-136}{9}*z + \pi * 3 * \frac{1}{9}*z^2}\,dz\,dy}
        
-- >>> mathematicaFun $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- \mathbb{1}(65 + (-1 * x) \leq 0) * \frac{\int_{0}^{100}\frac{\frac{1}{100}}{\pi * 3 * \frac{4633}{9} + \pi * 3 * \frac{-136}{9}*x + \pi * 3 * \frac{1}{9}*x^2}\,dy}{\int_{0}^{100}\int_{65}^{\infty}\frac{\frac{1}{100}}{\pi * 3 * \frac{4633}{9} + \pi * 3 * \frac{-136}{9}*z + \pi * 3 * \frac{1}{9}*z^2}\,dz\,dy}

-- >>> displayVs $ clean $ evalβ $ subEq $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1

-- >>> mathematica $ expectedValue $ App l0 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- \frac{\int_{0}^{100}\int_{0 + x}^{\infty}\frac{\frac{1}{100}*y}{\pi * 3 * \frac{4633}{9} + \pi * 3 * \frac{-136}{9}*y + \pi * 3 * \frac{1}{9}*y^2}\,dy\,dx}{\int_{0}^{100}\int_{0 + x}^{\infty}\frac{\frac{1}{100}}{\pi * 3 * \frac{4633}{9} + \pi * 3 * \frac{-136}{9}*y + \pi * 3 * \frac{1}{9}*y^2}\,dy\,dx}

-- >>> mathematicaFun $ distr $ App l1 (u 1) ⋆ Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- (0)

-- >>> mathematicaFun $ evalβ $ distr $ normal 0 10 ⋆ Lam (normal 0 10 ⋆ Lam (η ((Var Get) + (Var (Weaken Get)))))
-- (Integrate[((10*sqrt(pi))^(-2)*Exp[1/100*y*x + -1/200*y^2 + -1/200*x^2]*Exp[-1/200*y^2]), {y, -Infinity, Infinity}]) / (Integrate[Integrate[((10*sqrt(pi))^(-2)*Exp[-1/200*z^2]*Exp[-1/200*y^2]), {z, -Infinity, Infinity}], {y, -Infinity, Infinity}])

-- >>> mathematicaFun $ evalβ $ distr $ normal 68 3
-- \frac{(3 * \sqrt{\pi})^{-1}*e^{\frac{-2312}{9} + \frac{68}{9}*x + \frac{-1}{18}*x^2}}{\int_{-\infty}^{\infty}(3 * \sqrt{\pi})^{-1}*e^{\frac{-2312}{9} + \frac{68}{9}*y + \frac{-1}{18}*y^2}\,dy}
