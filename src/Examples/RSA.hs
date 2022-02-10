{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RebindableSyntax #-}

module Examples.RSA where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Integrals
import Models.Integrals.Approx4
import TLC.Terms
import TLC.Distributions
import qualified Algebra.Linear.Vector as V

-- >>> toGnuPlot "test.dat" test2'

test2' :: V.Vec (V.Vec Double)
test2' = approxTop test2

test2 :: P (('Unit × 'R) × 'R)
test2 = simplifyFun2 [] utilityl1


-- >>> maxima test2
-- charfun(53 - y <= 0)*charfun(-83 + y <= 0)*charfun(-78 + y <= 0)*charfun(-83 + x <= 0)*charfun(-x + y <= 0)*exp(-1/2*(1/3*(68 - x))^2)*integrate(exp(-1/2*(1/3*(68 - z))^2)*integrate(integrate(exp(-1/2*(1/3*(68 - v))^2), v, u, 83)^(-4), u, 53, min(78, z))^(-1)*integrate(exp(-1/2*(1/3*(68 - u))^2), u, y, 83)^(-4), z, y, 83)^(-1)*integrate(integrate(exp(-1/2*(1/3*(68 - u))^2), u, z, 83)^(-4), z, 53, min(78, x))^(-1)*integrate(exp(-1/2*(1/3*(68 - z))^2), z, y, 83)^(-4)


utts'' :: γ ⊢ (('U ⟶ 'R) ⟶ 'R)
utts'' = uniform (68-15) (68+10) ⋆ Lam (η (u' (Var Get)))

k :: γ ⊢ ((Context0 ⟶ 'R) ⟶ 'R)
k = uniform 0 1
    ⋆ Lam (normal 68 3
           ⋆ Lam
           (observe' ((≥) `App` Var Get `App`  (Con (General (Incl (68 - 15))))) >>
           (observe' ((≥) `App` (Con (General (Incl (68 + 15)))) `App`  Var Get) >>
            (η (Pair
                (Pair
                 (Pair
                  (Pair
                   (Pair TT (≥))
                   (Var (Weaken Get)))
                  human)
                 (Lam (Var (Weaken Get))))
                vlad)))))

makeUtts :: [γ ⊢ 'U] -> γ ⊢ (('U ⟶ 'R) ⟶ 'R)
makeUtts us = Lam $ foldr1 addi $ map (App (Var Get) . wkn) us
  where addi :: γ ⊢ 'R -> γ ⊢ 'R -> γ ⊢ 'R
        addi x y = (Con $ General Addi) `App` x `App` y

-- utts123 :: γ ⊢ (('U ⟶ 'R) ⟶ 'R)
-- utts123 = makeUtts [u 1, u 2, u 3]

updctx :: γ ⊢ Context0 -> γ ⊢ ('R ⟶ Context0)
updctx kk = Lam (Pair
                (Pair (Fst (Fst $ wkn kk))
                 (Lam (Var (Weaken Get))))
                (π Get $ wkn kk))

-- >>> interp (Con $ General $ Utt 1)
-- (height(v) ≥ θ)

-- | Pragmatic listener
l1 :: γ ⊢ ('U ⟶ (Context0 ⟶ 'R) ⟶ 'R)
l1 = Lam (k ⋆ Lam (
             factor' ((App (distr (App s1 (Var Get))) (Var (Weaken Get)))) >>
             η (Var Get)))

l1Distr :: γ ⊢ ('U ⟶ Context0 ⟶ 'R)
l1Distr = Lam (Lam (distr (l1 `App` Var (Weaken Get))) `App` Var Get)

-- | Pragmatic speaker
s1' :: Integer -> γ ⊢ (Context0 ⟶ ('U ⟶ 'R) ⟶ 'R)
s1' α = Lam (
             utts''
             ⋆ Lam (
             factor' ((distr (l0 `App` Var Get) `App`  (Var (Weaken Get))) ^+ α) >>
             η (Var Get)))

-- s1'' :: Integer -> H.Exp (Context0 ⟶ ('U ⟶ 'R) ⟶ 'R)
-- s1'' α = H.Lam $ \ctx ->
--            H.toHOAS utts'' H.⋆ H.Lam (\u ->
--               (H.toHOAS factor `H.App` _) H.>> H.η u
--                                      )

s1 :: γ ⊢ (Context0 ⟶ ('U ⟶ 'R) ⟶ 'R)
s1 = s1' 4

s1Distr :: γ ⊢ (Context0 ⟶ 'U ⟶ 'R)
s1Distr = Lam (Lam (distr (s1 `App` Var (Weaken Get))) `App` Var Get)

-- | Literal listener
l0 :: γ ⊢ ('U ⟶ (Context0 ⟶ 'R) ⟶ 'R)
l0 = Lam (k ⋆
          Lam (
             observe'
             (App (App (Con (General (Interp Z))) (Var (Weaken Get))) (Var Get)) >>
             η (Var Get)))

l0Distr :: γ ⊢ ('U ⟶ Context0 ⟶ 'R)
l0Distr = Lam (Lam (distr (l0 `App` Var (Weaken Get))) `App` Var Get)

-- l0DistrForFixedU2 :: γ ⊢ ('R ⟶ 'R)
-- l0DistrForFixedU2 = distr $ App l0 (u 2) ⋆ Lam (η (App (hmorph (height `App` vlad)) (Var Get)))

-- l1DistrForFixedU :: Int -> γ ⊢ ('R ⟶ 'R)
-- l1DistrForFixedU n = distr $ App l1 (u n) ⋆ Lam (η (App (hmorph (height `App` vlad)) (Var Get)))

test :: γ ⊢ ('R ⟶ 'R)
test = distr $ uniform 0 10 ⋆ Lam (uniform 0 10 ⋆ Lam (η ((Con (General Addi)) `App` (Var Get) `App` (Var (Weaken Get)))))

heightToCtx :: γ ⊢ ('R ⟶ Context0)
heightToCtx = Lam ((Pair
                    (Pair
                     (Pair
                      (Pair
                       (Pair TT (≥))
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

-- >>> displayVs $ evalβ utilitys1
-- (λx.(λy.(Uniform(⟨51, 81⟩)(λz.((((Uniform(⟨0, 1⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙((v ≥ 50)) * (𝟙((80 ≥ v)) * (𝟙((v ≥ z)) * ((u ≐ 0) * (v ≐ y))))))) / Uniform(⟨0, 1⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙((v ≥ 50)) * (𝟙((80 ≥ v)) * (𝟙((v ≥ z)) * 1)))))) * 1) * 1) * 1)) / Uniform(⟨51, 81⟩)(λz.((((Uniform(⟨0, 1⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙((v ≥ 50)) * (𝟙((80 ≥ v)) * (𝟙((v ≥ z)) * ((u ≐ 0) * (v ≐ y))))))) / Uniform(⟨0, 1⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙((v ≥ 50)) * (𝟙((80 ≥ v)) * (𝟙((v ≥ z)) * 1)))))) * 1) * 1) * 1)))))

-- >>> maxima $ approxIntegrals 1 $ simplifyFun2 utilitys1
-- charfun(50 - y <= 0)*charfun(-80 + y <= 0)*charfun(-80 + x <= 0)*charfun(50 - x <= 0)*charfun(-x + y <= 0)*(3*sqrt(2*%pi))^-(1)*1/30*exp(-2312/9 + 68/9*x - 1/18*x^2)/integrate(integrate((3*sqrt(2*%pi))^-(1)*exp(-2312/9 + 68/9*u - 1/18*u^2), u, 50, 80), z, 0, 1)/integrate((3*sqrt(2*%pi))^-(1)*1/30*exp(-2312/9 + 68/9*x - 1/18*x^2)/integrate(integrate((3*sqrt(2*%pi))^-(1)*exp(-2312/9 + 68/9*v - 1/18*v^2), v, 50, 80), u, 0, 1), z, 50, x)

--   charfun(((50.0)) - x <= 0) * charfun(((-80.0)) + x <= 0) * charfun(-x + y <= 0) * ((((1.329807601338109e-4)*exp(((-256.8888888888889)) + ((7.555555555555555))*x + ((-5.555555555555555e-2))*x^2)))/(1)) / (charfun(((-80.0)) + y <= 0) * (((5.948010033994905e-4) + (1.7730768017841454)*exp(((-256.8888888888889)) + ((7.555555555555555))*max(((50.0)), y) + ((-5.555555555555555e-2))*max(((50.0)), y)^2) + (7.092307207136581)*exp(((-43.55555555555557)) + ((1.5555555555555554))*max(((50.0)), y) + ((-1.3888888888888885e-2))*max(((50.0)), y)^2)) + ((-7.435012542493632e-6) + (-2.216346002230182e-2)*exp(((-256.8888888888889)) + ((7.555555555555555))*max(((50.0)), y) + ((-5.555555555555555e-2))*max(((50.0)), y)^2) + (-8.865384008920726e-2)*exp(((-43.55555555555557)) + ((1.5555555555555554))*max(((50.0)), y) + ((-1.3888888888888885e-2))*max(((50.0)), y)^2))*max(((50.0)), y))/(1));


-- >>> maxima $ simplifyFun2 Z utilitys1
-- charfun(51 - y <= 0)*charfun(-81 + y <= 0)*charfun(-80 + x <= 0)*charfun(50 - x <= 0)*charfun(51 - x <= 0)*charfun(-x + y <= 0)*(3*sqrt(2*%pi))^-(1)*1/30*exp(-2312/9 + 68/9*x - 1/18*x^2)/(charfun(-80 + y <= 0)*integrate(integrate((3*sqrt(2*%pi))^-(1)*exp(-2312/9 + 68/9*u - 1/18*u^2), u, max(y, 50), 80), z, 0, 1))/integrate((3*sqrt(2*%pi))^-(1)*1/30*exp(-2312/9 + 68/9*x - 1/18*x^2)/(charfun(-80 + z <= 0)*integrate(integrate((3*sqrt(2*%pi))^-(1)*exp(-2312/9 + 68/9*v - 1/18*v^2), v, max(z, 50), 80), u, 0, 1)), z, 51, min(81, x))

--  integrate((((((3 * sqrt(2 * %pi))^(-1) * (1/30) * (1/30))*exp((((-2312/9))) + (((68/9)))*x + (((-1/18)))*x^2)))/(1)) / (integrate(integrate(((((3 * sqrt(2 * %pi))^(-1) * (1/30))*exp((((-2312/9))) + (((68/9)))*v + (((-1/18)))*v^2)))/(1), v, z, ((80))), u, ((50)), ((80)))), z, ((50)), ((80)))

-- >>> displayVs $ evalβ $ s1
-- (λx.(λy.Uniform(⟨50, 80⟩)(λz.((((Uniform(⟨0, 1000⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙((v ≥ 50)) * (𝟙((80 ≥ v)) * (𝟙(⟦U(z)⟧(⟨⟨⟨⟨⟨⋄, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩)) * (⟨⟨⟨⟨⟨⋄, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩ ≐ x)))))) / Uniform(⟨0, 1000⟩)(λu.Normal(⟨68, 3⟩)(λv.(𝟙((v ≥ 50)) * (𝟙((80 ≥ v)) * (𝟙(⟦U(z)⟧(⟨⟨⟨⟨⟨⋄, (≥)⟩, u⟩, human⟩, (λw.v)⟩, v⟩)) * 1)))))) * 1) * 1) * y(U(z))))))

test1 :: P ('Unit × 'R)
test1 = simplifyFun [] $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph Z (App height vlad)) (Var Get)))

-- >>> test1
-- Cond (IsNegative {condExpr = Affine 50 (LinComb {fromLinComb = fromList [(Get,-1)]})}) (Cond (IsNegative {condExpr = Affine (-80) (LinComb {fromLinComb = fromList [(Get,1)]})}) (Cond (IsNegative {condExpr = Affine 65 (LinComb {fromLinComb = fromList [(Get,-1)]})}) (Div (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 0 (LinComb {fromLinComb = fromList []})], domainHiBounds = [Affine 1000 (LinComb {fromLinComb = fromList []})]}) (Ret (P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-2312/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari (There Get),1)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},68/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari (There Get),2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/18)]}))]}},(3*(2*pi)^(1 % 2))^((-1) % 1)*(1/1000))]}))]}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}}))) (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 0 (LinComb {fromLinComb = fromList []})], domainHiBounds = [Affine 1000 (LinComb {fromLinComb = fromList []})]}) (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 50 (LinComb {fromLinComb = fromList []}),Affine 65 (LinComb {fromLinComb = fromList []})], domainHiBounds = [Affine 80 (LinComb {fromLinComb = fromList []})]}) (Ret (P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-2312/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,1)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},68/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/18)]}))]}},(3*(2*pi)^(1 % 2))^((-1) % 1)*(1/1000))]}))]}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}})))))))
        
-- >>> simplifyFun Z $ distr $ App l0 (u' (Con (General (Incl 65)))) ⋆ Lam (η (App (hmorph Z (App height vlad)) (Var Get)))
-- Cond (IsNegative {condExpr = Affine 50 (LinComb {fromLinComb = fromList [(Get,-1)]})}) (Cond (IsNegative {condExpr = Affine (-80) (LinComb {fromLinComb = fromList [(Get,1)]})}) (Cond (IsNegative {condExpr = Affine 65 (LinComb {fromLinComb = fromList [(Get,-1)]})}) (Div (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 0 (LinComb {fromLinComb = fromList []})], domainHiBounds = [Affine 1000 (LinComb {fromLinComb = fromList []})]}) (Ret (P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-2312/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari (There Get),1)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},68/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari (There Get),2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/18)]}))]}},(3*(2*pi)^(1 % 2))^((-1) % 1)*(1/1000))]}))]}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}}))) (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 0 (LinComb {fromLinComb = fromList []})], domainHiBounds = [Affine 1000 (LinComb {fromLinComb = fromList []})]}) (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 50 (LinComb {fromLinComb = fromList []}),Affine 65 (LinComb {fromLinComb = fromList []})], domainHiBounds = [Affine 80 (LinComb {fromLinComb = fromList []})]}) (Ret (P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-2312/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,1)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},68/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/18)]}))]}},(3*(2*pi)^(1 % 2))^((-1) % 1)*(1/1000))]}))]}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}})))))))

-- >>> displayVs $ clean Z $ evalβ $ subEq Z $ (Pair TT vlad) ≐ (Pair TT vlad)
-- 1

-- >>> :set -XAllowAmbiguousTypes
-- >>> :set -XTypeApplications
-- >>> :set -XDataKinds
-- >>> simplify Z $ expectedValue $ App l0 (u 1) ⋆ Lam (η (App (hmorph Z (App height vlad)) (Var Get)))
-- Div (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 0 (LinComb {fromLinComb = fromList []})], domainHiBounds = [Affine 80 (LinComb {fromLinComb = fromList []}),Affine 1000 (LinComb {fromLinComb = fromList []})]}) (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 50 (LinComb {fromLinComb = fromList []}),Affine 0 (LinComb {fromLinComb = fromList [(Get,1)]})], domainHiBounds = [Affine 80 (LinComb {fromLinComb = fromList []})]}) (Ret (P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,1)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-2312/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,1)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},68/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/18)]}))]}},(3*(2*pi)^(1 % 2))^((-1) % 1)*(1/1000))]}))]}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}})))) (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 0 (LinComb {fromLinComb = fromList []})], domainHiBounds = [Affine 80 (LinComb {fromLinComb = fromList []}),Affine 1000 (LinComb {fromLinComb = fromList []})]}) (Integrate (Domain {domainConditions = [], domainLoBounds = [Affine 50 (LinComb {fromLinComb = fromList []}),Affine 0 (LinComb {fromLinComb = fromList [(Get,1)]})], domainHiBounds = [Affine 80 (LinComb {fromLinComb = fromList []})]}) (Ret (P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-2312/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,1)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},68/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/18)]}))]}},(3*(2*pi)^(1 % 2))^((-1) % 1)*(1/1000))]}))]}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}}))))

-- >>> simplifyFun Z $ distr $ App l1 (u 1) ⋆ Lam (η (App (hmorph Z θ) (Var Get)))
-- Ret (P {fromPoly = LinComb {fromLinComb = fromList []}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}})

-- >>> simplifyFun Z $ distr $ normal 0 10 ⋆ Lam (normal 0 10 ⋆ Lam (η ((Var Get) + (Var (Weaken Get)))))
-- Div (Integrate (Domain {domainConditions = [], domainLoBounds = [], domainHiBounds = []}) (Ret (P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,1),(Vari (There Get),1)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1/100)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/100)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari (There Get),2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/200)]}))]}},(10*(2*pi)^(1 % 2))^((-2) % 1))]}))]}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}}))) (Integrate (Domain {domainConditions = [], domainLoBounds = [], domainHiBounds = []}) (Integrate (Domain {domainConditions = [], domainLoBounds = [], domainHiBounds = []}) (Ret (P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/200)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari (There Get),2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/200)]}))]}},(10*(2*pi)^(1 % 2))^((-2) % 1))]}))]}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}}))))

-- >>> :set -XAllowAmbiguousTypes
-- >>> :set -XTypeApplications
-- >>> :set -XDataKinds
-- >>> simplify Z $ evalβ $ measure $ normal 68 3
-- Integrate (Domain {domainConditions = [], domainLoBounds = [], domainHiBounds = []}) (Ret (P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-2312/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,1)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},68/9)]})),(M (Exponential {fromExponential = LinComb {fromLinComb = fromList [(Vari Get,2)]}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},-1/18)]}))]}},(3*(2*pi)^(1 % 2))^((-1) % 1))]}))]}} :/ P {fromPoly = LinComb {fromLinComb = fromList [(M (Exponential {fromExponential = LinComb {fromLinComb = fromList []}}),Coef (LinComb {fromLinComb = fromList [(P {fromPoly = LinComb {fromLinComb = fromList []}},1)]}))]}}))
