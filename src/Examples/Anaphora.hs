{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Examples.Anaphora where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Integrals.Conversion
import Models.Integrals.Show
import Models.Logical.Logical
import TLC.Distributions
import TLC.Terms


pis :: γ ⊢ ((('Γ ⟶ 'E) ⟶ 'R) ⟶ 'R)
pis = nf_to_λ $ toFinite [ Neu $ NeuCon $ General $ Pi 0
                         , Neu $ NeuCon $ General $ Pi 1 ]

k :: γ ⊢ ((Context1 ⟶ 'R) ⟶ 'R)
k = pis
    ⋆ Lam (pis
           ⋆ Lam (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) jp)))
                  (Con $ General $ Incl 0.05)
                  ⋆ Lam (observe' (Var Get) >>
                         (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) vlad)))
                          (Con $ General $ Incl 0.05)
                          ⋆ Lam (observe' (Var Get) >>
                                 makeBernoulli (Exists' (Lam (App (App (rel 1) (Var Get)) jp)))
                                 (Con $ General $ Incl 0.05)
                                 ⋆ Lam (observe' (Var Get) >>
                                        makeBernoulli (Exists' (Lam (App (App (rel 1) (Var Get)) vlad)))
                                        (Con $ General $ Incl 0.05)
                                        ⋆ Lam (observe' (Var Get) >>
                                               makeBernoulli (App (prop 0) jp)
                                               (Con $ General $ Incl 0.9)
                                               ⋆ Lam (observe' (Var Get) >>
                                                      makeBernoulli (App (prop 0) vlad)
                                                      (Con $ General $ Incl 0.9)
                                                      ⋆ Lam (observe' (Var Get) >>
                                                             (observe'
                                                              (And'
                                                               (And'
                                                                (Forall' (Lam (Imp' (Exists' (Lam (App (App (rel 0) (Var Get)) (Var (Weaken Get))))) (App (prop 0) (Var Get)))))
                                                                (Forall' (Lam (Imp' (Exists' (Lam (App (App (rel 1) (Var Get)) (Var (Weaken Get))))) (App (prop 0) (Var Get))))))
                                                              (App (App (rel 1) vlad) jp)) >>
                                                              η (Pair
                                                                 (Pair
                                                                  (Pair
                                                                   (Pair
                                                                    (Pair
                                                                     (Pair
                                                                      (Pair TT (Var (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get)))))))))
                                                                      (Var (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get))))))))
                                                                     (rel 1))
                                                                    (rel 0))
                                                                   (prop 0))
                                                                  (entity 1))
                                                                 (entity 0))))))))))))
  
-- | Literal listener
l0 :: γ ⊢ ('U ⟶ (Context1 ⟶ 'R) ⟶ 'R)
l0 = Lam (k ⋆
          Lam (
             observe'
             (App (App (Con (General (Interp (S Z))))
                   (Var (Weaken Get))) (Var Get)) >>
             η (Var Get)))

-- >>> evalβ $ App l0 (Con $ General $ Utt'' [Nothing, Nothing])
-- λ((((((𝟙(∃(λ(relation0(x)(jp)))) * (((𝟙(∃(λ(relation1(x)(jp)))) * (𝟙(relation0(jp)(jp)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π0⟩, π0⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 / 20)) + ((𝟙((∃(λ(relation1(x)(jp))) → ⊥)) * (𝟙(relation0(jp)(jp)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π0⟩, π0⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 20)))))) * (1 / 20)) + ((𝟙((∃(λ(relation0(x)(jp))) → ⊥)) * (((𝟙(∃(λ(relation1(x)(jp)))) * (𝟙(relation0(jp)(jp)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π0⟩, π0⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 / 20)) + ((𝟙((∃(λ(relation1(x)(jp))) → ⊥)) * (𝟙(relation0(jp)(jp)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π0⟩, π0⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 20)))))) * (1 + (-1 * (1 / 20))))) + ((((𝟙(∃(λ(relation0(x)(jp)))) * (((𝟙(∃(λ(relation1(x)(jp)))) * (𝟙(relation0(v)(jp)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π0⟩, π1⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 / 20)) + ((𝟙((∃(λ(relation1(x)(jp))) → ⊥)) * (𝟙(relation0(v)(jp)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π0⟩, π1⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 20)))))) * (1 / 20)) + ((𝟙((∃(λ(relation0(x)(jp))) → ⊥)) * (((𝟙(∃(λ(relation1(x)(jp)))) * (𝟙(relation0(v)(jp)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π0⟩, π1⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 / 20)) + ((𝟙((∃(λ(relation1(x)(jp))) → ⊥)) * (𝟙(relation0(v)(jp)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π0⟩, π1⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 20)))))) * (1 + (-1 * (1 / 20))))) + 0)) + (((((𝟙(∃(λ(relation0(x)(jp)))) * (((𝟙(∃(λ(relation1(x)(jp)))) * (𝟙(relation0(jp)(v)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π1⟩, π0⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 / 20)) + ((𝟙((∃(λ(relation1(x)(jp))) → ⊥)) * (𝟙(relation0(jp)(v)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π1⟩, π0⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 20)))))) * (1 / 20)) + ((𝟙((∃(λ(relation0(x)(jp))) → ⊥)) * (((𝟙(∃(λ(relation1(x)(jp)))) * (𝟙(relation0(jp)(v)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π1⟩, π0⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 / 20)) + ((𝟙((∃(λ(relation1(x)(jp))) → ⊥)) * (𝟙(relation0(jp)(v)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π1⟩, π0⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 20)))))) * (1 + (-1 * (1 / 20))))) + ((((𝟙(∃(λ(relation0(x)(jp)))) * (((𝟙(∃(λ(relation1(x)(jp)))) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π1⟩, π1⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 / 20)) + ((𝟙((∃(λ(relation1(x)(jp))) → ⊥)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π1⟩, π1⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 20)))))) * (1 / 20)) + ((𝟙((∃(λ(relation0(x)(jp))) → ⊥)) * (((𝟙(∃(λ(relation1(x)(jp)))) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π1⟩, π1⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 / 20)) + ((𝟙((∃(λ(relation1(x)(jp))) → ⊥)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⟨⟨⋄, π1⟩, π1⟩, relation1⟩, relation0⟩, property0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 20)))))) * (1 + (-1 * (1 / 20))))) + 0)) + 0)))

-- | Pragmatic speaker
s1' :: Integer -> γ ⊢ ((Context1 × 'U) ⟶ ('U ⟶ 'R) ⟶ 'R)
s1' α = Lam (App (Con $ General MakeUtts) (Var Get)
             ⋆ Lam (
                factor'
                (distr (l0 `App` Var Get) `App` (Fst $ Var (Weaken Get)) ^+ α) >>
                η (Var Get)))

s1 :: γ ⊢ ((Context1 × 'U) ⟶ ('U ⟶ 'R) ⟶ 'R)
s1 = s1' 1

-- | Pragmatic listener
l1 :: γ ⊢ ('U ⟶ (Context1 ⟶ 'R) ⟶ 'R)
l1 = Lam (k ⋆ Lam (
             factor'
             (App (distr (App s1 (Pair (Var Get) (Var (Weaken Get)))))
              (Var (Weaken Get))) >>
             η (Var Get)))

-- >>> mathematica $ evalPLogical $ normalForm $ expectedValue $ App l0 (nf_to_λ $ u'' [Nothing, Nothing]) ⋆ Lam (η (App (hmorph (S Z) (App (Con $ General EqGen) (Pair (sel' 1 (upd' jp (upd' vlad emp))) jp))) (Var Get)))
-- (81/16000000 + 81/800000 - 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 9/4000 - 9/80000 - 9/80000 + 9/1600000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/2000 - 81/40000 - 81/40000 + 81/800000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 9/200 - 9/4000 - 9/4000 + 9/80000 - 9/4000 + 9/80000 + 9/80000 - 9/1600000 - 81/2000 + 81/40000 + 81/40000 - 81/800000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/16000000 + 81/800000 - 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 9/4000 - 9/80000 - 9/80000 + 9/1600000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/2000 - 81/40000 - 81/40000 + 81/800000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 9/200 - 9/4000 - 9/4000 + 9/80000 - 9/4000 + 9/80000 + 9/80000 - 9/1600000 - 81/2000 + 81/40000 + 81/40000 - 81/800000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000)/(81/16000000 + 81/800000 - 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 9/4000 - 9/80000 - 9/80000 + 9/1600000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/2000 - 81/40000 - 81/40000 + 81/800000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 9/200 - 9/4000 - 9/4000 + 9/80000 - 9/4000 + 9/80000 + 9/80000 - 9/1600000 - 81/2000 + 81/40000 + 81/40000 - 81/800000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/16000000 + 81/800000 - 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 9/4000 - 9/80000 - 9/80000 + 9/1600000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/2000 - 81/40000 - 81/40000 + 81/800000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 9/200 - 9/4000 - 9/4000 + 9/80000 - 9/4000 + 9/80000 + 9/80000 - 9/1600000 - 81/2000 + 81/40000 + 81/40000 - 81/800000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/16000000 + 81/800000 - 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 9/4000 - 9/80000 - 9/80000 + 9/1600000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 81/2000 - 81/40000 - 81/40000 + 81/800000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 9/200 - 9/4000 - 9/4000 + 9/80000 - 9/4000 + 9/80000 + 9/80000 - 9/1600000 - 81/2000 + 81/40000 + 81/40000 - 81/800000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/16000000 + 81/800000 - 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/800000 - 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000 + 9/4000 - 9/80000 - 9/80000 + 9/1600000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 81/2000 - 81/40000 - 81/40000 + 81/800000 - 81/40000 + 81/800000 + 81/800000 - 81/16000000 + 9/200 - 9/4000 - 9/4000 + 9/80000 - 9/4000 + 9/80000 + 9/80000 - 9/1600000 - 81/2000 + 81/40000 + 81/40000 - 81/800000 + 81/40000 - 81/800000 - 81/800000 + 81/16000000)
