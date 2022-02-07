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
           -- ⋆ Lam (makeBernoulli (App (App (rel 0) jp) jp)
                  -- (Con $ General $ Incl 0.2)
                   -- ⋆ Lam (observe' (Var Get) >>
                         ⋆ Lam (η (Pair
                             (Pair
                              (Pair
                               (Pair
                                (Pair TT (Var (Weaken Get)))
                                (Var Get))
                               (rel 0))
                              (entity 1))
                             (entity 0))))

-- | Literal listener
l0 :: γ ⊢ ('U ⟶ (Context1 ⟶ 'R) ⟶ 'R)
l0 = Lam (k ⋆
          Lam (
             observe'
             (App (App (Con (General (Interp (S Z))))
                   (Var (Weaken Get))) (Var Get)) >>
             η (Var Get)))

-- >>> evalβ $ App l0 (Con $ General $ Utt'' [Nothing, Nothing])
-- λ((((((𝟙(relation0(v)(v)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π0⟩, π0⟩, relation0⟩, v⟩, jp⟩))) * (1 / 5)) + ((𝟙((relation0(v)(v) → ⊤)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π0⟩, π0⟩, relation0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 5))))) + ((((𝟙(relation0(v)(v)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π0⟩, π1⟩, relation0⟩, v⟩, jp⟩))) * (1 / 5)) + ((𝟙((relation0(v)(v) → ⊤)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π0⟩, π1⟩, relation0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 5))))) + 0)) + (((((𝟙(relation0(v)(v)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π1⟩, π0⟩, relation0⟩, v⟩, jp⟩))) * (1 / 5)) + ((𝟙((relation0(v)(v) → ⊤)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π1⟩, π0⟩, relation0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 5))))) + ((((𝟙(relation0(v)(v)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π1⟩, π1⟩, relation0⟩, v⟩, jp⟩))) * (1 / 5)) + ((𝟙((relation0(v)(v) → ⊤)) * (𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π1⟩, π1⟩, relation0⟩, v⟩, jp⟩))) * (1 + (-1 * (1 / 5))))) + 0)) + 0)))

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

-- >>> mathematica $ evalPLogical $ normalForm $ expectedValue $ App l0 (nf_to_λ $ u'' [Nothing, Nothing]) ⋆ Lam (η (App (hmorph (S Z) (App (Con $ General EqGen) (Pair (sel' 0 (upd' jp (upd' vlad emp))) jp))) (Var Get)))
-- (1 + 1)/(1 + 1 + 1 + 1)
