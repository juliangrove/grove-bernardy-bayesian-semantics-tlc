{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Examples.Anaphora where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Integrals
import Models.Logical.Logical
import TLC.Distributions
import TLC.Terms


pis :: γ ⊢ ((('Γ ⟶ 'E) ⟶ 'R) ⟶ 'R)
pis = toFinite [Con $ General $ Pi 0, Con $ General $ Pi 1]

k :: γ ⊢ ((Context1 ⟶ 'R) ⟶ 'R)
k = pis
    ⋆ Lam (pis
           ⋆ Lam
           (η (Pair
               (Pair
                (Pair
                 (Pair
                  (Pair TT (Var (Weaken Get)))
                  (Var Get))
                 (Con (Special $ Relation 0)))
                vlad)
               vlad)))

-- | Literal listener
l0 :: γ ⊢ ('U ⟶ (Context1 ⟶ 'R) ⟶ 'R)
l0 = Lam (k ⋆
          Lam (
             observe'
             (App (App (Con (General (Interp (S Z))))
                   (Var (Weaken Get))) (Var Get)) >>
             η (Var Get)))

-- >>> evalβ $ App l0 (Con $ General $ Utt'' [Nothing, Nothing])
-- λ((((𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π0⟩, π0⟩, relation0⟩, v⟩, v⟩)) + ((𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π0⟩, π1⟩, relation0⟩, v⟩, v⟩)) + 0)) + (((𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π1⟩, π0⟩, relation0⟩, v⟩, v⟩)) + ((𝟙(relation0(v)(v)) * x(⟨⟨⟨⟨⟨⋄, π1⟩, π1⟩, relation0⟩, v⟩, v⟩)) + 0)) + 0)))



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

-- >>> evalβ $ App l1 (u'' [Nothing, Nothing])
-- λ(((((((((((((𝟙(relation0(*** Exception: src/TLC/Terms.hs:437:21-46: Non-exhaustive patterns in Con (Special
