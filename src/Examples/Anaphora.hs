{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Examples.Anaphora where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..), sum)
import Models.Integrals.Conversion
import Models.Integrals.Show
import Models.Logical.FiniteLogical
import TLC.Distributions
import TLC.Terms


pis :: [Int] -> γ ⊢ ((('Γ ⟶ 'E) ⟶ 'R) ⟶ 'R)
pis ns = Lam $ sum [ App (Var Get) (Con $ General $ Pi i) | i <- ns ]

k :: Witness n -> γ ⊢ ((Context n ⟶ 'R) ⟶ 'R)
k (S Z) =
  pis [0, 1] ⋆
  Lam (pis [0, 1] ⋆
       Lam (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) jp)))
            (Con $ General $ Incl 0.05) ⋆
            Lam (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) vlad)))
                 (Con $ General $ Incl 0.05) ⋆
                 Lam (makeBernoulli (Exists' (Lam (App (App (rel 1) (Var Get)) jp)))
                      (Con $ General $ Incl 0.05) ⋆
                      Lam (makeBernoulli (Exists' (Lam (App (App (rel 1) (Var Get)) vlad)))
                           (Con $ General $ Incl 0.05) ⋆
                           Lam (makeBernoulli (App (prop 0) jp)
                                (Con $ General $ Incl 0.9) ⋆
                                Lam (makeBernoulli (App (prop 0) vlad)
                                     (Con $ General $ Incl 0.9) ⋆
                                     Lam (η (And'
                                             (And' (Var Get)
                                              (And' (Var (Weaken Get))
                                               (And' (Var (Weaken (Weaken Get)))
                                                (And' (Var (Weaken (Weaken (Weaken Get))))
                                                 (And' (Var (Weaken (Weaken (Weaken (Weaken Get)))))
                                                  (Var (Weaken (Weaken (Weaken (Weaken (Weaken Get)))))))))))
                                             (And'
                                              (And'
                                               (Forall' (Lam (Imp' (Exists' (Lam (App (App (rel 0) (Var Get)) (Var (Weaken Get))))) (App (prop 0) (Var Get)))))
                                               (Forall' (Lam (Imp' (Exists' (Lam (App (App (rel 1) (Var Get)) (Var (Weaken Get))))) (App (prop 0) (Var Get))))))
                                              (App (App (rel 1) vlad) jp)))) ⋆
                                     Lam (η (Pair
                                             (Pair
                                              (Pair
                                               (Pair
                                                (Pair
                                                 (Pair TT
                                                  (Var Get))
                                                 (Var (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get)))))))))
                                                (Var (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get))))))))
                                               (rel 0))
                                              (entity 1))
                                             (entity 0))))))))))
k (S (S Z)) =
  pis [0, 1] ⋆
  Lam (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) jp)))
       (Con $ General $ Incl 0.05) ⋆
       Lam (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) vlad)))
            (Con $ General $ Incl 0.05) ⋆
             Lam (makeBernoulli (App (prop 0) jp)
                  (Con $ General $ Incl 0.05) ⋆
                  Lam (makeBernoulli (App (prop 0) vlad)
                       (Con $ General $ Incl 0.05) ⋆
                       Lam (makeBernoulli (App (prop 1) jp)
                            (Con $ General $ Incl 0.2) ⋆
                            Lam (makeBernoulli (App (prop 1) vlad)
                                 (Con $ General $ Incl 0.2) ⋆
                                 Lam (η
                                      (And'
                                       (And' (Var Get)
                                        (And' (Var (Weaken Get))
                                         (And' (Var (Weaken (Weaken Get)))
                                          (And' (Var (Weaken (Weaken (Weaken Get))))
                                           (And' (Var (Weaken (Weaken (Weaken (Weaken Get)))))
                                            (Var (Weaken (Weaken (Weaken (Weaken (Weaken Get)))))))))))
                                       (And'
                                        (And'
                                         (Forall' (Lam (Imp' (Exists' (Lam (App (App (rel 0) (Var Get)) (Var (Weaken Get))))) (App (prop 1) (Var Get)))))
                                         (Forall' (Lam (Imp' (App (prop 0) (Var Get)) (App (prop 1) (Var Get))))))
                                        (App (App (rel 0) vlad) jp)))) ⋆
                                 Lam (η (Pair
                                         (Pair
                                          (Pair
                                           (Pair
                                            (Pair TT
                                             (Var Get))
                                            (Var (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get))))))))
                                           (prop 0))
                                          (entity 1))
                                         (entity 0)))))))))
k _ = error "k: not defined yet."

-- | Literal listener
l0 :: Witness n -> γ ⊢ ('U ⟶ (Context n ⟶ 'R) ⟶ 'R)
l0 n = Lam (k n ⋆
            Lam (observe'
                 (hmorph n (Con $ Special $ Proposition 0) `App` Var Get
                  `And'` (Con (General (Interp n)) `App`
                          Var (Weaken Get) `App` Var Get)) >>
                 η (Var Get)))

-- | Pragmatic speaker
s1' :: Equality (Context n)
    => Witness n -> Rational -> γ ⊢ ((Context n × 'U) ⟶ ('U ⟶ 'R) ⟶ 'R)
s1' n α =
  Lam (Con (General $ MakeUtts n) `App` Var Get ⋆
       Lam (factor'
            (distr (l0 n `App` Var Get) `App` Fst (Var (Weaken Get)) ^/ α) >>
            η (Var Get)))

s1 :: Equality (Context n)
   => Witness n -> γ ⊢ ((Context n × 'U) ⟶ ('U ⟶ 'R) ⟶ 'R)
s1 n = s1' n 0

-- | Pragmatic listener
l1 :: Equality (Context n)
   => Rational -> Witness n -> γ ⊢ ('U ⟶ (Context n ⟶ 'R) ⟶ 'R)
l1 α n =
  Lam (k n ⋆
       Lam (factor'
            (distr (s1' n α `App` (Var Get `Pair` Var (Weaken Get)))
             `App` Var (Weaken Get)) >>
            η (Var Get)))
