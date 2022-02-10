{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Examples.Anaphora where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import Models.Integrals.Conversion
import Models.Integrals.Show
import Models.Logical.FiniteLogical
import TLC.Distributions
import TLC.Terms


pis :: γ ⊢ ((('Γ ⟶ 'E) ⟶ 'R) ⟶ 'R)
pis = nf_to_λ $ toFinite [ Neu $ NeuCon $ General $ Pi 0
                         , Neu $ NeuCon $ General $ Pi 1 ]

k :: Witness n -> γ ⊢ ((Context n ⟶ 'R) ⟶ 'R)
k (S Z) =
  pis ⋆
  Lam (pis ⋆
       Lam (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) jp)))
            (Con $ General $ Incl 0.05) ⋆
            Lam (observe' (Var Get) >>
                  (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) vlad)))
                   (Con $ General $ Incl 0.05) ⋆
                   Lam (observe' (Var Get) >>
                        makeBernoulli (Exists' (Lam (App (App (rel 1) (Var Get)) jp)))
                        (Con $ General $ Incl 0.05) ⋆
                        Lam (observe' (Var Get) >>
                             makeBernoulli (Exists' (Lam (App (App (rel 1) (Var Get)) vlad)))
                             (Con $ General $ Incl 0.05) ⋆
                             Lam (observe' (Var Get) >>
                                  makeBernoulli (App (prop 0) jp)
                                  (Con $ General $ Incl 0.9) ⋆
                                  Lam (observe' (Var Get) >>
                                       makeBernoulli (App (prop 0) vlad)
                                       (Con $ General $ Incl 0.9) ⋆
                                       Lam (observe' (Var Get) >>
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
k (S (S Z)) =
  pis ⋆
  Lam (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) jp)))
       (Con $ General $ Incl 0.05) ⋆
       Lam (observe' (Var Get) >>
            (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) vlad)))
             (Con $ General $ Incl 0.05) ⋆
             Lam (observe' (Var Get) >>
                  makeBernoulli (App (prop 0) jp)
                  (Con $ General $ Incl 0.05) ⋆
                  Lam (observe' (Var Get) >>
                       makeBernoulli (App (prop 0) vlad)
                       (Con $ General $ Incl 0.05) ⋆
                       Lam (observe' (Var Get) >>
                            makeBernoulli (App (prop 1) jp)
                            (Con $ General $ Incl 0.2) ⋆
                            Lam (observe' (Var Get) >>
                                 makeBernoulli (App (prop 1) vlad)
                                 (Con $ General $ Incl 0.2) ⋆
                                 Lam (observe' (Var Get) >>
                                      (observe'
                                       (And'
                                        (And'
                                         (Forall' (Lam (Imp' (Exists' (Lam (App (App (rel 0) (Var Get)) (Var (Weaken Get))))) (App (prop 1) (Var Get)))))
                                         (Forall' (Lam (Imp' (App (prop 0) (Var Get)) (App (prop 1) (Var Get))))))
                                        (App (App (rel 0) vlad) jp)) >>
                                       η (Pair
                                          (Pair
                                           (Pair
                                            (Pair TT (Var (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get))))))))
                                            (prop 0))
                                           (entity 1))
                                          (entity 0)))))))))))
k _ = error "k: not defined yet."

k1 :: γ ⊢ Context2
k1 = Pair
     (Pair
      (Pair
       (Pair TT (Con $ General $ Pi 1))
       (prop 0))
      (entity 1))
     (entity 0)

-- | Literal listener
l0 :: Witness n -> γ ⊢ ('U ⟶ (Context n ⟶ 'R) ⟶ 'R)
l0 n = Lam (k n ⋆
            Lam (observe'
                 (App (App (Con (General (Interp n)))
                       (Var (Weaken Get))) (Var Get)) >>
                 η (Var Get)))

-- >>> displayVs $ evalβ $ s1' (S (S Z)) 1

-- | Pragmatic speaker
s1' :: Equality (Context n)
    => Witness n -> Rational -> γ ⊢ ((Context n × 'U) ⟶ ('U ⟶ 'R) ⟶ 'R)
s1' n α =
  Lam (App (Con $ General $ MakeUtts n) (Var Get)
       ⋆ Lam (factor'
              (distr (l0 n `App` Var Get) `App`
               (Fst $ Var (Weaken Get)) ^/ α) >>
              η (Var Get)))

s1 :: Equality (Context n)
   => Witness n -> γ ⊢ ((Context n × 'U) ⟶ ('U ⟶ 'R) ⟶ 'R)
s1 n = s1' n 0.5

-- | Pragmatic listener
l1 :: Equality (Context n)
   => Witness n -> γ ⊢ ('U ⟶ (Context n ⟶ 'R) ⟶ 'R)
l1 n =
  Lam (k n ⋆ Lam (factor'
                  (App (distr (App (s1 n) (Pair (Var Get) (Var (Weaken Get)))))
                   (Var (Weaken Get))) >>
                  η (Var Get)))
