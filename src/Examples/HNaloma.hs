{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RebindableSyntax #-}

module Examples.HNaloma where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..), sum)
import TLC.Terms (Context, Witness (..))
import TLC.HOAS
import qualified TLC.Terms as F


true' :: Exp 'T
true' = Con (Tru)
false' :: Exp 'T
false' = Con (Fal)
and' :: Exp 'T -> Exp 'T -> Exp 'T
and' φ ψ = App (App (Con (And)) φ) ψ
or' :: Exp 'T -> Exp 'T -> Exp 'T
or' φ ψ = App (App (Con (Or)) φ) ψ
imp' :: Exp 'T -> Exp 'T -> Exp 'T
imp' φ ψ = App (App (Con (Imp)) φ) ψ
forall' :: Exp (α1 ⟶ 'T) -> Exp 'T
forall' f = App (Con (Forall)) f
exists' :: Exp (α1 ⟶ 'T) -> Exp 'T
exists' f = App (Con (Exists)) f
equals' :: Exp a -> Exp a -> Exp 'T
equals' m n = App (App (Con (Equals)) m) n


prop :: Int -> Exp ('E ':-> 'T)
prop i = Con $ F.Property i
rel :: Int -> Exp ('E ':-> ('E ⟶ 'T))
rel i = Con $ F.Relation i
vlad :: Exp 'E
vlad = Con $ F.Vlad
jp :: Exp 'E
jp = Con $ F.JP
entity :: Int -> Exp 'E
entity i = Con $ F.Entity i
height :: Exp ('E ':-> 'R)
height = Con $ F.Height
human :: Exp ('E ':-> 'T)
human = Con $ F.Human
θ :: Exp 'R
θ = Con $ F.Theta
emp :: Exp 'Γ
emp = Con $ Empty
upd :: Exp ('E ':-> ('Γ ⟶ 'Γ))
upd = Con $ Upd
upd' :: Exp 'E -> Exp 'Γ -> Exp 'Γ
upd' x c = upd @@ x @@ c
sel :: Int -> Exp ('Γ ':-> 'E)
sel n = Con $ F.Sel n
sel' :: Int -> Exp 'Γ -> Exp 'E
sel' n c = sel n @@ c


pis :: [Int] -> Exp ((('Γ ⟶ 'E) ⟶ 'R) ⟶ 'R)
pis ns = Lam $ \k -> sum [ k @@ (Con $ Pi i) | i <- ns ]

makeBernoulli :: Exp 'T -> Exp 'R -> Exp (('T ⟶ 'R) ⟶ 'R)
makeBernoulli φ x = Lam $ \k -> (k @@ φ) * x +
                                (k @@ (imp' φ false')) * (one - x)

hmorph' :: F.Witness n -> Exp α -> Exp (F.Context n ⟶ α)
hmorph' n = toHoas . F.hmorph n . fromHoas

context :: Witness n -> Exp ((Context n ⟶ 'R) ⟶ 'R)
{-k (S Z) =
  pis [0, 1] ⋆
  Lam (pis [0, 1] ⋆
       Lam (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) jp)))
            (Con $ Incl 0.05) ⋆
            Lam (makeBernoulli (Exists' (Lam (App (App (rel 0) (Var Get)) vlad)))
                 (Con $ Incl 0.05) ⋆
                 Lam (makeBernoulli (Exists' (Lam (App (App (rel 1) (Var Get)) jp)))
                      (Con $ Incl 0.05) ⋆
                      Lam (makeBernoulli (Exists' (Lam (App (App (rel 1) (Var Get)) vlad)))
                           (Con $ Incl 0.05) ⋆
                           Lam (makeBernoulli (App (prop 0) jp)
                                (Con $ Incl 0.9) ⋆
                                Lam (makeBernoulli (App (prop 0) vlad)
                                     (Con $ Incl 0.9) ⋆
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
-}

(∧) :: Exp 'T -> Exp 'T -> Exp 'T
(∧) = and'

context (S (S Z)) =
  pis [0, 1] ⋆ \pie ->
  makeBernoulli (exists' (Lam $ \e -> (App (App (rel 0) e) jp))) 0.05 ⋆ \prop1 ->
  makeBernoulli (exists' (Lam $ \e -> (App (App (rel 0) e) vlad))) (0.05) ⋆ \prop2 -> 
  makeBernoulli (App (prop 0) jp) (0.05) ⋆ \prop3 -> 
  makeBernoulli (App (prop 0) vlad) (0.05) ⋆ \prop4 -> 
  makeBernoulli (App (prop 1) jp) (0.2) ⋆ \prop5 -> 
  makeBernoulli (App (prop 1) vlad) (0.2) ⋆ \prop6 ->
  η (Pair
     (Pair
      (Pair
       (Pair
        (Pair TT
         (prop1 ∧ prop2 ∧ prop3∧ prop4∧ prop5∧ prop6 ∧
          (forall' (Lam $ \e0 -> (imp' (exists' (Lam $ \e1 -> (App (App (rel 0) e1) e0))) (App (prop 1) e0))))
          ∧ (forall' (Lam $ \e0 -> (imp' (App (prop 0) e0) (App (prop 1) e0))))
          ∧ (App (App (rel 0) vlad) jp)))
        pie)
       (prop 0))
      (entity 1))
     (entity 0))
context _ = error "k: not defined yet."


-- | Literal listener
l0 :: Witness n -> Exp 'U -> Exp 'U -> Exp ((Context n ⟶ 'R) ⟶ 'R)
l0 n u u0 =
  context n ⋆ \k ->
  observe
  (hmorph' n (Con (F.Proposition 0)) @@ k ∧
   (Con (Interp n) @@ u @@ k)
      -- ∧ (Con ((Interp n)) @@ u0 @@ k) -- naloma paper has this somehow?
  ) >>
  η k

-- | Pragmatic speaker
s1' :: Equality (Context n)
    => Witness n -> Rational -> Exp (Context n) -> Exp 'U -> Exp (('U ⟶ 'R) ⟶ 'R)
s1' n α ctx u0 =
  (Con (MakeUtts n) @@ (ctx `Pair` u0)) ⋆ \u ->
  factor (distr (l0 n u u0) ctx ^/ α) >>
  η u

s1 :: Equality (Context n)
   => Witness n -> Exp (Context n) -> Exp 'U -> Exp (('U ⟶ 'R) ⟶ 'R)
s1 n = s1' n 0

-- | Pragmatic listener
l1' :: Equality (Context n)
   => Rational -> Witness n -> Exp 'U -> Exp ((Context n ⟶ 'R) ⟶ 'R)
l1' α n u =
  context n ⋆ \ctx ->
  -- adding observation here has no effects
  -- observe (interp u ctx)
  -- sufficient condition for this having no effects: (ctx,u ⊢ ⊥) ⇒ (s1Distr ctx u = 0)
  factor (distr (s1' n α ctx u) u) >>
  η ctx

l1 :: Equality (Context n) => Rational -> Witness n -> 'Unit ⊢ ('U ⟶ ((Context n ⟶ 'R) ⟶ 'R))
l1 α n = fromHoas (Lam (l1' α n)) 
