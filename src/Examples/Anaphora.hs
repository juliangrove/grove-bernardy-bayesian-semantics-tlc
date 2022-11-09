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
import qualified Models.Logical.FiniteLogical as FL
import TLC.HOAS
import qualified TLC.Terms as T


true' :: Exp T.T
true' = Con Tru
false' :: Exp T.T
false' = Con Fal
and' :: Exp T.T -> Exp T.T -> Exp T.T
and' φ ψ = Con And @@ φ @@ ψ
(∧) = and'
or' :: Exp T.T -> Exp T.T -> Exp T.T
or' φ ψ = Con Or @@ φ @@ ψ
(∨) = or'
imp' :: Exp T.T -> Exp T.T -> Exp T.T
imp' φ ψ = Con Imp @@ φ @@ ψ
(→) = imp'
forall :: Exp (α ⟶ T.T) -> Exp T.T
forall f = Con Forall @@ f
forall' f = forall $ Lam f
exists :: Exp (α ⟶ T.T) -> Exp T.T
exists f = Con Exists @@ f
exists' f = exists $ Lam f
equals' :: Exp a -> Exp a -> Exp T.T
equals' m n = Con Equals @@ m @@ n

prop :: Int -> Exp (T.E ':-> T.T)
prop i = Con $ T.Property i
rel :: Int -> Exp (T.E ':-> (T.E ⟶ T.T))
rel i = Con $ T.Relation i
vlad :: Exp T.E
vlad = Con T.Vlad
jp :: Exp T.E
jp = Con T.JP
emacs :: Exp T.E
emacs = Con T.JP
the_command :: Exp T.E
the_command = Con T.Vlad
entity :: Int -> Exp T.E
entity i = Con $ T.Entity i
height :: Exp (T.E ':-> T.R)
height = Con $ T.Height
human :: Exp (T.E ':-> T.T)
human = Con $ T.Human
θ :: Exp T.R
θ = Con $ T.Theta
emp :: Exp T.Γ
emp = Con $ Empty
upd :: Exp (T.E ':-> (T.Γ ⟶ T.Γ))
upd = Con $ Upd
upd' :: Exp T.E -> Exp T.Γ -> Exp T.Γ
upd' x c = upd @@ x @@ c
sel :: Int -> Exp (T.Γ ':-> T.E)
sel n = Con $ T.Sel n
sel' :: Int -> Exp T.Γ -> Exp T.E
sel' n c = sel n @@ c
incl :: Rational -> Exp T.R
incl n = Con $ Incl n

pis :: [Int] -> Exp (((T.Γ ⟶ T.E) ⟶ T.R) ⟶ T.R)
pis ns = Lam $ \k -> sum [ k @@ (Con $ Pi i) | i <- ns ]

makeBernoulli :: Exp T.T -> Exp T.R -> Exp ((T.T ⟶ T.R) ⟶ T.R)
makeBernoulli φ x = Lam $ \k -> (k @@ φ) * x + (k @@ (φ → false')) * (one - x)

hmorph' :: T.Witness n -> Exp α -> Exp (T.Context n ⟶ α)
hmorph' n = toHoas . T.hmorph n . fromHoas

ktx :: T.Witness n -> Exp ((T.Context n ⟶ T.R) ⟶ T.R)
ktx (T.S T.Z) =
  pis [0, 1] ⋆ \π ->
  pis [0, 1] ⋆ \π' ->
  makeBernoulli (exists' (\x -> rel 0 @@ x @@ jp)) (incl 0.05) ⋆ \φ0 ->
  makeBernoulli (exists' (\x -> rel 0 @@ x @@ vlad)) (incl 0.05) ⋆ \φ1 ->
  makeBernoulli (exists' (\x -> rel 1 @@ x @@ jp)) (incl 0.05) ⋆ \φ2 ->
  makeBernoulli (exists' (\x -> rel 1 @@ x @@ vlad)) (incl 0.05) ⋆ \φ3 ->
  makeBernoulli (prop 0 @@ jp) (incl 0.9) ⋆ \φ4 ->
  makeBernoulli (prop 0 @@ vlad) (incl 0.9) ⋆ \φ5 ->
  η (φ0 ∧ φ1 ∧ φ2 ∧ φ3 ∧ φ4 ∧ φ5 ∧
     (forall' (\x -> exists' (\y -> rel 0 @@ y @@ x) → (prop 0 @@ x))) ∧
     (forall' (\x -> exists' (\y -> rel 1 @@ y @@ x) → (prop 0 @@ x))) ∧
     (rel 1 @@ vlad @@ jp)) ⋆ \φ6 ->
  η (TT & φ6 & π & π' & rel 0 & entity 1 & entity 0)
ktx (T.S (T.S T.Z)) =
  pis [0, 1] ⋆ \π ->
  makeBernoulli (exists' (\x -> rel 1 @@ x @@ emacs)) (incl 0.05) ⋆ \φ0 ->
  makeBernoulli (exists' (\x -> rel 1 @@ x @@ the_command)) (incl 0.05) ⋆ \φ1 ->
  makeBernoulli (prop 0 @@ emacs) (incl 0.05) ⋆ \φ2 ->
  makeBernoulli (prop 0 @@ the_command) (incl 0.05) ⋆ \φ3 ->
  makeBernoulli (prop 1 @@ emacs) (incl 0.2) ⋆ \φ2 ->
  makeBernoulli (prop 1 @@ the_command) (incl 0.2) ⋆ \φ3 ->
  η (φ0 ∧ φ1 ∧ φ2 ∧ φ3 ∧
    forall' (\x -> exists' (\y -> rel 1 @@ y @@ x) → (prop 1 @@ x)) ∧
    forall' (\x -> prop 0 @@ x → (prop 1 @@ x)) ∧
    (rel 1 @@ the_command @@ emacs)) ⋆ \φ6 ->
  η (TT & φ6 & π & prop 0 & the_command & emacs)
ktx _ = error "k: not defined yet."


p1 :: Exp ((T.T ⟶ T.R) ⟶ T.R)
p1 =
  makeBernoulli (exists' (\x -> rel 0 @@ x @@ emacs)) (incl 0.05) ⋆ \φ0 ->
  makeBernoulli (prop 0 @@ emacs) (incl 0.2) ⋆ \φ1 ->
  η (φ0 ∧ φ1 ∧ (rel 0 @@ the_command @@ emacs))

p1' :: T.Unit ⊢ ((T.T ⟶ T.R) ⟶ T.R)
p1' = fromHoas p1

p2 :: Exp ((T.T ⟶ T.R) ⟶ T.R)
p2 =
  makeBernoulli (exists' (\x -> rel 0 @@ x @@ emacs)) (incl 0.05) ⋆ \φ0 ->
  makeBernoulli (prop 0 @@ emacs) (incl 0.2) ⋆ \φ1 ->
  observe (φ0 ∧ φ1 ∧ (forall' (\x -> exists' (\y -> rel 0 @@ y @@ x) → (prop 0 @@ x)))) >>
  η (φ0 ∧ φ1 ∧ (rel 0 @@ the_command @@ emacs))

p2' :: T.Unit ⊢ ((T.T ⟶ T.R) ⟶ T.R)
p2' = fromHoas p2

-- | Literal listener
l0 :: T.Witness n -> Exp (T.U ⟶ (T.Context n ⟶ T.R) ⟶ T.R)
l0 n =
  Lam $ \u ->
  ktx n ⋆ \k ->
  observe (hmorph' n (Con (T.Proposition 0)) @@ k ∧
           (Con (Interp n) @@ u @@ k)) >>
  η k
  
-- | Pragmatic speaker
s1' :: Equality (T.Context n)
    => T.Witness n -> Rational -> Exp ((T.Context n × T.U) ⟶ (T.U ⟶ T.R) ⟶ T.R)
s1' n α =
  Lam $ \k_u ->
  Con (MakeUtts n) @@ k_u ⋆ \u' ->
  factor (distr (l0 n @@ u') (Fst k_u) ^/ α) >>
  η u'
  
s1 :: Equality (T.Context n)
   => T.Witness n -> Exp ((T.Context n × T.U) ⟶ (T.U ⟶ T.R) ⟶ T.R)
s1 n = s1' n 0

-- | Pragmatic listener
l1' :: Equality (T.Context n)
    => Rational -> T.Witness n -> Exp (T.U ⟶ (T.Context n ⟶ T.R) ⟶ T.R)
l1' α n =
  Lam $ \u ->
  ktx n ⋆ \k ->
  factor (distr (s1' n α @@ (k & u)) u) >>
  η k

l1 :: Equality (T.Context n)
   => Rational -> T.Witness n -> T.Unit ⊢ (T.U ⟶ ((T.Context n ⟶ T.R) ⟶ T.R))
l1 α n = fromHoas (l1' α n) 
