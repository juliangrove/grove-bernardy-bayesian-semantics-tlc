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


true' :: Exp 'T
true' = Con Tru
false' :: Exp 'T
false' = Con Fal
and' :: Exp 'T -> Exp 'T -> Exp 'T
and' φ ψ = Con And @@ φ @@ ψ
(∧) = and'
or' :: Exp 'T -> Exp 'T -> Exp 'T
or' φ ψ = Con Or @@ φ @@ ψ
(∨) = or'
imp' :: Exp 'T -> Exp 'T -> Exp 'T
imp' φ ψ = Con Imp @@ φ @@ ψ
(→) = imp'
forall :: Exp (α ⟶ 'T) -> Exp 'T
forall f = Con Forall @@ f
forall' f = forall $ Lam f
exists :: Exp (α ⟶ 'T) -> Exp 'T
exists f = Con Exists @@ f
exists' f = exists $ Lam f
equals' :: Exp a -> Exp a -> Exp 'T
equals' m n = Con Equals @@ m @@ n

prop :: Int -> Exp ('E ':-> 'T)
prop i = Con $ T.Property i
rel :: Int -> Exp ('E ':-> ('E ⟶ 'T))
rel i = Con $ T.Relation i
vlad :: Exp 'E
vlad = Con T.Vlad
jp :: Exp 'E
jp = Con T.JP
emacs :: Exp 'E
emacs = Con T.JP
the_command :: Exp 'E
the_command = Con T.Vlad
entity :: Int -> Exp 'E
entity i = Con $ T.Entity i
height :: Exp ('E ':-> 'R)
height = Con $ T.Height
human :: Exp ('E ':-> 'T)
human = Con $ T.Human
θ :: Exp 'R
θ = Con $ T.Theta
emp :: Exp 'Γ
emp = Con $ Empty
upd :: Exp ('E ':-> ('Γ ⟶ 'Γ))
upd = Con $ Upd
upd' :: Exp 'E -> Exp 'Γ -> Exp 'Γ
upd' x c = upd @@ x @@ c
sel :: Int -> Exp ('Γ ':-> 'E)
sel n = Con $ T.Sel n
sel' :: Int -> Exp 'Γ -> Exp 'E
sel' n c = sel n @@ c
incl :: Rational -> Exp 'R
incl n = Con $ Incl n

pis :: [Int] -> Exp ((('Γ ⟶ 'E) ⟶ 'R) ⟶ 'R)
pis ns = Lam $ \k -> sum [ k @@ (Con $ Pi i) | i <- ns ]

makeBernoulli :: Exp 'T -> Exp 'R -> Exp (('T ⟶ 'R) ⟶ 'R)
makeBernoulli φ x = Lam $ \k -> (k @@ φ) * x + (k @@ (φ → false')) * (one - x)

hmorph' :: T.Witness n -> Exp α -> Exp (T.Context n ⟶ α)
hmorph' n = toHoas . T.hmorph n . fromHoas

ktx :: T.Witness n -> Exp ((T.Context n ⟶ 'R) ⟶ 'R)
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


p1 :: Exp (('T ⟶ 'R) ⟶ 'R)
p1 =
  makeBernoulli (exists' (\x -> rel 0 @@ x @@ emacs)) (incl 0.05) ⋆ \φ0 ->
  makeBernoulli (prop 0 @@ emacs) (incl 0.2) ⋆ \φ1 ->
  η (φ0 ∧ φ1 ∧ (rel 0 @@ the_command @@ emacs))

p1' :: 'Unit ⊢ (('T ⟶ 'R) ⟶ 'R)
p1' = fromHoas p1

p2 :: Exp (('T ⟶ 'R) ⟶ 'R)
p2 =
  makeBernoulli (exists' (\x -> rel 0 @@ x @@ emacs)) (incl 0.05) ⋆ \φ0 ->
  makeBernoulli (prop 0 @@ emacs) (incl 0.2) ⋆ \φ1 ->
  observe (φ0 ∧ φ1 ∧ (forall' (\x -> exists' (\y -> rel 0 @@ y @@ x) → (prop 0 @@ x)))) >>
  η (φ0 ∧ φ1 ∧ (rel 0 @@ the_command @@ emacs))

p2' :: 'Unit ⊢ (('T ⟶ 'R) ⟶ 'R)
p2' = fromHoas p2

-- | Literal listener
l0 :: T.Witness n -> Exp ('U ⟶ (T.Context n ⟶ 'R) ⟶ 'R)
l0 n =
  Lam $ \u ->
  ktx n ⋆ \k ->
  observe (hmorph' n (Con (T.Proposition 0)) @@ k ∧
           (Con (Interp n) @@ u @@ k)) >>
  η k
  
-- | Pragmatic speaker
s1' :: Equality (T.Context n)
    => T.Witness n -> Rational -> Exp ((T.Context n × 'U) ⟶ ('U ⟶ 'R) ⟶ 'R)
s1' n α =
  Lam $ \k_u ->
  Con (MakeUtts n) @@ k_u ⋆ \u' ->
  factor (distr (l0 n @@ u') (Fst k_u) ^/ α) >>
  η u'
  
s1 :: Equality (T.Context n)
   => T.Witness n -> Exp ((T.Context n × 'U) ⟶ ('U ⟶ 'R) ⟶ 'R)
s1 n = s1' n 0

-- | Pragmatic listener
l1' :: Equality (T.Context n)
    => Rational -> T.Witness n -> Exp ('U ⟶ (T.Context n ⟶ 'R) ⟶ 'R)
l1' α n =
  Lam $ \u ->
  ktx n ⋆ \k ->
  factor (distr (s1' n α @@ (k & u)) u) >>
  η k

l1 :: Equality (T.Context n)
   => Rational -> T.Witness n -> 'Unit ⊢ ('U ⟶ ((T.Context n ⟶ 'R) ⟶ 'R))
l1 α n = fromHoas (l1' α n) 
