{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE LambdaCase #-}

module TLC.HOAS (Exp(..), (@@), module TLC.Terms,
                uniform, normal, (≥), measure, distr, average, observe,
                factor, fromHoas, (⋆), (>>), η, toHoas, π) where

import Prelude hiding ((>>), Num(..), Fractional(..))
import Algebra.Classes
import qualified TLC.Terms as F
import TLC.Terms (type (⊢), type(∈)(..), type (×),  type (⟶), Type(..), Con(..),
                  Equality)

import Unsafe.Coerce (unsafeCoerce)
import Type.Reflection ((:~:)(..))

data Key (a :: F.Type) = Key Int

compareKeys :: Key a -> Key b -> Maybe (a :~: b)
compareKeys (Key x) (Key y) = if x == y
                              then Just (unsafeCoerce Refl)
                              else Nothing

data Ctx γ where
  Entry :: Key a -> Ctx γ -> Ctx (γ × a)
  Nil :: Ctx 'F.Unit

newkey :: Ctx γ -> Key a
newkey Nil = Key 0
newkey (Entry (Key n) _) = Key (n + 1)

data Exp t where
  TT  :: Exp 'F.Unit
  Con :: F.Con a -> Exp a
  App :: Exp (a ⟶ b) -> Exp a -> Exp b
  Var :: Key a -> Exp a
  Lam :: forall a b. (Exp a -> Exp b) -> Exp (a ⟶ b)
  Pair :: Exp a -> Exp b -> Exp (a × b)
  Fst :: Exp (a × b) -> Exp a
  Snd :: Exp (a × b) -> Exp b

-- This actually converts a deBrujn level to the correct deBrujn index
-- depending on the context.
lk :: Ctx γ -> Key x -> x ∈ γ
lk (Entry k ρ) k' = case compareKeys k k' of
                      Just Refl -> F.Get
                      Nothing -> F.Weaken (lk ρ k')
lk Nil _ = error "fromHOAS: panic: variable not found"

fromHOAS :: Exp t -> Ctx γ -> γ ⊢ t
fromHOAS t0 k = case t0 of
  TT -> F.TT
  Con x -> F.Con x
  Var  i -> F.Var (lk k i)
  App  t u -> F.App (fromHOAS t k) (fromHOAS u k)
  Pair  t u -> F.Pair (fromHOAS t k) (fromHOAS u k)
  Fst t -> F.Fst (fromHOAS t k)
  Snd t -> F.Snd (fromHOAS t k)
  Lam t -> F.Lam (fromHOAS (t (Var key)) (Entry key k))
             where key = newkey k

fromHoas :: Exp t -> 'Unit ⊢ t
fromHoas e = fromHOAS e Nil

-- examples:
identity :: Exp (b ⟶ b)
identity = Lam $ \x -> x

twice :: Exp (b ⟶ (b ⟶ b) ⟶ b)
twice = Lam $ \x -> Lam $ \f -> f @@ (f @@ x)

-- >>> F.displayVs $ fromHOAS twice Empty
-- (λx.(λy.y(y(x))))

toHOAS :: forall γ t. γ ⊢ t -> Exp γ -> Exp t
toHOAS e ρ =
  let eval :: forall x. γ ⊢ x -> Exp x
      eval t = toHOAS t ρ
  in case e of
      F.TT -> TT
      F.Con x -> Con x
      F.Var v -> lk' v ρ
      F.Lam t -> Lam (\a -> (toHOAS t) (Pair ρ a))
      F.App t u -> App (eval t) (eval u)
      F.Pair t u -> Pair (eval t) (eval u)
      F.Fst t -> Fst (eval t)
      F.Snd t -> Snd (eval t)

lk' :: x ∈ γ -> Exp γ -> Exp x
lk' F.Get t = Snd t
lk' (F.Weaken v) t = lk' v (Fst t)

toHoas :: 'F.Unit ⊢ t -> Exp t
toHoas e = toHOAS e TT


η :: Exp α -> Exp ((α ⟶ r) ⟶ r)
η m = Lam $ \f -> f @@ m

-- (⋆) :: Exp ((α ⟶ r) ⟶ r) -> Exp (α ⟶ ((β ⟶ r) ⟶ r)) -> Exp ((β ⟶ r) ⟶ r)
-- m ⋆ k = Lam $ \f -> m @@ (Lam $ \x -> k @@ x @@ f)

(⋆) :: Exp ((α ⟶ r) ⟶ r) -> (Exp α -> Exp ((β ⟶ r) ⟶ r)) -> Exp ((β ⟶ r) ⟶ r)
m ⋆ k = Lam $ \f -> m @@ (Lam $ \x -> k x @@ f)

(>>) :: Exp (('F.Unit ⟶ r) ⟶ r) -> Exp ((β ⟶ r) ⟶ r) -> Exp ((β ⟶ r) ⟶ r)
m >> k = m ⋆ (\_ -> k) 

(≐) :: Equality α => Exp α -> Exp α -> Exp 'R
m ≐ n = Con (EqGen) @@ (Pair m n)

infixl @@
(@@) :: Exp (a ⟶ b) -> Exp a -> Exp b
(@@) = App


(∘) :: Exp (a1 ⟶ b) -> Exp (a2 ⟶ a1) -> Exp (a2 ⟶ b)
f ∘ g = Lam $ \x -> f @@ (g @@ x)


measure :: Exp ((α ⟶ 'R) ⟶ 'R) -> Exp 'R
measure p = p @@ (Lam $ \_ -> one)

average :: Exp (('R ⟶ 'R) ⟶ 'R) -> Exp 'R
average p = p @@ (Lam $ \x -> x)

distr :: Equality α => Exp ((α ⟶ 'R) ⟶ 'R) -> Exp α -> Exp 'R
distr p x = p @@ (Lam $ \y -> y ≐ x) / measure p

instance Additive (Exp 'R) where
  zero = Con (Incl 0)
  x + y  = Con (Addi) @@ x @@ y
instance AbelianAdditive (Exp 'R)
instance Group (Exp 'R) where
  negate = App (App (Con Mult) (Con (Incl (-1))))
instance Multiplicative (Exp 'R) where
  one = Con (Incl 1)
  x * y  = Con Mult @@ x @@ y
  x ^+ y = Con Expo @@ x @@ fromInteger y
instance Division (Exp 'R) where
  x / y  = Con Divi @@ x @@ y
instance Field (Exp 'R) where
  fromRational = Con . Incl 
instance Scalable (Exp 'R) (Exp 'R) where
  (*^) = (*)
instance Ring (Exp 'R) where
  fromInteger = Con . Incl . fromInteger
instance Roots (Exp 'R) where
  x ^/ y = Con Expo @@ x @@ fromRational y

uniform :: Rational -> Rational -> Exp (('R ⟶ 'R) ⟶ 'R)
uniform x y = App (Con Uni) (Pair (Con $ Incl x) (Con $ Incl y))

normal :: Rational -> Rational -> Exp (('R ⟶ 'R) ⟶ 'R)
normal x y = App (Con Nml) (Pair (Con $ Incl x) (Con $ Incl y))

factor :: Exp 'R -> Exp (('Unit ⟶ 'R) ⟶ 'R)
factor x = Lam (\k -> (k @@ TT) * x)

observe :: Exp 'T -> Exp (('Unit ⟶ 'R) ⟶ 'R)
observe x = factor (Con Indi @@ x)  

(≥) :: Exp 'R -> Exp 'R -> Exp 'T
x ≥ y = Con GTE @@ x @@ y 

π :: α ∈ κ -> Exp κ -> Exp α
π Get κ = Snd κ
π (Weaken i) κ = π i (Fst κ)
