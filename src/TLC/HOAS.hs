{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE LambdaCase #-}

module TLC.HOAS where

import qualified TLC.Terms as F
import TLC.Terms (type (⊢), type(∈)(..), type (×),  type (⟶))

import Unsafe.Coerce (unsafeCoerce)
import Type.Reflection ((:~:)(..))

data Key (a :: F.Type) = Key Int

compareKeys :: Key a -> Key b -> Maybe (a :~: b)
compareKeys (Key x) (Key y) = if x == y then Just (unsafeCoerce Refl) else Nothing

data Ctx γ where
  Entry :: Key a -> Ctx γ -> Ctx (γ × a)
  Empty :: Ctx 'F.Unit

newkey :: Ctx γ -> Key a
newkey Empty = Key 0
newkey (Entry (Key n) _) = Key (n+1)

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
lk Empty _ = error "fromHOAS: panic"

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

-- examples:
identity :: Exp (b ⟶ b)
identity = Lam $ \x -> x

twice :: Exp (b ⟶ ((b ⟶ b) ⟶ b))
twice = Lam $ \x -> Lam $ \f -> f `App` (f `App` x)

infixl `App`

-- >>> displayVs $ fromHOAS twice Terms.HOAS.Empty
-- (λx.(λy.y(y(x))))
{-
toHOAS :: forall γ t. γ ⊢ t -> Exp γ -> Exp t
toHOAS e ρ =
  let eval :: forall x. γ ⊢ x -> Exp x
      eval t = toHOAS' t ρ
  in case e of
      F.TT -> TT
      F.Con x -> Con x
      F.Var v -> lk' v ρ
      F.Lam t -> Lam (\a -> App (toHOAS t) (Pair ρ a))
      F.App t u -> App (eval t) (eval u)
      F.Pair t u -> Pair (eval t) (eval u)
      F.Fst t -> Fst (eval t)
      F.Snd t -> Snd (eval t)

lk' :: x ∈ γ -> Exp γ -> Exp x
lk' F.Get t = Snd t
lk' (F.Weaken v) t = lk' v (Fst t)

toHOAS'' :: γ ⊢ t -> Exp (γ ⟶ t)
toHOAS'' e = Lam (toHOAS e)

toHOAS' :: 'F.Unit ⊢ t -> Exp t
toHOAS' e = (toHOAS'' e) `App` TT


η :: Exp α -> Exp ((α ⟶ r) ⟶ r)
η m = Lam $ \f -> f `App` m

(⋆) :: Exp ((α ⟶ r) ⟶ r) -> Exp (α ⟶ ((β ⟶ r) ⟶ r)) -> Exp ((β ⟶ r) ⟶ r)
m ⋆ k = Lam $ \f -> m `App` (Lam $ \x -> k `App` x `App` f)

(>>) :: Exp (('F.Unit ⟶ r) ⟶ r) -> Exp ((β ⟶ r) ⟶ r) -> Exp ((β ⟶ r) ⟶ r)
m >> k = m ⋆ Lam  (\_ -> k) 


-- distr :: F.Equality α => Exp ((α ⟶ 'F.R) ⟶ 'F.R) -> Exp (α ⟶ 'F.R)
-- distr p = Lam $ \x -> -- (App (wkn p) (Lam ((Var Get) ≐ (Var (Weaken Get)))) / measure (wkn p))

-}
