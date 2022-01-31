{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE LambdaCase #-}

module Terms.HOAS where

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

fromHOAS :: Exp t -> Ctx γ -> (⊢)γ t
fromHOAS t0 k = case t0 of
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
twice = Lam $ \x -> Lam $ \f -> App f (App f x)



  

