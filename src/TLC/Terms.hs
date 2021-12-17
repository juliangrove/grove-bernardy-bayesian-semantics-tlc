{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TLC.Terms where

import Data.Functor.Identity
import Prelude hiding (Monad(..))
import TLC.RN

data Type = E | T | R | U | Γ
          | Type :-> Type
          | Unit
          | Type :× Type

data (α :: Type) ∈ (γ :: Type) where
  Get :: α ∈ (α × γ)
  Weaken :: α ∈ γ -> α ∈ (β × γ)
deriving instance Show (α ∈ γ)

type α × β = α ':× β
type α ⟶ β = α ':-> β

data Con α where
  U1 :: Con U
  U2 :: Con U
  U3 :: Con U
  Rl :: Double -> Con R
  Indi :: Con (T ⟶ R)
  Mult :: Con (R ⟶ (R ⟶ R))
  Nml :: Con ((R × R) ⟶ ((R ⟶ R) ⟶ R))
  Distr :: Con (((α ⟶ R) ⟶ R) ⟶ (α ⟶ R))
  Tru :: Con T
  Fal :: Con T
  And :: Con (T ⟶ (T ⟶ T))
  Or :: Con (T ⟶ (T ⟶ T))
  Imp :: Con (T ⟶ (T ⟶ T))
  Exists :: Con ((α ⟶ T) ⟶ T)
  Forall :: Con ((α ⟶ T) ⟶ T)
  Height :: Con (E ⟶ R)
  Human :: Con (E ⟶ T)
  Theta :: Con R
  GTE :: Con (R ⟶ (R ⟶ T))
  Empty :: Con Γ
  Upd :: Con (E ⟶ (Γ ⟶ Γ))
  Sel :: Con (Γ ⟶ E)
deriving instance Show (Con α)

-- Well-typed terms.
data γ ⊢ α where
  Var :: α ∈ γ -> γ ⊢ α
  Con :: Con α -> γ ⊢ α
  App :: γ ⊢ (α ⟶ β) -> γ ⊢ α -> γ ⊢ β
  Lam :: (α × γ) ⊢ β -> γ ⊢ (α ⟶ β)
  Fst :: γ ⊢ (α × β) -> γ ⊢ α
  Snd :: γ ⊢ (α × β) -> γ ⊢ β
  TT :: γ ⊢ Unit
  Pair :: γ ⊢ α -> γ ⊢ β -> γ ⊢ (α × β)
deriving instance Show (γ ⊢ t)

subst :: (α × γ) ⊢ β -> γ ⊢ α -> γ ⊢ β
subst (Var Get) t = t
subst (Var (Weaken i)) t = Var i
subst (Con c) t = Con c
subst (App m n) t = App (subst m t) (subst n t)
subst (Lam m) t = Lam $ subst (exch m) (wkn t)
subst (Fst m) t = Fst $ subst m t
subst (Snd m ) t = Snd $ subst m t
subst TT t = TT
subst (Pair m n) t = Pair (subst m t) (subst n t)

evalstepβ :: γ ⊢ α -> γ ⊢ α
evalstepβ (Var i) = Var i
evalstepβ (App m n) = case m of
                        Lam m' -> subst m' n
                        _ -> App (evalstepβ m) (evalstepβ n)
evalstepβ (Lam m) = Lam $ evalstepβ m
evalstepβ (Fst m) = case m of
                      Pair m' n' -> evalstepβ m'
                      _ -> Fst $ evalstepβ m
evalstepβ (Snd m) = case m of
                      Pair m' n' -> evalstepβ n'
                      _ -> Snd $ evalstepβ m
evalstepβ TT = TT
evalstepβ (Pair m n) = Pair (evalstepβ m) (evalstepβ n)

normalF :: γ ⊢ α -> Bool
normalF (Var i) = True
normalF (Con c) = True
normalF (App m n) = case m of
                      Lam m' -> False
                      _-> normalF m && normalF n
normalF (Lam m) = normalF m
normalF (Fst m) = case m of
                    Pair m' n' -> False
                    _ -> normalF m
normalF (Snd m) = case m of
                    Pair m' n' -> False
                    _ -> normalF m
normalF TT = True
normalF (Pair m n) = normalF m && normalF n

evalβ :: γ ⊢ α -> γ ⊢ α
evalβ m = case normalF m of
            True -> m
            False -> evalβ (evalstepβ m)

lft :: (α ∈ γ -> α ∈ δ) -> α ∈ (β × γ) -> α ∈ (β × δ)
lft f Get = Get
lft f (Weaken i) = Weaken $ f i

π :: α ∈ κ -> γ ⊢ κ -> γ ⊢ α
π Get γ = Fst γ
π (Weaken i) γ = π i (Snd γ)

type Context
  = (E ⟶ R × (E ⟶ T × (R × ((R ⟶ (R ⟶ T)) × (Γ × ((E ⟶ (Γ ⟶ Γ)) × ((Γ ⟶ E) × Unit)))))))

findC :: Con α -> α ∈ Context
findC Height = Get
findC Human = Weaken Get
findC Theta = Weaken (Weaken Get)
findC GTE = Weaken (Weaken (Weaken Get))
findC Empty = Weaken (Weaken (Weaken (Weaken Get)))
findC Upd = Weaken (Weaken (Weaken (Weaken (Weaken Get))))
findC Sel = Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get)))))

rename :: (∀α. α ∈ γ -> α ∈ δ) -> γ ⊢ β -> δ ⊢ β
rename f (Var i) = Var $ f i
rename f (Con c) = (Con c)
rename f (App m n) = App (rename f m) (rename f n)
rename f (Lam m) = Lam $ rename (lft f) m
rename f (Fst m) = Fst $ rename f m
rename f (Snd m) = Snd $ rename f m
rename f (Pair m n) = Pair (rename f m) (rename f n)

wkn :: γ ⊢ α -> (β × γ) ⊢ α
wkn = rename Weaken

exch :: (α × (β × γ)) ⊢ ω -> (β × (α × γ)) ⊢ ω
exch = rename $ \case
  Get -> Weaken Get
  Weaken Get -> Get

contr :: (α × (α × γ)) ⊢ β -> (α × γ) ⊢ β
contr = rename $ \case
  Get -> Get
  Weaken i -> i

hmorph0 :: γ ⊢ α -> (Context × γ) ⊢ α
hmorph0 (Var i) = Var (Weaken i)
hmorph0 (App m n) = App (hmorph0 m) (hmorph0 n)
hmorph0 (Lam m) = Lam $ exch (hmorph0 m)
hmorph0 (Fst m) = Fst $ hmorph0 m
hmorph0 (Snd m) = Snd $ hmorph0 m
hmorph0 (Pair m n) = Pair (hmorph0 m) (hmorph0 n)
hmorph0 (Con c) = π (findC c) (Var Get)

hmorph :: γ ⊢ α -> γ ⊢ (Context ⟶ α)
hmorph m = Lam (hmorph0 m)

-- >>> Con (RN (Integral (Normal (Lit 0) (Lit 1)) (Lit (-1)) (Lit 1) (\x -> RNV x)))
-- Con (RN Normal 0.0 1.0(-1.0, 1.0)x:(x))

η :: γ ⊢ α -> γ ⊢ ((α ⟶ R) ⟶ R)
η m = Lam (App (Var Get) (wkn m))

(>>=) :: γ ⊢ ((α ⟶ R) ⟶ R) -> γ ⊢ (α ⟶ ((β ⟶ R) ⟶ R)) -> γ ⊢ ((β ⟶ R) ⟶ R)
m >>= k
  = Lam (App (wkn m) (Lam (App (App (wkn (wkn k)) (Var Get)) (Var (Weaken Get)))))

(>>) :: γ ⊢ ((Unit ⟶ R) ⟶ R) -> γ ⊢ ((β ⟶ R) ⟶ R) -> γ ⊢ ((β ⟶ R) ⟶ R)
m >> k = m >>= Lam (wkn k)
