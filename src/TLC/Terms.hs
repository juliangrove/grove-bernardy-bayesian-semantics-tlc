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

data Logical α where
  Tru :: Logical T
  Fal :: Logical T
  And :: Logical (T ⟶ (T ⟶ T))
  Or :: Logical (T ⟶ (T ⟶ T))
  Imp :: Logical (T ⟶ (T ⟶ T))
  Forall :: Logical ((α ⟶ T) ⟶ T)
  Exists :: Logical ((α ⟶ T) ⟶ T)
  Equals :: Logical (α ⟶ (α ⟶ T))

instance Show (Logical α) where
  show Tru = "⊤"
  show Fal = "⊥"
  show And = "(∧)"
  show Or = "(∨)"
  show Imp = "(→)"
  show Forall = "∀"
  show Exists = "∃"
  show Equals = "(=)"
  
data Rl α where
  Incl :: Double -> Rl R
  Indi :: Rl (T ⟶ R)
  Mult :: Rl (R ⟶ (R ⟶ R))
  Nml :: Rl ((R × R) ⟶ ((R ⟶ R) ⟶ R))
  Distr :: Rl (((α ⟶ R) ⟶ R) ⟶ (α ⟶ R))

instance Show (Rl α) where
  show (Incl x) = show x
  show Indi = "𝟙"
  show Mult = "(*)"
  show Nml = "Normal"
  show Distr = "Distr"

data Special α where
  Utt :: Int -> Special U
  Height :: Special (E ⟶ R)
  Human :: Special (E ⟶ T)
  Theta :: Special R
  GTE :: Special (R ⟶ (R ⟶ T))
  Empty :: Special Γ
  Upd :: Special (E ⟶ (Γ ⟶ Γ))
  Sel :: Special (Γ ⟶ E)

instance Show (Special α) where
  show (Utt i) = "U" ++ show i
  show Height = "height"
  show Human = "human"
  show Theta = "θ"
  show GTE = "(≥)"
  show Empty = "ε"
  show Upd = "(∷)"
  show Sel = "sel"

data Con α where
  Logical :: Logical α -> Con α
  Rl :: Rl α -> Con α
  Special :: Special α -> Con α

instance Show (Con α) where
  show (Logical c) = show c
  show (Rl c) = show c
  show (Special c) = show c

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

instance Show (γ ⊢ α) where
  show (Var Get) = "x"
  show (Var (Weaken i)) = show (Var i) ++ "'"
  show (App (App (Con (Logical And)) p) q)
    = "(" ++ show p ++ " ∧ " ++ show q ++ ")"
  show (App (App (Con (Logical Or)) p) q)
    = "(" ++ show p ++ " ∨ " ++ show q ++ ")"
  show (App (App (Con (Logical Imp)) p) q)
    = "(" ++ show p ++ " → " ++ show q ++ ")"
  show (App (App (Con (Logical Equals)) m) n)
    = "(" ++ show m ++ " = " ++ show n ++ ")"
  show (App (App (Con (Special GTE)) m) n)
    = "(" ++ show m ++ " ≥ " ++ show n ++ ")"
  show (App (App (Con (Special Upd)) m) n)
    = "(" ++ show m ++ "∷" ++ show n ++ ")"
  show (App m n) = show m ++ "(" ++ show n ++ ")"
  show (Con c) = show c
  show (Lam m) = "λ" ++ show m
  show (Fst m) = "(π₁ " ++ show m ++ ")"
  show (Snd m) = "(π₂" ++ show m ++ ")"
  show TT = "⋄"
  show (Pair m n) = "⟨" ++ show m ++ ", " ++ show n ++ "⟩"

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

findC :: Special α -> α ∈ Context
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
hmorph0 (Con (Special c)) = π (findC c) (Var Get)
hmorph0 (Con c) = Con c

hmorph :: γ ⊢ α -> γ ⊢ (Context ⟶ α)
hmorph m = Lam (hmorph0 m)

η :: γ ⊢ α -> γ ⊢ ((α ⟶ R) ⟶ R)
η m = Lam (App (Var Get) (wkn m))

(>>=) :: γ ⊢ ((α ⟶ R) ⟶ R) -> γ ⊢ (α ⟶ ((β ⟶ R) ⟶ R)) -> γ ⊢ ((β ⟶ R) ⟶ R)
m >>= k
  = Lam (App (wkn m) (Lam (App (App (wkn (wkn k)) (Var Get)) (Var (Weaken Get)))))

(>>) :: γ ⊢ ((Unit ⟶ R) ⟶ R) -> γ ⊢ ((β ⟶ R) ⟶ R) -> γ ⊢ ((β ⟶ R) ⟶ R)
m >> k = m >>= Lam (wkn k)
