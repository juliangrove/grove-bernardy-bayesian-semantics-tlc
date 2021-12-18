{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module TLC.Terms where

import Data.Functor.Identity
import Prelude hiding (Monad(..))

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

(≐) :: Equality α => γ ⊢ α -> γ ⊢ α -> γ ⊢ R
m ≐ n = App (App (Con (Rl EqGen)) m) n

class Equality α where
  equals :: (γ ⊢ α) -> (γ ⊢ α) -> γ ⊢ R
instance Equality E where
  equals (Con (Special Vlad)) (Con (Special Vlad)) = Con $ Rl $ Incl 1
-- instance Equality T
instance Equality R where
  equals (Con (Rl (Incl x))) (Con (Rl (Incl y))) = case x == y of
                                                     True -> Con $ Rl $ Incl 1
                                                     False -> Con $ Rl $ Incl 0
  equals (Con (Special Theta)) (Con (Special Theta)) = Con $ Rl $ Incl 1
  equals x y = App (App (Con (Rl EqRl)) x) y 
instance Equality U where
  equals (Con (Special (Utt i))) (Con (Special (Utt j))) = case i == j of
                             True -> Con $ Rl $ Incl 1
                             False -> Con $ Rl $ Incl 0
instance Equality Unit where
  equals TT TT = Con $ Rl $ Incl 1
instance (Equality α, Equality β) => Equality (α × β) where
  equals (Pair m n) (Pair m' n')
    = App (App (Con $ Rl $ Mult) (equals m m')) (equals n n')
  equals m n = App (App (Con $ Rl $ EqGen) m) n
instance Equality (E ⟶ R) where
  equals (Con (Special Height)) (Con (Special Height)) = Con $ Rl $ Incl 1
  equals (Lam m) (Lam n) | isConstant 0 m && isConstant 0 n = case equals m n of
                             Con (Rl (Incl 1)) -> Con $ Rl $ Incl 1
                             Con (Rl (Incl 0)) -> Con $ Rl $ Incl 0
                             App (App (Con (Rl EqRl))
                                  (Var (Weaken i)))
                               (Var (Weaken j)) -> App (App (Con (Rl EqRl)) (Var i)) (Var j)
instance Equality (E ⟶ T) where
  equals (Con (Special Human)) (Con (Special Human)) = Con $ Rl $ Incl 1
instance Equality (R ⟶ (R ⟶ T)) where
  equals (Con (Special GTE)) (Con (Special GTE)) = Con $ Rl $ Incl 1 
instance Equality Γ where
  equals (Con (Special Empty)) (Con (Special Empty)) = Con $ Rl $ Incl 1
instance Equality (E ⟶ (Γ ⟶ Γ)) where
  equals (Con (Special Upd)) (Con (Special Upd)) = Con $ Rl $ Incl 1
instance Equality (Γ ⟶ E) where
  equals (Con (Special Sel)) (Con (Special Sel)) = Con $ Rl $ Incl 1

subEq :: γ ⊢ α -> γ ⊢ α
subEq (App (App (Con (Rl EqGen)) m) n) = equals m n
subEq (Var i) = Var i
subEq (Con c) = Con c
subEq (App m n) = App (subEq m) (subEq n)
subEq (Lam m) = Lam $ subEq m
subEq (Fst m) = Fst $ subEq m
subEq (Snd m) = Snd $ subEq m
subEq TT = TT
subEq (Pair m n) = Pair (subEq m) (subEq n)

reduce1step :: γ ⊢ α -> γ ⊢ α
reduce1step (App (App (Con (Rl Mult)) (Con (Rl (Incl 1)))) n) = reduce1step n
reduce1step (App (App (Con (Rl Mult)) m) (Con (Rl (Incl 1)))) = reduce1step m
reduce1step (Var i) = Var i
reduce1step (Con c) = Con c
reduce1step (App m n) = App (reduce1step m) (reduce1step n)
reduce1step (Lam m) = Lam $ reduce1step m
reduce1step (Fst m) = Fst $ reduce1step m
reduce1step (Snd m) = Snd $ reduce1step m
reduce1step TT = TT
reduce1step (Pair m n) = Pair (reduce1step m) (reduce1step n)

has1s :: γ ⊢ α -> Bool
has1s (Con (Rl (Incl 1))) = True
has1s (Var i) = False
has1s (Con c) = False
has1s (App m n) = has1s m || has1s n
has1s (Lam m) = has1s m
has1s (Fst m) = has1s m
has1s (Snd m) = has1s m
has1s TT = False
has1s (Pair m n) = has1s m || has1s n

reduce1s :: γ ⊢ α -> γ ⊢ α
reduce1s m = if has1s m then reduce1s (reduce1step m) else m

clean :: γ ⊢ α -> γ ⊢ α
clean = reduce1s . subEq

isConstant :: Int -> γ ⊢ α -> Bool
isConstant i (Var Get) = i < 0
isConstant i (Var (Weaken j)) = isConstant (i - 1) (Var j)
isConstant i (Con c) = True
isConstant i (App m n) = isConstant i m && isConstant i n
isConstant i (Lam m) = isConstant (i + 1) m
isConstant i (Fst m) = isConstant i m
isConstant i (Snd m) = isConstant i m
isConstant i TT = True
isConstant i (Pair m n) = isConstant i m && isConstant i n

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
  Divi :: Rl (R ⟶ (R ⟶ R))
  Nml :: Rl ((R × R) ⟶ ((R ⟶ R) ⟶ R))
  Uni :: Rl ((R × R) ⟶ ((R ⟶ R) ⟶ R))
  EqGen :: Equality α => Rl (α ⟶ (α ⟶ R))
  EqRl :: Rl (R ⟶ (R ⟶ R))

instance Show (Rl α) where
  show (Incl x) = show x
  show Indi = "𝟙"
  show Mult = "(*)"
  show Divi = "(/)"
  show Nml = "Normal"
  show Uni = "Uniform"
  show EqGen = "(≐)"
  show EqRl = "(≐)"

data Special α where
  Utt :: Int -> Special U
  Vlad :: Special E
  Height :: Special (E ⟶ R)
  Human :: Special (E ⟶ T)
  Theta :: Special R
  GTE :: Special (R ⟶ (R ⟶ T))
  Empty :: Special Γ
  Upd :: Special (E ⟶ (Γ ⟶ Γ))
  Sel :: Special (Γ ⟶ E)

instance Show (Special α) where
  show (Utt i) = "U" ++ show i
  show Vlad = "v"
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
  show (App (App (Con (Rl Mult)) m) n)
    = "(" ++ show m ++ " * " ++ show n ++ ")"
  show (App (App (Con (Rl Divi)) m) n)
    = "(" ++ show m ++ " / " ++ show n ++ ")"
  show (App (App (Con (Rl EqGen)) m) n)
    = "(" ++ show m ++ " ≐ " ++ show n ++ ")"
  show (App (App (Con (Rl EqRl)) m) n)
    = "(" ++ show m ++ " ≐ " ++ show n ++ ")"
  show (App (App (Con (Special GTE)) m) n)
    = "(" ++ show m ++ " ≥ " ++ show n ++ ")"
  show (App (App (Con (Special Upd)) m) n)
    = show m ++ "∷" ++ show n
  show (App m n) = show m ++ "(" ++ show n ++ ")"
  show (Con c) = show c
  show (Lam m) = "λ(" ++ show m ++ ")"
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
evalstepβ (Con c) = Con c
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
  = (E ×
     (E ⟶ R ×
      (E ⟶ T ×
       (R ×
        ((R ⟶ (R ⟶ T)) ×
         (Γ ×
          ((E ⟶ (Γ ⟶ Γ)) ×
           ((Γ ⟶ E) × Unit))))))))

findC :: Special α -> α ∈ Context
findC Vlad = Get
findC Height = Weaken Get
findC Human = Weaken (Weaken Get)
findC Theta = Weaken (Weaken (Weaken Get))
findC GTE = Weaken (Weaken (Weaken (Weaken (Get))))
findC Empty = Weaken (Weaken (Weaken (Weaken (Weaken Get))))
findC Upd = Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get)))))
findC Sel = Weaken (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get))))))
                   
rename :: (∀α. α ∈ γ -> α ∈ δ) -> γ ⊢ β -> δ ⊢ β
rename f (Var i) = Var $ f i
rename f (Con c) = (Con c)
rename f (App m n) = App (rename f m) (rename f n)
rename f (Lam m) = Lam $ rename (lft f) m
rename f (Fst m) = Fst $ rename f m
rename f (Snd m) = Snd $ rename f m
rename f TT = TT
rename f (Pair m n) = Pair (rename f m) (rename f n)

wkn :: γ ⊢ α -> (β × γ) ⊢ α
wkn = rename Weaken

exch :: (α × (β × γ)) ⊢ ω -> (β × (α × γ)) ⊢ ω
exch = rename $ \case
  Get -> Weaken Get
  Weaken Get -> Get
  (Weaken (Weaken i)) -> Weaken (Weaken i)

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
