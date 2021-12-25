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
{-# LANGUAGE ViewPatterns #-}

module TLC.Terms where

import Data.Functor.Identity
import Prelude hiding (Monad(..))

data Type = E | T | R | U | Γ
          | Type :-> Type
          | Unit
          | Type :× Type

data (α :: Type) ∈ (γ :: Type) where
  Get :: α ∈ (γ × α)
  Weaken :: α ∈ γ -> α ∈ (γ × β)
deriving instance Show (α ∈ γ)

type α × β = α ':× β
type α ⟶ β = α ':-> β

(≐) :: Equality α => γ ⊢ α -> γ ⊢ α -> γ ⊢ R
m ≐ n = App (App (Con (Rl EqGen)) m) n

class Equality α where
  equals :: (γ ⊢ α) -> (γ ⊢ α) -> γ ⊢ R
instance Equality E where
  equals (Con (Special Vlad)) (Con (Special Vlad)) = Con $ Rl $ Incl 1
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
  equals (Lam m) (Lam n) | isConstant 0 m && isConstant 0 n
    = case equals m n of
        Con (Rl (Incl 1)) -> Con $ Rl $ Incl 1
        Con (Rl (Incl 0)) -> Con $ Rl $ Incl 0
        App (App (Con (Rl EqRl)) (Var (Weaken i))) (Var (Weaken j))
          -> App (App (Con (Rl EqRl)) (Var i)) (Var j)
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

canReduce :: γ ⊢ α -> Bool
canReduce (App (Con (Rl Mult)) (Con (Rl (Incl 1)))) = True
canReduce (App (App (Con (Rl Mult)) x) (Con (Rl (Incl 1)))) = True
canReduce (Var i) = False
canReduce (Con c) = False
canReduce (App m n) = canReduce m || canReduce n
canReduce (Lam m) = canReduce m
canReduce (Fst m) = canReduce m
canReduce (Snd m) = canReduce m
canReduce TT = False
canReduce (Pair m n) = canReduce m || canReduce n

reduce1s :: γ ⊢ α -> γ ⊢ α
reduce1s m = if canReduce m then reduce1s (reduce1step m) else m

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
  Lam :: (γ × α) ⊢ β -> γ ⊢ (α ⟶ β)
  Fst :: γ ⊢ (α × β) -> γ ⊢ α
  Snd :: γ ⊢ (α × β) -> γ ⊢ β
  TT :: γ ⊢ Unit
  Pair :: γ ⊢ α -> γ ⊢ β -> γ ⊢ (α × β)

data Neutral γ α where
  NeuVar :: α ∈ γ -> Neutral γ α
  NeuCon :: Con α -> Neutral γ α
  NeuApp :: Neutral γ (α ⟶ β) -> NF γ α -> Neutral γ β
  NeuFst :: Neutral γ (α × β) -> Neutral γ α
  NeuSnd :: Neutral γ (α × β) -> Neutral γ β
  NeuTT :: Neutral γ Unit

data NF γ α where
  NFLam :: NF (γ × α) β -> NF γ (α ⟶ β)
  NFPair :: NF γ α -> NF γ β -> NF γ (α × β)
  Neu :: Neutral γ α -> NF γ α

wknNF :: NF γ α -> NF (γ × β) α
wknNF = renameNF Weaken

exchNF :: NF ((γ × α) × β) ω -> NF ((γ × β) × α) ω
exchNF = renameNF $ \case
  Get -> Weaken Get
  Weaken Get -> Get
  Weaken (Weaken i) -> Weaken $ Weaken i

substNeu :: Neutral γ α -> (forall β.β ∈ γ -> NF δ β) -> NF δ α
substNeu (NeuVar i) f = f i
substNeu (NeuCon c) _ = Neu $ NeuCon c
substNeu (NeuApp m n) f = case substNeu m f of
                            NFLam m' -> substNF0 m' (substNF n f)
                            Neu m' -> Neu $ NeuApp m' (substNF n f)
substNeu (NeuFst m) f = case substNeu m f of
                          NFPair m' n' -> m'
                          Neu m' -> Neu $ NeuFst m'
substNeu (NeuSnd m) f = case substNeu m f of
                          NFPair m' n' -> n'
                          Neu m' -> Neu $ NeuSnd m'
substNeu NeuTT f = Neu NeuTT
                            
substNF :: NF γ α -> (forall β.β ∈ γ -> NF δ β) -> NF δ α
substNF (NFLam m) f = NFLam $ substNF m $ \case
  Get -> Neu $ NeuVar Get
  Weaken i -> wknNF $ f i
substNF (NFPair m n) f = NFPair (substNF m f) (substNF n f)
substNF (Neu m) f = substNeu m f

substNF0 :: NF (γ × α) β -> NF γ α -> NF γ β
substNF0 m t = substNF m $ \case
  Get -> t
  (Weaken i) -> Neu $ NeuVar i

normalForm :: γ ⊢ α -> NF γ α
normalForm (Var i) = Neu $ NeuVar i
normalForm (Con c) = Neu $ NeuCon c
normalForm (App (normalForm -> m) (normalForm -> n))
  = case m of
      NFLam m' -> substNF0 m' n
      Neu m' -> Neu $ NeuApp m' n
normalForm (Lam (normalForm -> m)) = NFLam m
normalForm (Fst (normalForm -> m))
  = case m of
      NFPair m' n' -> m'
      Neu m' -> Neu $ NeuFst m'
normalForm (Snd (normalForm -> m))
  = case m of
      NFPair m' n' -> n'
      Neu m' -> Neu $ NeuSnd m'
normalForm (Pair (normalForm -> m) (normalForm -> n)) = NFPair m n
normalForm TT = Neu NeuTT

nf_to_λ :: NF γ α -> γ ⊢ α
nf_to_λ (Neu (neu_to_λ -> m)) = m
nf_to_λ (NFLam (nf_to_λ -> m)) = Lam m
nf_to_λ (NFPair (nf_to_λ -> m) (nf_to_λ -> n)) = Pair m n

neu_to_λ :: Neutral γ α -> γ ⊢ α
neu_to_λ (NeuVar i) = Var i
neu_to_λ (NeuCon c) = Con c
neu_to_λ (NeuApp (neu_to_λ -> m) (nf_to_λ -> n)) = App m n
neu_to_λ (NeuFst (neu_to_λ -> m)) = Fst m
neu_to_λ (NeuSnd (neu_to_λ -> m)) = Snd m
neu_to_λ NeuTT = TT

evalβ :: γ ⊢ α -> γ ⊢ α
evalβ = nf_to_λ . normalForm

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

lft :: (α ∈ γ -> α ∈ δ) -> α ∈ (γ × β) -> α ∈ (δ × β)
lft f Get = Get
lft f (Weaken i) = Weaken $ f i

π :: α ∈ κ -> γ ⊢ κ -> γ ⊢ α
π Get γ = Snd γ
π (Weaken i) γ = π i (Fst γ)

type Context
  = (((((((Unit
            × (Γ ⟶ E))
           × (E ⟶ (Γ ⟶ Γ)))
          × Γ)
         × (R ⟶ (R ⟶ T))
        × R)
       × (E ⟶ T))
      × (E ⟶ R))
     × E)

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

renameNeu :: (forall α. α ∈ γ -> α ∈ δ) -> Neutral γ β -> Neutral δ β
renameNeu f = \case
  NeuVar i -> NeuVar $ f i
  NeuCon c -> NeuCon c
  NeuApp (renameNeu f -> m) (renameNF f -> n) -> NeuApp m n
  NeuFst (renameNeu f -> m) -> NeuFst m
  NeuSnd (renameNeu f -> m) -> NeuSnd m
  NeuTT -> NeuTT

renameNF :: (forall α. α ∈ γ -> α ∈ δ) -> NF γ β -> NF δ β
renameNF f = \case
  (Neu (renameNeu f -> m)) -> Neu m
  (NFLam (renameNF (lft f) -> m)) -> NFLam m
  (NFPair (renameNF f -> m) (renameNF f -> n)) -> NFPair m n

wkn :: γ ⊢ α -> (γ × β) ⊢ α
wkn = rename Weaken

exch :: ((γ × α) × β) ⊢ ω -> ((γ × β) × α) ⊢ ω
exch = rename $ \case
  Get -> Weaken Get
  Weaken Get -> Get
  (Weaken (Weaken i)) -> Weaken (Weaken i)

contr :: ((γ × α) × α) ⊢ β -> (γ × α) ⊢ β
contr = rename $ \case
  Get -> Get
  Weaken i -> i

hmorph0 :: γ ⊢ α -> (γ × Context) ⊢ α
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
m >>= k = Lam (App (wkn m)
               (Lam (App (App (wkn (wkn k)) (Var Get)) (Var (Weaken Get)))))

(>>) :: γ ⊢ ((Unit ⟶ R) ⟶ R) -> γ ⊢ ((β ⟶ R) ⟶ R) -> γ ⊢ ((β ⟶ R) ⟶ R)
m >> k = m >>= Lam (wkn k)
