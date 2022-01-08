{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ViewPatterns #-}

module TLC.Terms where

import Data.Functor.Identity
import Prelude hiding ((>>))

data Type = E | T | R | U | Γ
          | Type :-> Type
          | Unit
          | Type :× Type

data (α :: Type) ∈ (γ :: Type) where
  Get :: α ∈ (γ × α)
  Weaken :: α ∈ γ -> α ∈ (γ × β)
deriving instance Show (α ∈ γ)
deriving instance Eq (α ∈ γ)

type α × β = α ':× β
type α ⟶ β = α ':-> β

(≐) :: Equality α => γ ⊢ α -> γ ⊢ α -> γ ⊢ R
m ≐ n = App (App (Con (Rl EqGen)) m) n

equals' :: Int -> (γ1 ⊢ α) -> (γ2 ⊢ β) -> Bool
equals' _ (Var Get) (Var Get) = True
equals' n (Var Get) _ = n <= 0
equals' n _ (Var Get) = n <= 0
equals' n (Var (Weaken i)) (Var (Weaken j)) = equals' (n - 1) (Var i) (Var j)
equals' n (Var (Weaken i)) m2 = equals' (n - 1) (Var i) m2
equals' n m1 (Var (Weaken j)) = equals' (n - 1) m1 (Var j)
equals' _ (Con c1) (Con c2) = case c1 of c2 -> True
equals' n (App m1 n1) (App m2 n2) = equals' n m1 m2 && equals' n n1 n2
equals' n (Lam m1) (Lam m2) = equals' (n + 1) m1 m2
equals' n (Fst m1) (Fst m2) = equals' n m1 m2
equals' n (Snd m1) (Snd m2) = equals' n m1 m2
equals' n (Pair m1 n1) (Pair m2 n2) = equals' n m1 m2 && equals' n n1 n2
equals' n TT TT = True

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
  equals (Lam m) (Lam n) | equals' 0 m n
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
subEq = \case
  App (App (Con (Rl EqGen)) m) n -> equals m n
  Var i -> Var i
  Con c -> Con c
  App (subEq -> m) (subEq -> n) -> App m n
  Lam (subEq -> m) -> Lam m
  Fst (subEq -> m) -> Fst m
  Snd (subEq -> m) -> Snd m
  TT -> TT
  Pair (subEq -> m) (subEq -> n) -> Pair m n

reduce1step :: γ ⊢ α -> γ ⊢ α
reduce1step = \case
  App (App (Con (Rl Mult)) (Con (Rl (Incl 1)))) (reduce1step -> n) -> n
  App (App (Con (Rl Mult)) (reduce1step -> m)) (Con (Rl (Incl 1))) -> m
  Var i -> Var i
  Con c -> Con c
  App (reduce1step -> m) (reduce1step -> n) -> App m n
  Lam (reduce1step -> m) -> Lam m
  Fst (reduce1step -> m) -> Fst m
  Snd (reduce1step -> m) -> Snd m
  TT -> TT
  Pair (reduce1step -> m) (reduce1step -> n) -> Pair m n

canReduce :: γ ⊢ α -> Bool
canReduce = \case
  App (Con (Rl Mult)) (Con (Rl (Incl 1))) -> True
  App (App (Con (Rl Mult)) x) (Con (Rl (Incl 1))) -> True
  Var i -> False
  Con c -> False
  App (canReduce -> m) (canReduce -> n) -> m || n
  Lam m -> canReduce m
  Fst m -> canReduce m
  Snd m -> canReduce m
  TT -> False
  Pair (canReduce -> m) (canReduce -> n) -> m || n

reduce1s :: γ ⊢ α -> γ ⊢ α
reduce1s m = if canReduce m then reduce1s (reduce1step m) else m

clean :: γ ⊢ α -> γ ⊢ α
clean = reduce1s . subEq

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

-- Neutral terms (no constructors, except in arguments).
data Neutral γ α where
  NeuVar :: α ∈ γ -> Neutral γ α
  NeuCon :: Con α -> Neutral γ α
  NeuApp :: Neutral γ (α ⟶ β) -> NF γ α -> Neutral γ β
  NeuFst :: Neutral γ (α × β) -> Neutral γ α
  NeuSnd :: Neutral γ (α × β) -> Neutral γ β
  NeuTT :: Neutral γ Unit

-- Terms in normal form.
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
normalForm = \case
  Var i -> Neu $ NeuVar i
  Con c -> Neu $ NeuCon c
  App (normalForm -> m) (normalForm -> n) -> case m of
                                               NFLam m' -> substNF0 m' n
                                               Neu m' -> Neu $ NeuApp m' n
  Lam (normalForm -> m) -> NFLam m
  Fst (normalForm -> m) -> case m of
                             NFPair m' n' -> m'
                             Neu m' -> Neu $ NeuFst m'
  Snd (normalForm -> m) -> case m of
                             NFPair m' n' -> n'
                             Neu m' -> Neu $ NeuSnd m'
  Pair (normalForm -> m) (normalForm -> n) -> NFPair m n
  TT -> Neu NeuTT

nf_to_λ :: NF γ α -> γ ⊢ α
nf_to_λ = \case
  Neu (neu_to_λ -> m) -> m
  NFLam (nf_to_λ -> m) -> Lam m
  NFPair (nf_to_λ -> m) (nf_to_λ -> n) -> Pair m n

neu_to_λ :: Neutral γ α -> γ ⊢ α
neu_to_λ = \case
  NeuVar i -> Var i
  NeuCon c -> Con c
  NeuApp (neu_to_λ -> m) (nf_to_λ -> n) -> App m n
  NeuFst (neu_to_λ -> m) -> Fst m
  NeuSnd (neu_to_λ -> m) -> Snd m
  NeuTT -> TT

evalβ :: γ ⊢ α -> γ ⊢ α
evalβ = nf_to_λ . normalForm

instance Show (γ ⊢ α) where
  show = \case
    Var Get -> "x"
    Var (Weaken i) -> show (Var i) ++ "'"
    App (App (Con (Logical And)) (show -> p)) (show -> q)
      -> "(" ++ p ++ " ∧ " ++ q ++ ")"
    App (App (Con (Logical Or)) (show -> p)) (show -> q)
      -> "(" ++ p ++ " ∨ " ++ q ++ ")"
    App (App (Con (Logical Imp)) (show -> p)) (show -> q)
      -> "(" ++ p ++ " → " ++ q ++ ")"
    App (App (Con (Logical Equals)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " = " ++ n ++ ")"
    App (App (Con (Rl Mult)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " * " ++ n ++ ")"
    App (App (Con (Rl Divi)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " / " ++ n ++ ")"
    App (App (Con (Rl EqGen)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " ≐ " ++ n ++ ")"
    App (App (Con (Rl EqRl)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " ≐ " ++ n ++ ")"
    App (App (Con (Special GTE)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " ≥ " ++ n ++ ")"
    App (App (Con (Special Upd)) (show -> m)) (show -> n)
      -> m ++ "∷" ++ n
    App (show -> m) (show -> n) -> m ++ "(" ++ n ++ ")"
    Con (show -> c) -> c
    Lam (show -> m) -> "λ(" ++ m ++ ")"
    Fst (show -> m) -> "(π₁ " ++ m ++ ")"
    Snd (show -> m) -> "(π₂" ++ m ++ ")"
    TT -> "⋄"
    Pair (show -> m) (show -> n) -> "⟨" ++ m ++ ", " ++ n ++ "⟩"

displayDB :: γ ⊢ α -> IO ()
displayDB t = putStrLn $ show t

displayVs :: γ ⊢ α -> IO ()
displayVs t = putStrLn $ displayVs' 0 t

freshes :: [String]
freshes = "" : map show ints >>= \i -> map (:i) ['x', 'y', 'z', 'u', 'v', 'w']
  where ints = 1 : map succ ints

displayVs' :: Int -> γ ⊢ α -> String
displayVs' i = \case
  Var Get -> freshes !! (i - 1)
  Var (Weaken j) -> displayVs' (i - 1) $ Var j
  App (App (Con (Logical And)) (displayVs' i -> p)) (displayVs' i -> q)
    -> "(" ++ p ++ " ∧ " ++ q ++ ")"
  App (App (Con (Logical Or)) (displayVs' i -> p)) (displayVs' i -> q)
    -> "(" ++ p ++ " ∨ " ++ q ++ ")"
  App (App (Con (Logical Imp)) (displayVs' i -> p)) (displayVs' i -> q)
    -> "(" ++ p ++ " → " ++ q ++ ")"
  App (App (Con (Logical Equals)) (displayVs' i -> m)) (displayVs' i -> n)
    -> "(" ++ m ++ " = " ++ n ++ ")"
  App (App (Con (Rl Mult)) (displayVs' i -> m)) (displayVs' i -> n)
    -> "(" ++ m ++ " * " ++ n ++ ")"
  App (App (Con (Rl Divi)) (displayVs' i -> m)) (displayVs' i -> n)
    -> "(" ++ m ++ " / " ++ n ++ ")"
  App (App (Con (Rl EqGen)) (displayVs' i -> m)) (displayVs' i -> n)
    -> "(" ++ m ++ " ≐ " ++ n ++ ")"
  App (App (Con (Rl EqRl)) (displayVs' i -> m)) (displayVs' i -> n)
    -> "(" ++ m ++ " ≐ " ++ n ++ ")"
  App (App (Con (Special GTE)) (displayVs' i -> m)) (displayVs' i -> n)
    -> "(" ++ m ++ " ≥ " ++ n ++ ")"
  App (App (Con (Special Upd)) (displayVs' i -> m)) (displayVs' i -> n)
    -> m ++ "∷" ++ n
  App (displayVs' i -> m) n@(displayVs' i -> n') -> m ++ case n of
                                                           Lam _ -> n'
                                                           Fst _ -> n'
                                                           Snd _ -> n'
                                                           _ -> "(" ++ n' ++ ")"
  Con (show -> c) -> c
  Lam (displayVs' (i + 1) -> m) -> "(λ" ++ freshes !! i ++ "." ++ m ++ ")"
  Fst (displayVs' i -> m) -> "(π₁ " ++ m ++ ")"
  Snd (displayVs' i -> m) -> "(π₂" ++ m ++ ")"
  TT -> "⋄"
  Pair (displayVs' i -> m) (displayVs' i -> n) -> "⟨" ++ m ++ ", " ++ n ++ "⟩"

lft :: (α ∈ γ -> α ∈ δ) -> α ∈ (γ × β) -> α ∈ (δ × β)
lft f = \case
  Get -> Get
  Weaken i -> Weaken $ f i

π :: α ∈ κ -> γ ⊢ κ -> γ ⊢ α
π Get κ = Snd κ
π (Weaken i) κ = π i (Fst κ)

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
findC = \case
  Vlad -> Get
  Height -> Weaken Get
  Human -> Weaken (Weaken Get)
  Theta -> Weaken (Weaken (Weaken Get))
  GTE -> Weaken (Weaken (Weaken (Weaken (Get))))
  Empty -> Weaken (Weaken (Weaken (Weaken (Weaken Get))))
  Upd -> Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get)))))
  Sel -> Weaken (Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get))))))
                   
rename :: (∀α. α ∈ γ -> α ∈ δ) -> γ ⊢ β -> δ ⊢ β
rename f = \case
  Var i -> Var $ f i
  Con c -> Con c
  App (rename f -> m) (rename f -> n) -> App m n
  Lam (rename (lft f) -> m) -> Lam m
  Fst (rename f -> m) -> Fst m
  Snd (rename f -> m) -> Snd m
  TT -> TT
  Pair (rename f -> m) (rename f -> n) -> Pair m n

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
hmorph0 = \case
  Var i -> Var $ Weaken i
  Con (Special c) -> π (findC c) (Var Get)
  Con c -> Con c
  App (hmorph0 -> m) (hmorph0 -> n) -> App m n
  Lam (hmorph0 -> m) -> Lam $ exch m
  Fst (hmorph0 -> m) -> Fst m
  Snd (hmorph0 -> m) -> Snd m
  Pair (hmorph0 -> m) (hmorph0 -> n) -> Pair m n

hmorph :: γ ⊢ α -> γ ⊢ (Context ⟶ α)
hmorph (hmorph0 -> m) = Lam m

η :: γ ⊢ α -> γ ⊢ ((α ⟶ R) ⟶ R)
η m = Lam (App (Var Get) (wkn m))

(⋆) :: γ ⊢ ((α ⟶ R) ⟶ R) -> γ ⊢ (α ⟶ ((β ⟶ R) ⟶ R)) -> γ ⊢ ((β ⟶ R) ⟶ R)
m ⋆ k = Lam (App (wkn m)
               (Lam (App (App (wkn (wkn k)) (Var Get)) (Var (Weaken Get)))))

(>>) :: γ ⊢ ((Unit ⟶ R) ⟶ R) -> γ ⊢ ((β ⟶ R) ⟶ R) -> γ ⊢ ((β ⟶ R) ⟶ R)
m >> k = m ⋆ Lam (wkn k)
