{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
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

import Algebra.Classes
import Data.Functor.Identity
import Data.Ratio
import Data.String.Utils
import Prelude hiding ((>>), Num(..))


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
infixr ⟶
infixr :->

(≐) :: Equality α => γ ⊢ α -> γ ⊢ α -> γ ⊢ R
m ≐ n = App (App (Con (General EqGen)) m) n

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
equals' _ TT TT = True

class Equality α where
  equals :: (γ ⊢ α) -> (γ ⊢ α) -> γ ⊢ R
instance Equality E where
  equals (Con (Special (Entity m))) (Con (Special (Entity n))) =
    Con $ General $ Incl $ case m == n of True -> 1; False -> 0
instance Equality R where
  equals (Con (General (Incl x))) (Con (General (Incl y)))
    = case x == y of
        True -> Con $ General $ Incl 1
        False -> Con $ General $ Incl 0
  equals (Con (Special (Degree m))) (Con (Special (Degree n))) =
          Con $ General $ Incl $ case m == n of True -> 1; False -> 0
  equals x y = App (App (Con (General EqRl)) x) y
instance Equality U where
  equals (Con (General (Utt i))) (Con (General (Utt j))) = case i == j of
                             True -> Con $ General $ Incl 1
                             False -> Con $ General $ Incl 0
  equals (App (Con (General Utt')) x) (App (Con (General Utt')) y)
    = App (App (Con (General EqRl)) x) y
  equals _ _ = Con $ General $ Incl 0
instance Equality Unit where
  equals TT TT = Con $ General $ Incl 1
instance (Equality α, Equality β) => Equality (α × β) where
  equals (Pair m n) (Pair m' n') =
    App (App (Con $ General $ Mult) (equals m m')) (equals n n')
  equals m n = App (App (Con $ General $ EqGen) m) n
instance Equality (E ⟶ R) where
  equals (Con (Special (MeasureFun m))) (Con (Special (MeasureFun n))) =
    Con $ General $ Incl $ case m == n of True -> 1; False -> 0
  equals (Lam m) (Lam n) | equals' 0 (Lam m) (Lam n)
    = case equals m n of
        Con (General (Incl 1)) -> Con $ General $ Incl 1
        Con (General (Incl 0)) -> Con $ General $ Incl 0
        App (App (Con (General EqRl)) (Var (Weaken i))) (Var (Weaken j))
          -> App (App (Con (General EqRl)) (Var i)) (Var j)
instance Equality (E ⟶ T) where
  equals (Con (Special (Property m))) (Con (Special (Property n))) =
    Con $ General $ Incl $ case m == n of True -> 1; False -> 0
instance Equality (R ⟶ R ⟶ T) where
  equals (Con (Special GTE)) (Con (Special GTE)) = Con $ General $ Incl 1 
instance Equality Γ where
  equals (Con (Special Empty)) (Con (Special Empty)) = Con $ General $ Incl 1
instance Equality (E ⟶ Γ ⟶ Γ) where
  equals (Con (Special Upd)) (Con (Special Upd)) = Con $ General $ Incl 1
instance Equality (Γ ⟶ E) where
  equals (Con (Special Sel)) (Con (Special Sel)) = Con $ General $ Incl 1

u :: Int -> γ ⊢ 'U
u i = Con $ General $ Utt i

u' :: γ ⊢ 'R -> γ ⊢ 'U
u' = App $ Con $ General Utt'

vlad = Con $ Special Vlad
height = Con $ Special Height
human = Con $ Special Human
θ = Con $ Special Theta
(≥) = Con $ Special GTE
emp = Con $ Special Empty
upd = Con $ Special Upd
sel = Con $ Special Sel

(/\) :: γ ⊢ T -> γ ⊢ T -> γ ⊢ T
p /\ q = App (App (Con (Logical And)) p) q

(\/) :: γ ⊢ T -> γ ⊢ T -> γ ⊢ T
p \/ q = App (App (Con (Logical Or)) p) q

(-->) :: γ ⊢ T -> γ ⊢ T -> γ ⊢ T
p --> q = App (App (Con (Logical Imp)) p) q

exists :: γ ⊢ (α ⟶ T) -> γ ⊢ T
exists φ = App (Con (Logical Exists)) φ

interp :: γ ⊢ U -> γ ⊢ T
interp (Con (General (Utt 1))) = App (App (≥) (App height vlad)) θ -- 'Vlad is tall'
interp (Con (General (Utt 2))) = App (App (≥) θ) (App height vlad) -- 'Vlad is not tall'
interp (Con (General (Utt 3))) = Con $ Logical Tru -- silence
interp (App (Con (General Utt')) x) = App (App (≥) (App height vlad)) x

subEq :: γ ⊢ α -> γ ⊢ α
subEq = \case
  App (App (Con (General EqGen)) m) n -> equals m n
  App (Con (General (Interp n))) u -> hmorph n (interp u)
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
  App (App (Con (General Mult)) (Con (General (Incl 1)))) (reduce1step -> n) -> n
  App (App (Con (General Mult)) (reduce1step -> m)) (Con (General (Incl 1))) -> m
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
  App (Con (General Mult)) (Con (General (Incl 1))) -> True
  App (App (Con (General Mult)) x) (Con (General (Incl 1))) -> True
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

showR :: Rational -> String
showR (\x -> (numerator x, denominator x) -> (num, den))
  = case (num, den) of
      (0, _) -> "0"
      (_, 1) -> show num
      (_, _) -> "(" ++ show num ++ " / " ++ show den ++ ")"

data Logical α where
  Tru :: Logical T
  Fal :: Logical T
  And :: Logical (T ⟶ T ⟶ T)
  Or :: Logical (T ⟶ T ⟶ T)
  Imp :: Logical (T ⟶ T ⟶ T)
  Forall :: Logical ((α ⟶ T) ⟶ T)
  Exists :: Logical ((α ⟶ T) ⟶ T)
  Equals :: Logical (α ⟶ α ⟶ T)

pattern True' = Con (Logical Tru)
pattern False' = Con (Logical Fal)
pattern And' φ ψ = App (App (Con (Logical And)) φ) ψ
pattern Or' φ ψ = App (App (Con (Logical Or)) φ) ψ
pattern Imp' φ ψ = App (App (Con (Logical Imp)) φ) ψ
pattern Forall' f = App (Con (Logical Forall)) f
pattern Exists' f = App (Con (Logical Exists)) f
pattern Equals' m n = App (App (Con (Logical Equals)) m) n

instance Show (Logical α) where
  show Tru = "⊤"
  show Fal = "⊥"
  show And = "(∧)"
  show Or = "(∨)"
  show Imp = "(→)"
  show Forall = "∀"
  show Exists = "∃"
  show Equals = "(=)"
 
data General α where
  Incl :: Rational -> General R
  Indi :: General ('T ⟶ 'R)
  Addi :: General ('R ⟶ 'R ⟶ 'R)
  Mult :: General ('R ⟶ 'R ⟶ 'R)
  Divi :: General ('R ⟶ 'R ⟶ 'R)
  EqGen :: Equality α => General (α ⟶ α ⟶ 'R)
  EqRl :: General ('R ⟶ 'R ⟶ 'R)
  Utt :: Int -> General 'U
  Utt' :: General ('R ⟶ 'U)
  Cau :: General (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Les :: General (('R ⟶ 'R) ⟶ 'R)
  Nml :: General (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Qua :: General (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Uni :: General (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Interp :: Witness n -> General ('U ⟶ Context n ⟶ 'T)

instance Additive (γ ⊢ 'R) where
  zero = Con (General (Incl 0))
  x + y  = Con (General Addi) `App` x `App` y
instance AbelianAdditive (γ ⊢ 'R)
instance Group (γ ⊢ 'R) where
  negate = App (App (Con (General Mult)) (Con (General (Incl (-1)))))
instance Multiplicative (γ ⊢ 'R) where
  one = Con (General (Incl 1))
  x * y  = Con (General Mult) `App` x `App` y
instance Division (γ ⊢ 'R) where
  x / y  = Con (General Divi) `App` x `App` y

instance Show (General α) where
  show (Incl x) = showR x
  show Indi = "𝟙"
  show Addi = "(+)"
  show Mult = "(*)"
  show Divi = "(/)"
  show Nml = "Normal"
  show Uni = "Uniform"
  show Cau = "Cauchy"
  show Les = "Lesbegue"
  show EqGen = "(≐)"
  show EqRl = "(≡)"
  show (Utt i) = "U" ++ show i
  show Utt' = "U"
  show (Interp n) = "⟦⟧"

data Special α where
  Entity :: Int -> Special E
  MeasureFun :: Int -> Special (E ⟶ R)
  Property :: Int -> Special (E ⟶ T)
  Degree :: Int -> Special R
  GTE :: Special (R ⟶ R ⟶ T)
  Empty :: Special Γ
  Upd :: Special (E ⟶ Γ ⟶ Γ)
  Sel :: Special (Γ ⟶ E)

pattern Vlad = Entity 1
pattern Height = MeasureFun 1
pattern Human = Property 1
pattern Theta = Degree 1
  
instance Show (Special α) where
  show Vlad = "v"
  show (Entity n) = "entity" ++ show n
  show Height = "height"
  show (MeasureFun n) = "measurefun" ++ show n
  show Human = "human"
  show (Property n) = "property" ++ show n
  show Theta = "θ"
  show (Degree n) = "degree" ++ show n
  show GTE = "(≥)"
  show Empty = "ε"
  show Upd = "(∷)"
  show Sel = "sel"

data Con α where
  Logical :: Logical α -> Con α
  General :: General α -> Con α
  Special :: Special α -> Con α

instance Show (Con α) where
  show (Logical c) = show c
  show (General c) = show c
  show (Special c) = show c

-- Well-typed terms.
data γ ⊢ α where
  Var :: α ∈ γ -> γ ⊢ α
  Con :: Con α -> γ ⊢ α
  App :: γ ⊢ (α ⟶ β) -> γ ⊢ α -> γ ⊢ β
  Lam :: (γ × α) ⊢ β -> γ ⊢ (α ⟶ β)
  Fst :: γ ⊢ (α × β) -> γ ⊢ α
  Snd :: γ ⊢ (α × β) -> γ ⊢ β
  TT :: γ ⊢ 'Unit
  Pair :: γ ⊢ α -> γ ⊢ β -> γ ⊢ (α × β)

infixl `App`

absInversion :: γ ⊢ ('R ⟶ α) -> (γ × 'R) ⊢ α
absInversion (Lam f) = f
absInversion t = App (wkn t) (Var Get)

-- Neutral terms (no constructors, except in arguments).
data Neutral γ α where
  NeuVar :: α ∈ γ -> Neutral γ α
  NeuCon :: Con α -> Neutral γ α
  NeuApp :: Neutral γ (α ⟶ β) -> NF γ α -> Neutral γ β
  NeuFst :: Neutral γ (α × β) -> Neutral γ α
  NeuSnd :: Neutral γ (α × β) -> Neutral γ β
  NeuTT :: Neutral γ 'Unit

-- Terms in normal form.
data NF γ α where
  NFLam :: NF (γ × α) β -> NF γ (α ⟶ β)
  NFPair :: NF γ α -> NF γ β -> NF γ (α × β)
  Neu :: Neutral γ α -> NF γ α

absInversionNF :: NF γ ('R ⟶ α) -> NF (γ × 'R) α
absInversionNF (NFLam f) = f
absInversionNF (Neu t) = Neu (NeuApp (renameNeu Weaken t) (Neu (NeuVar Get)))

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
  show = replace "%" "/" . \case
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
    App (App (Con (General Addi)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " + " ++ n ++ ")"
    App (App (Con (General Mult)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " * " ++ n ++ ")"
    App (App (Con (General Divi)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " / " ++ n ++ ")"
    App (App (Con (General EqGen)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " ≐ " ++ n ++ ")"
    App (App (Con (General EqRl)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " ≐ " ++ n ++ ")"
    App (Con (General (Interp n))) (show -> u) -> "⟦" ++ u ++ "⟧"
    App (App (Con (Special GTE)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " ≥ " ++ n ++ ")"
    App (App (Con (Special Upd)) (show -> m)) (show -> n)
      -> m ++ "∷" ++ n
    App (show -> m) (show -> n) -> m ++ "(" ++ n ++ ")"
    Con (show -> c) -> c
    Lam (show -> m) -> "λ(" ++ m ++ ")"
    Fst (show -> m) -> "(π₁ " ++ m ++ ")"
    Snd (show -> m) -> "(π₂ " ++ m ++ ")"
    TT -> "⋄"
    Pair (show -> m) (show -> n) -> "⟨" ++ m ++ ", " ++ n ++ "⟩"

displayDB :: γ ⊢ α -> IO ()
displayDB t = putStrLn $ show t

displayVs :: 'Unit ⊢ α -> IO ()
displayVs t = putStrLn $ replace "%" "/" $ displayVs' freshes (\case) t

freshes :: [String]
freshes = "" : map show ints >>= \i -> map (:i) ['x', 'y', 'z', 'u', 'v', 'w']
  where ints = 1 : map succ ints

displayVs1 :: ('Unit × β)  ⊢ α -> String
displayVs1 t = case freshes of
  [] -> error "displayVs1: panic"
  f:fs -> displayVs' fs (\case Get -> f; Weaken _ -> "γ") t

displayVs' :: forall γ α.
              [String] -> (forall x. x ∈ γ -> String) -> γ ⊢ α -> String
displayVs' fs ρ t =
 let dd :: forall β. γ ⊢ β -> String
     dd = displayVs' fs ρ
 in case t of
  Var v -> ρ v
  App (App (Con (Logical And)) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " ∧ " ++ q ++ ")"
  App (App (Con (Logical Or)) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " ∨ " ++ q ++ ")"
  App (App (Con (Logical Imp)) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " → " ++ q ++ ")"
  App (App (Con (Logical Equals)) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " = " ++ n ++ ")"
  App (App (Con (General Addi)) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " + " ++ n ++ ")"
  App (App (Con (General Mult)) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " * " ++ n ++ ")"
  App (App (Con (General Divi)) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " / " ++ n ++ ")"
  App (App (Con (General EqGen)) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " ≐ " ++ n ++ ")"
  App (App (Con (General EqRl)) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " ≐ " ++ n ++ ")"
  App (Con (General (Interp n))) (dd -> u) -> "⟦" ++ u ++ "⟧"
  App (App (Con (Special GTE)) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " ≥ " ++ n ++ ")"
  App (App (Con (Special Upd)) (dd -> m)) (dd -> n)
    -> m ++ "∷" ++ n
  App (dd -> m) n@(dd -> n') -> m ++ case n of
                                       Lam _ -> n'
                                       Fst _ -> n'
                                       Snd _ -> n'
                                       _ -> "(" ++ n' ++ ")"
  Con (show -> c) -> c
  Lam t' -> case fs of
    fresh:rest -> "(λ" ++ fresh ++ "." ++ displayVs' rest (\case
                                                              Get -> fresh
                                                              Weaken x -> ρ x)
                  t' ++ ")"
    _ -> error "displayVs: ran out of fresh variables."
  Fst (dd -> m) -> "(π₁ " ++ m ++ ")"
  Snd (dd -> m) -> "(π₂ " ++ m ++ ")"
  TT -> "⋄"
  Pair (dd -> m) (dd -> n) -> "⟨" ++ m ++ ", " ++ n ++ "⟩"

lft :: (α ∈ γ -> α ∈ δ) -> α ∈ (γ × β) -> α ∈ (δ × β)
lft f = \case
  Get -> Get
  Weaken i -> Weaken $ f i

π :: α ∈ κ -> γ ⊢ κ -> γ ⊢ α
π Get κ = Snd κ
π (Weaken i) κ = π i (Fst κ)

type Context0 = Unit × (R ⟶ R ⟶ T) × R × (E ⟶ T) × (E ⟶ R) × E
type Context1 = Unit × Γ × (E ⟶ Γ ⟶ Γ) × (Γ ⟶ E) × E × E

data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat

data Witness (n :: Nat) where
  Z :: Witness 'Zero
  S :: Witness n -> Witness ('Succ n)

type family Context (n :: Nat) where
  Context 'Zero = Context0
  Context ('Succ 'Zero) = Context1

findC :: Witness n -> Special α -> α ∈ Context n
findC = \case
  Z -> \case
    Vlad -> Get
    Height -> Weaken Get
    Human -> Weaken (Weaken Get)
    Theta -> Weaken (Weaken (Weaken Get))
    GTE -> Weaken (Weaken (Weaken (Weaken (Get))))
           
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

contr :: (γ × α × α) ⊢ β -> (γ × α) ⊢ β
contr = rename $ \case
  Get -> Get
  Weaken i -> i

hmorph0 :: Witness n -> γ ⊢ α -> (γ × Context n) ⊢ α
hmorph0 n = \case
  Var i -> Var $ Weaken i
  Con (Special c) -> π (findC n c) (Var Get)
  Con c -> Con c
  App (hmorph0 n -> m) (hmorph0 n -> n) -> App m n
  Lam (hmorph0 n -> m) -> Lam $ exch m
  Fst (hmorph0 n -> m) -> Fst m
  Snd (hmorph0 n -> m) -> Snd m
  Pair (hmorph0 n -> m) (hmorph0 n -> n) -> Pair m n

hmorph :: Witness n -> γ ⊢ α -> γ ⊢ (Context n ⟶ α)
hmorph n (hmorph0 n -> m) = Lam m

η :: γ ⊢ α -> γ ⊢ ((α ⟶ 'R) ⟶ 'R)
η m = Lam (App (Var Get) (wkn m))

(⋆) :: γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ (α ⟶ ((β ⟶ 'R) ⟶ 'R)) -> γ ⊢ ((β ⟶ 'R) ⟶ 'R)
m ⋆ k = Lam (App (wkn m) (Lam (App (App (wkn (wkn k)) (Var Get)) (Var (Weaken Get)))))

(>>) :: γ ⊢ (('Unit ⟶ 'R) ⟶ 'R) -> γ ⊢ ((β ⟶ 'R) ⟶ 'R) -> γ ⊢ ((β ⟶ 'R) ⟶ 'R)
m >> k = m ⋆ Lam (wkn k)
