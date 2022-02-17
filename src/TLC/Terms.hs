{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
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
import Data.Ratio
import Data.String.Utils
import qualified FOL.FOL as FOL
import Prelude hiding ((>>), Num(..), Sum(..), sum)


data Type = E | T | R | U | Γ
          | Type :-> Type
          | Unit
          | Type :× Type

data (α :: Type) ∈ (γ :: Type) where
  Get :: α ∈ (γ × α)
  Weaken :: α ∈ γ -> α ∈ (γ × β)
deriving instance Show (α ∈ γ)
deriving instance Eq (α ∈ γ)
deriving instance Ord (α ∈ γ) -- do not chane this instance, it is used for testin deepness of variables

type α × β = α ':× β
type α ⟶ β = α ':-> β
infixr ⟶
infixr :->

(≐) :: Equality α => γ ⊢ α -> γ ⊢ α -> γ ⊢ 'R
m ≐ n = App (Con (EqGen)) (Pair m n)

noOccur :: (α ∈ (γ × x)) -> Maybe (α ∈ γ)
noOccur = \case
  Get -> Nothing
  Weaken x -> Just x

pattern NCon x = Neu (NeuCon x)
pattern NVar x = Neu (NeuVar x)
class Equality α where
  equals :: forall γ. NF γ α -> NF γ α -> NF γ 'R
instance Equality 'E where
  equals (NCon (Entity m)) (NCon (Entity n)) =
    NCon $ Incl $ case m == n of True -> 1; False -> 0
  equals x y = Neu $ NeuApp (NeuCon EqGen) (NFPair x y) 
instance Equality 'R where
  equals (NCon (Incl x)) (NCon (Incl y))
    = case x == y of
        True -> one
        False -> NCon $ Incl 0
  equals (NCon (Degree m)) (NCon (Degree n)) =
          NCon $ Incl $ case m == n of True -> 1; False -> 0
  equals x y = Neu $ NeuCon EqRl `NeuApp` x `NeuApp` y
instance Equality 'U where
  equals (NCon (Utt i)) (NCon (Utt j)) = case i == j of
                             True -> one
                             False -> NCon (Incl 0)
  equals (Neu (NeuApp (NeuCon Utt') x))
    (Neu (NeuApp (NeuCon Utt') y)) = equals x y
  equals (NCon (Utt'' es0)) (NCon (Utt'' es1)) =
    checkEquality es0 es1
    where checkEquality :: [Maybe (Con 'E)] -> [Maybe (Con 'E)]
                        -> NF γ 'R
          checkEquality [] [] = one
          checkEquality (Nothing:es0) (Nothing:es1) = checkEquality es0 es1
          checkEquality (Just _ : _) (Nothing:_) = NCon (Incl 0)
          checkEquality (Nothing:_) (Just _ : _) = NCon (Incl 0)
          checkEquality (Just x : es0) (Just y : es1) =
            equals (NCon x) (NCon y) * checkEquality es0 es1
  equals m n = Neu $ (NeuCon EqGen) `NeuApp` (NFPair m n)
instance Equality 'Unit where
  equals _ _ = one
instance (Equality α, Equality β) => Equality (α × β) where
  equals (NFPair m n) (NFPair m' n') = equals m m' * equals n n'
  equals m n = Neu $ (NeuCon EqGen) `NeuApp` (NFPair m n)
instance Equality ('E ⟶ 'R) where
  equals :: forall γ. NF γ ('E ⟶ 'R) -> NF γ ('E ⟶ 'R) -> NF γ 'R
  equals (NCon (MeasureFun m)) (NCon (MeasureFun n)) =
    NCon $ Incl $ case m == n of True -> 1; False -> 0
  equals (NFLam m) (NFLam n)
    | Just x <- traverseNF noOccur (equals m n) = x
  equals t u = Neu ((NeuCon EqGen) `NeuApp` (NFPair t u))
instance Equality ('E ⟶ 'T) where
  equals (NCon (Property m)) (NCon (Property n)) =
    NCon $ Incl $ case m == n of True -> 1; False -> 0
instance Equality ('E ⟶ 'E ⟶ 'T) where
  equals (NCon (Relation m)) (NCon (Relation n)) =
    NCon $ Incl $ case m == n of True -> 1; False -> 0
instance Equality ('R ⟶ 'R ⟶ 'T) where
  equals (NCon GTE) (NCon GTE) = one
instance Equality 'Γ where
  equals (NCon Empty) (NCon Empty) = one
instance Equality ('E ⟶ 'Γ ⟶ 'Γ) where
  equals (NCon Upd) (NCon Upd) = one
instance Equality 'T where
  equals ϕ ψ = if termToFol ϕ == termToFol ψ then one else zero 
instance Equality ('Γ ⟶ 'E) where
  equals (NCon (Sel i)) (NCon (Sel j)) =
    case i == j of
      True -> one
      False -> NCon (Incl 0)
  equals (NCon (Pi i)) (NCon (Pi j)) =
    case i == j of
      True -> one
      False -> NCon (Incl 0)

--------------------------------------
type ValueSubst = forall δ β. β ∈ δ -> FOL.Value

viewApp :: ValueSubst -> γ ⊢ α -> Maybe (String, [FOL.Value])
viewApp ρ = \case
  TLC.Terms.Con c -> Just (show c, [])
  App x y -> case viewApp ρ x of
               Just (f, args) -> Just (f, args ++ [termToFol' ρ y])
               _ -> Nothing
  _ -> Nothing

termToFol' :: ValueSubst -> γ ⊢ α -> FOL.Value
termToFol' ρ t =
  case t of
    Var i -> ρ i
    True' -> FOL.VTru
    False' -> FOL.VFal
    And' (termToFol' ρ -> φ) (termToFol' ρ -> ψ) -> FOL.VAnd φ ψ
    Imp' (termToFol' ρ -> φ) (termToFol' ρ -> ψ) -> FOL.VOr (FOL.VNot φ) ψ
    Or' (termToFol' ρ -> φ) (termToFol' ρ -> ψ) -> FOL.VOr φ ψ
    Forall' f -> FOL.VAll (\x -> termToFol' (\case
                                                Get -> x
                                                Weaken i -> ρ i)
                            (evalβ $ App (wkn f) (Var Get)))
    Exists' f -> FOL.VExi (\x -> termToFol' (\case
                                                Get -> x
                                                Weaken i -> ρ i)
                            (evalβ $ App (wkn f) (Var Get)))
    _ -> case viewApp ρ t of
                 Just (f, args) -> FOL.VApp f args
                 Nothing -> error $ "termToFol': viewApp produced Nothing"

termToFol :: NF γ α -> FOL.Value
termToFol = termToFol' (\case) . nf_to_λ 
-- ------------------------------------------------------------------


u :: Int -> γ ⊢ 'U
u i = Con $ Utt i

u' :: γ ⊢ 'R -> γ ⊢ 'U
u' = App $ Con Utt'

u'' :: [Maybe (Con 'E)] -> NF γ 'U
u'' as = Neu $ NeuCon $ Utt'' as

prop i = Con $ Property i
rel i = Con $ Relation i
vlad = Con Vlad
jp = Con JP
entity i = Con $ Entity i
heiht = Con Height
human = Con Human
θ = Con Theta
(≥) = Con GTE
emp = Con Empty
upd = Con Upd
upd' x c = upd `App` x `App` c
sel n = Con $ Sel n
sel' n c = sel n `App` c

(/\) :: γ ⊢ 'T -> γ ⊢ 'T -> γ ⊢ 'T
p /\ q = App (App (Con And) p) q

(\/) :: γ ⊢ 'T -> γ ⊢ 'T -> γ ⊢ 'T
p \/ q = App (App (Con Or) p) q

(-->) :: γ ⊢ 'T -> γ ⊢ 'T -> γ ⊢ 'T
p --> q = App (App (Con Imp) p) q

exists :: γ ⊢ (α ⟶ 'T) -> γ ⊢ 'T
exists φ = App (Con (Exists)) φ

reduce1step :: γ ⊢ α -> γ ⊢ α
reduce1step = \case
  App (App (Con Mult) (Con (Incl 1))) (reduce1step -> n) -> n
  App (App (Con Mult) (reduce1step -> m)) (Con (Incl 1)) -> m
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
  App (Con Mult) (Con (Incl 1)) -> True
  App (App (Con Mult) x) (Con (Incl 1)) -> True
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
clean = reduce1s . evalβ 

showR :: Rational -> String
showR (\x -> (numerator x, denominator x) -> (num, den))
  = case (num, den) of
      (0, _) -> "0"
      (_, 1) -> show num
      (_, _) -> "(" ++ show num ++ " / " ++ show den ++ ")"

data Con α where
  -- constants
  Tru :: Con 'T
  Fal :: Con 'T
  And :: Con ('T ⟶ 'T ⟶ 'T)
  Or :: Con ('T ⟶ 'T ⟶ 'T)
  Imp :: Con ('T ⟶ 'T ⟶ 'T)
  Forall :: Con ((α ⟶ 'T) ⟶ 'T)
  Exists :: Con ((α ⟶ 'T) ⟶ 'T)
  Equals :: Con (α ⟶ α ⟶ 'T)
  -- purpose stuff
  Incl :: Rational -> Con 'R
  Indi :: Con ('T ⟶ 'R)
  Addi :: Con ('R ⟶ 'R ⟶ 'R)
  Mult :: Con ('R ⟶ 'R ⟶ 'R)
  Expo :: Con ('R ⟶ 'R ⟶ 'R)
  Divi :: Con ('R ⟶ 'R ⟶ 'R)
  EqGen :: Equality α => Con ((α × α) ⟶ 'R)
  EqRl :: Con ('R ⟶ 'R ⟶ 'R)
  Utt :: Int -> Con 'U
  Utt' :: Con ('R ⟶ 'U)
  Utt'' :: [Maybe (Con 'E)] -> Con 'U
  MakeUtts :: Witness n -> Con ((Context n × 'U) ⟶ (('U ⟶ 'R) ⟶ 'R))
  Cau :: Con (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Les :: Con (('R ⟶ 'R) ⟶ 'R)
  Nml :: Con (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Qua :: Con (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Uni :: Con (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Interp :: Witness n -> Con ('U ⟶ Context n ⟶ 'T)
  HMorph :: Witness n -> Con x -> Con (Context n ⟶ x)
  Empty :: Con 'Γ
  Upd :: Con ('E ⟶ 'Γ ⟶ 'Γ)
  Pi :: Int -> Con ('Γ ⟶ 'E)
  -- Special constants (may take on distributions)
  Entity :: Int -> Con 'E
  MeasureFun :: Int -> Con ('E ⟶ 'R)
  Property :: Int -> Con ('E ⟶ 'T)
  Relation :: Int -> Con ('E ⟶ 'E ⟶ 'T)
  Proposition :: Int -> Con 'T
  Degree :: Int -> Con 'R
  GTE :: Con ('R ⟶ 'R ⟶ 'T)
  Sel :: Int -> Con ('Γ ⟶ 'E)

special :: Con α -> Bool
special = \case
  Entity _ -> True
  MeasureFun _ -> True
  Property _ -> True
  Relation _ -> True
  Proposition _ -> True
  Degree _ -> True
  GTE -> True
  Sel _ -> True
  _ -> False
  
pattern True' = Con Tru
pattern False' = Con Fal
pattern And' φ ψ = App (App (Con And) φ) ψ
pattern Or' φ ψ = Con Or `App` φ `App` ψ
pattern Imp' φ ψ = Con Imp `App` φ `App` ψ
pattern Forall' f = Con Forall `App` f
pattern Exists' f = Con Exists `App` f
pattern Equals' m n = Con Equals `App` m `App` n

instance Show (Con α) where
  show Tru = "⊤"
  show Fal = "⊥"
  show And = "(∧)"
  show Or = "(∨)"
  show Imp = "(→)"
  show Forall = "∀"
  show Exists = "∃"
  show Equals = "(=)"
  show (Incl x) = showR x
  show Indi = "𝟙"
  show Expo = "(^)"
  show Addi = "(+)"
  show Mult = "(*)"
  show Divi = "(/)"
  show Nml = "Normal"
  show Uni = "Uniform"
  show Cau = "Cauchy"
  show Les = "Lesbeue"
  show EqGen = "(≐)"
  show EqRl = "(≡)"
  show (Utt i) = "'U" ++ show i
  show Utt' = "'U"
  show (Utt'' as) = "U" ++ show as
  show (Interp _) = "⟦⟧"
  show Empty = "ε"
  show Upd = "(∷)"
  show (Pi n) = "π" ++ show n
  show (MakeUtts _) = "MakeUtts"
  show JP = "emacs"
  show Vlad = "the_command"
  show (Entity n) = "entity" ++ show n
  show Height = "heiht"
  show (MeasureFun n) = "measurefun" ++ show n
  show (Property 0) = "prepared"
  show (Proposition n) = "φ" ++ show n
  show Human = "animate"
  show (Property n) = "property" ++ show n
  show (Relation 0) = "wait_for"
  show (Relation n) = "relation" ++ show n
  show Theta = "θ"
  show (Degree n) = "deree" ++ show n
  show GTE = "(≥)"
  show (Sel n) = "sel" ++ show n

instance Additive (γ ⊢ 'R) where
  zero = Con (Incl 0)
  x + y  = Con Addi `App` x `App` y
instance Additive (NF γ 'R) where
  zero = normalForm zero
  x + y = normalForm (nf_to_λ x + nf_to_λ y)
instance AbelianAdditive (γ ⊢ 'R)
instance AbelianAdditive (NF γ 'R)
instance Group (γ ⊢ 'R) where
  negate = App (App (Con Mult) (Con (Incl (-1))))
instance Group (NF γ 'R) where
  negate = normalForm . negate . nf_to_λ
instance Multiplicative (γ ⊢ 'R) where
  one = Con (Incl 1)
  x * y  = Con Mult `App` x `App` y
  x ^+ n = Con (Expo) `App` x `App` Con ((Incl (fromInteger n)))
instance Multiplicative (NF γ 'R) where
  one = normalForm one
  x * y = normalForm (nf_to_λ x * nf_to_λ y)
instance Division (γ ⊢ 'R) where
  x / y  = Con Divi `App` x `App` y
instance Division (NF γ 'R) where
  x / y = normalForm (nf_to_λ x Algebra.Classes./ nf_to_λ y)
instance Roots (γ ⊢ 'R) where
  x ^/ n = Con (Expo) `App` x `App` Con (Incl n)

pattern JP = Entity 0
pattern Vlad = Entity 1
pattern Height = MeasureFun 1
pattern Human = Property 1
pattern Theta = Degree 1
  
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
(@@) = App

absInversion :: γ ⊢ ('R ⟶ α) -> (γ × 'R) ⊢ α
absInversion (Lam f) = f
absInversion t = App (wkn t) (Var Get)

-- Neutral terms (no constructors, except in aruments).
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

traverseNF :: Applicative f => (forall x. x ∈ γ -> f (x ∈ δ)) -> NF γ α -> f (NF δ α)
traverseNF f = \case
  NFLam x -> NFLam <$> traverseNF (lft' f) x
  NFPair x y ->NFPair <$> traverseNF f x <*> traverseNF f y
  Neu x -> Neu <$> traverseNeu f x

traverseNeu :: Applicative f => (forall x. x ∈ γ -> f (x ∈ δ)) -> Neutral γ α -> f (Neutral δ α)
traverseNeu f = \case
  NeuVar x -> NeuVar <$> f x
  NeuCon x -> pure (NeuCon x)
  NeuApp t u -> NeuApp <$> traverseNeu f t <*> traverseNF f u 
  NeuFst t -> NeuFst <$>  traverseNeu f t
  NeuSnd t -> NeuSnd <$>  traverseNeu f t
  NeuTT -> pure NeuTT 
  
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
substNeu (NeuApp m n) f = apply (substNeu m f) (substNF n f)
substNeu (NeuFst m) f = fst' (substNeu m f)
substNeu (NeuSnd m) f = snd' (substNeu m f)
substNeu NeuTT _ = Neu NeuTT
                            
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

apply :: NF γ (α1 ⟶ α2) -> NF γ α1 -> NF γ α2
apply t u = case t of
    NFLam m' -> substNF0 m' u -- β rule
    Neu m' -> case m' of      -- δ rules
      (NeuCon ((Pi i))) -> listFromContext u !! i
      (NeuCon ((MakeUtts n))) ->
        case u of
          NFPair k (Neu (NeuCon u''))
            -> if checkk n k
               then makeUtts' n (normalForm ctx) k (Neu (NeuCon u''))
               else deflt
          _ -> deflt
        where checkk :: Witness n -> NF γ (Context n) -> Bool
              checkk (S Z) = \case
                NFPair (NFPair (NFPair (NFPair (NFPair _ (NCon (_)))
                                        (NCon (_))) _) _) _ ->
                  True
                _ -> False
              checkk (S (S Z)) = \case
                NFPair (NFPair (NFPair (NFPair _ (NCon (_))) _) _) _ ->
                  True
                _ -> False
      (NeuCon (EqGen)) -> equals (fst' u) (snd' u)
      (NeuCon ((HMorph i s))) -> normalForm (App (hmorph i (Con (s))) (nf_to_λ u)) -- normalForm (hmorph i _)
      (NeuCon (Interp i)) -> case nf_to_λ u of
         Con (Utt 1) -> morph $ App (App (≥) (App heiht vlad)) θ -- 'Vlad is tall'
         Con (Utt 2) -> morph $ App (App (≥) θ) (App heiht vlad) -- 'Vlad is not tall'
         Con (Utt 3) -> morph $ Con $ Tru -- silence
         App (Con (Utt')) x ->
           morph $ App (App (≥) (App heiht vlad)) x
         Con (Utt'' [Nothing]) -> morph $ App (prop 0) (sel' 0 ctx)
         Con (Utt'' [Just e0]) ->
           morph $ App (prop 0) (Con $ e0)
         Con (Utt'' [Nothing, Nothing])
           -> morph $ App (App (rel 0) (sel' 0 ctx)) (sel' 1 ctx)
         Con (Utt'' [Just e0, Nothing]) ->
           morph $ App (App (rel 0) (Con e0)) (sel' 1 ctx)
         Con (Utt'' [Nothing, Just e1]) ->
           morph $ App (App (rel 0) (sel' 0 ctx)) (Con e1)
         Con (Utt'' [Just e0, Just e1]) ->
           morph $ App (App (rel 0) (Con e0)) (Con e1)
         _ -> deflt
        where morph = normalForm . hmorph i
      _ -> deflt
      where deflt = Neu (NeuApp m' u)
            ctx = upd' jp (upd' vlad emp)
            listFromContext :: NF γ 'Γ -> [NF γ 'E]
            listFromContext u = case nf_to_λ u of
              Con Empty -> []
              App (App (Con Upd) x) c
                -> normalForm x : listFromContext (normalForm c)

toFinite :: [NF γ α] -> NF γ ((α ⟶ 'R) ⟶ 'R)
toFinite ts = NFLam $ sum [ apply (Neu (NeuVar Get)) (wknNF t) | t <- ts ]

makeUtts :: NF γ 'Γ -> [NF γ ('Γ ⟶ 'E)] -> Con 'U -> NF γ (('U ⟶ 'R) ⟶ 'R)
makeUtts (nf_to_λ -> ctx) (map nf_to_λ -> [sel0]) = \case
  Utt'' [Nothing] -> toFinite $ [ u'' [Nothing]
                                , u'' [Just e0] ]
  u@(Utt'' [Just _]) -> normalForm $ η $ Con $ u  
  where NCon (e0) = normalForm (sel0 `App` ctx)
makeUtts (nf_to_λ -> ctx) (map nf_to_λ -> [sel0, sel1]) = \case
  Utt'' [Nothing, Nothing] -> toFinite $ [ u'' [Nothing, Nothing]
                                         , u'' [Just e0, Nothing]
                                         , u'' [Nothing, Just e1]
                                         , u'' [Just e0, Just e1]
                                         ]
  Utt'' [Just e0', Nothing] -> toFinite $ [ u'' [Just e0', Nothing]
                                          , u'' [Just e0', Just e1] ]
  Utt'' [Nothing, Just e1'] -> toFinite $ [ u'' [Nothing, Just e1']
                                          , u'' [Just e0, Just e1'] ]
  u@(Utt'' [Just _, Just _]) -> normalForm $ η $ Con $ u
  where NCon (e0) = normalForm (sel0 `App` ctx)
        NCon (e1) = normalForm (sel1 `App` ctx)

makeUtts' :: Witness n
          -> NF γ 'Γ -> NF γ (Context n) -> NF γ 'U -> NF γ (('U ⟶ 'R) ⟶ 'R)
makeUtts' (S Z) ctx k u =
  let Pair (Pair (Pair (Pair (Pair _ sel1) sel0) _) _) _ = nf_to_λ k
      Con (u') = nf_to_λ u
  in makeUtts ctx [normalForm sel0, normalForm sel1] u'
makeUtts' (S (S Z)) ctx k u =
  let Pair (Pair (Pair (Pair _ sel0) _) _) _ = nf_to_λ k
      Con (u') = nf_to_λ u
  in makeUtts ctx [normalForm sel0] u'

normalForm :: γ ⊢ α -> NF γ α
normalForm = \case
  Var i -> Neu $ NeuVar i
  Con c -> Neu $ NeuCon c
  App (normalForm -> m) (normalForm -> n) -> apply m n 
  Lam (normalForm -> m) -> NFLam m
  Fst (normalForm -> m) -> fst' m
  Snd (normalForm -> m) -> snd' m
  Pair (normalForm -> m) (normalForm -> n) -> NFPair m n
  TT -> Neu NeuTT

fst' :: NF γ (α × β) -> NF γ α
fst' = \case
           NFPair m' _ -> m'
           Neu m' -> Neu $ NeuFst m'

snd' :: NF γ (α1 × α2) -> NF γ α2
snd' = \case
           NFPair _ n' -> n'
           Neu m' -> Neu $ NeuSnd m'

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

instance Show (NF γ α) where
  show = show . nf_to_λ
instance Show (γ ⊢ α) where
  show = replace "%" "/" . \case
    Var Get -> "x"
    Var (Weaken i) -> show (Var i) ++ "'"
    App (App (Con And) (show -> p)) (show -> q)
      -> "(" ++ p ++ " ∧ " ++ q ++ ")"
    App (App (Con Or) (show -> p)) (show -> q)
      -> "(" ++ p ++ " ∨ " ++ q ++ ")"
    App (App (Con Imp) (show -> p)) (show -> q)
      -> "(" ++ p ++ " → " ++ q ++ ")"
    App (App (Con (Equals)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " = " ++ n ++ ")"
    App (App (Con Addi) (show -> m)) (show -> n)
      -> "(" ++ m ++ " + " ++ n ++ ")"
    App (App (Con Mult) (show -> m)) (show -> n)
      -> "(" ++ m ++ " * " ++ n ++ ")"
    App (App (Con Divi) (show -> m)) (show -> n)
      -> "(" ++ m ++ " / " ++ n ++ ")"
    App (Con (EqGen)) (Pair (show -> m) (show -> n))
      -> "(" ++ m ++ " ≐ " ++ n ++ ")"
    App (App (Con EqRl) (show -> m)) (show -> n)
      -> "(" ++ m ++ " ≐ " ++ n ++ ")"
    App (Con (Interp n)) (show -> u) -> "⟦" ++ u ++ "⟧"
    App (App (Con Upd) (show -> m)) (show -> n)
      -> m ++ "∷" ++ n
    App (App (Con GTE) (show -> m)) (show -> n)
      -> "(" ++ m ++ " ≥ " ++ n ++ ")"
    App (show -> m) (show -> n) -> m ++ "(" ++ n ++ ")"
    Con (show -> c) -> c
    Lam (show -> m) -> "λ(" ++ m ++ ")"
    Fst (show -> m) -> "(π₁ " ++ m ++ ")"
    Snd (show -> m) -> "(π₂ " ++ m ++ ")"
    TT -> "⋄"
    Pair (show -> m) (show -> n) -> "⟨" ++ m ++ ", " ++ n ++ "⟩"

displayDB :: γ ⊢ α -> IO ()
displayDB t = putStrLn $ show t

displayVs :: Unit ⊢ α -> IO ()
displayVs t = putStrLn $ replace "%" "/" $ displayVs' freshes (\case) t

freshes :: [String]
freshes = "" : map show ints >>= \i -> map (:i) ['x', 'y', 'z', 'u', 'v', 'w']
  where ints = 1 : map succ ints

displayVs1 :: (Unit × β)  ⊢ α -> String
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
  App (App (Con And) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " ∧ " ++ q ++ ")"
  App (App (Con Or) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " ∨ " ++ q ++ ")"
  App (App (Con Imp) (dd -> p)) (dd -> q)
    -> "(" ++ p ++ " → " ++ q ++ ")"
  App (App (Con (Equals)) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " = " ++ n ++ ")"
  App (App (Con Addi) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " + " ++ n ++ ")"
  App (App (Con Mult) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " * " ++ n ++ ")"
  App (App (Con Divi) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " / " ++ n ++ ")"
  App (Con (EqGen)) (Pair (dd -> m) (dd -> n))
    -> "(" ++ m ++ " ≐ " ++ n ++ ")"
  App (App (Con EqRl) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " ≐ " ++ n ++ ")"
  App (Con (Interp n)) (dd -> u) -> "⟦" ++ u ++ "⟧"
  App (App (Con Upd) (dd -> m)) (dd -> n)
    -> m ++ "∷" ++ n
  App (App (Con GTE) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " ≥ " ++ n ++ ")"
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

lft' :: Applicative f => (forall v. v ∈ γ -> f (v ∈ δ)) -> (forall v. v ∈ (γ × α) -> f (v ∈ (δ × α)))
lft' _ Get = pure Get
lft' f (Weaken x) = Weaken <$> (f x)


lft :: (α ∈ γ -> α ∈ δ) -> α ∈ (γ × β) -> α ∈ (δ × β)
lft f = \case
  Get -> Get
  Weaken i -> Weaken $ f i

π :: α ∈ κ -> γ ⊢ κ -> γ ⊢ α
π Get κ = Snd κ
π (Weaken i) κ = π i (Fst κ)

type Context0 = 'Unit × ('R ⟶ 'R ⟶ 'T) × 'R × ('E ⟶ 'T) × ('E ⟶ 'R) × 'E
type Context1 = 'Unit × 'T × ('Γ ⟶ 'E) × ('Γ ⟶ 'E) × ('E ⟶ 'E ⟶ 'T) × 'E × 'E
type Context2 = 'Unit × 'T × ('Γ ⟶ 'E) × ('E ⟶ 'T) × 'E × 'E

data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat

data Witness (n :: Nat) where
  Z :: Witness 'Zero
  S :: Witness n -> Witness ('Succ n)

type family Context (n :: Nat) where
  Context 'Zero = Context0
  Context ('Succ 'Zero) = Context1
  Context ('Succ ('Succ 'Zero)) = Context2

findC :: Witness n -> Con α -> α ∈ Context n
findC = \case
  Z -> \case
    Vlad -> Get
    Height -> Weaken Get
    Human -> Weaken (Weaken Get)
    Theta -> Weaken (Weaken (Weaken Get))
    GTE -> Weaken (Weaken (Weaken (Weaken Get)))
  S Z -> \case
    Entity 0 -> Get
    Entity 1 -> Weaken Get
    Relation 0 -> Weaken (Weaken Get)
    Sel 0 -> Weaken (Weaken (Weaken Get))
    Sel 1 -> Weaken (Weaken (Weaken (Weaken Get)))
    Proposition 0 -> Weaken (Weaken (Weaken (Weaken (Weaken Get))))
  S (S Z) -> \case
    Entity 0 -> Get
    Entity 1 -> Weaken Get
    Property 0 -> Weaken (Weaken Get)
    Sel 0 -> Weaken (Weaken (Weaken Get))
    Proposition 0 -> Weaken (Weaken (Weaken (Weaken Get)))
           
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
  Weaken (Weaken i) -> Weaken (Weaken i)

contr :: (γ × α × α) ⊢ β -> (γ × α) ⊢ β
contr = rename $ \case
  Get -> Get
  Weaken i -> i

hmorph0 :: Witness n -> γ ⊢ α -> (γ × Context n) ⊢ α
hmorph0 n = \case
  Var i -> Var $ Weaken i
  Con c | special c -> π (findC n c) (Var Get)
  Con c -> Con c
  App (hmorph0 n -> m) (hmorph0 n -> n) -> App m n
  Lam (hmorph0 n -> m) -> Lam $ exch m
  Fst (hmorph0 n -> m) -> Fst m
  Snd (hmorph0 n -> m) -> Snd m
  Pair (hmorph0 n -> m) (hmorph0 n -> n) -> Pair m n
  TT -> TT

hmorph :: Witness n -> γ ⊢ α -> γ ⊢ (Context n ⟶ α)
hmorph n (hmorph0 n -> m) = Lam m

η :: γ ⊢ α -> γ ⊢ ((α ⟶ 'R) ⟶ 'R)
η m = Lam (App (Var Get) (wkn m))

(⋆) :: γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ (α ⟶ ((β ⟶ 'R) ⟶ 'R)) -> γ ⊢ ((β ⟶ 'R) ⟶ 'R)
m ⋆ k = Lam (App (wkn m) (Lam (App (App (wkn (wkn k)) (Var Get)) (Var (Weaken Get)))))

(>>) :: γ ⊢ ((Unit ⟶ 'R) ⟶ 'R) -> γ ⊢ ((β ⟶ 'R) ⟶ 'R) -> γ ⊢ ((β ⟶ 'R) ⟶ 'R)
m >> k = m ⋆ Lam (wkn k)
