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
import Prelude hiding ((>>), Num(..))


data Type = E | 'T | R | U | 'Γ
          | Type :-> Type
          | Unit
          | Type :× Type

data (α :: Type) ∈ (γ :: Type) where
  Get :: α ∈ (γ × α)
  Weaken :: α ∈ γ -> α ∈ (γ × β)
deriving instance Show (α ∈ γ)
deriving instance Eq (α ∈ γ)
deriving instance Ord (α ∈ γ) -- do not change this instance, it is used for testing deepness of variables

type α × β = α ':× β
type α ⟶ β = α ':-> β
infixr ⟶
infixr :->

(≐) :: Equality α => γ ⊢ α -> γ ⊢ α -> γ ⊢ 'R
m ≐ n = App (Con (General EqGen)) (Pair m n)

noOccur :: (α ∈ (γ × x)) -> Maybe (α ∈ γ)
noOccur = \case
  Get -> Nothing
  Weaken x -> Just x

pattern NCon x = Neu (NeuCon x)
pattern NVar x = Neu (NeuVar x)
class Equality α where
  equals :: forall γ. NF γ α -> NF γ α -> NF γ 'R
instance Equality 'E where
  equals (NCon (Special (Entity m))) (NCon (Special (Entity n))) =
    NCon $ General $ Incl $ case m == n of True -> 1; False -> 0
  equals x y = Neu $ NeuApp (NeuCon (General EqGen)) (NFPair x y) 
instance Equality 'R where
  equals (NCon (General (Incl x))) (NCon (General (Incl y)))
    = case x == y of
        True -> one
        False -> NCon $ General $ Incl 0
  equals (NCon (Special (Degree m))) (NCon (Special (Degree n))) =
          NCon $ General $ Incl $ case m == n of True -> 1; False -> 0
  equals x y = Neu $ NeuCon (General EqRl) `NeuApp` x `NeuApp` y
instance Equality 'U where
  equals (NCon (General (Utt i))) (NCon (General (Utt j))) = case i == j of
                             True -> one
                             False -> NCon (General (Incl 0))
  equals (Neu (NeuApp (NeuCon (General Utt')) x))
    (Neu (NeuApp (NeuCon (General Utt')) y)) = equals x y
  equals (NCon (General (Utt'' es0))) (NCon (General (Utt'' es1))) =
    checkEquality es0 es1
    where checkEquality :: [Maybe (Special 'E)] -> [Maybe (Special 'E)]
                        -> NF γ 'R
          checkEquality [] [] = one
          checkEquality (Nothing:es0) (Nothing:es1) = checkEquality es0 es1
          checkEquality (Just _ : _) (Nothing:_) = NCon (General (Incl 0))
          checkEquality (Nothing:_) (Just _ : _) = NCon (General (Incl 0))
          checkEquality (Just x : es0) (Just y : es1) =
            equals (NCon $ Special x) (NCon $ Special y) * checkEquality es0 es1
  equals m n = Neu $ (NeuCon $ General $ EqGen) `NeuApp` (NFPair m n)
instance Equality Unit where
  equals _ _ = one
instance (Equality α, Equality β) => Equality (α × β) where
  equals (NFPair m n) (NFPair m' n') = equals m m' * equals n n'
  equals m n = Neu $ (NeuCon $ General $ EqGen) `NeuApp` (NFPair m n)
instance Equality ('E ⟶ 'R) where
  equals :: forall γ. NF γ ('E ⟶ 'R) -> NF γ ('E ⟶ 'R) -> NF γ 'R
  equals (NCon (Special (MeasureFun m))) (NCon (Special (MeasureFun n))) =
    NCon $ General $ Incl $ case m == n of True -> 1; False -> 0
  equals (NFLam m) (NFLam n)
    | Just x <- traverseNF noOccur (equals m n) = x
  equals t u = Neu ((NeuCon $ General $ EqGen) `NeuApp` (NFPair t u))
instance Equality ('E ⟶ 'T) where
  equals (NCon (Special (Property m))) (NCon (Special (Property n))) =
    NCon $ General $ Incl $ case m == n of True -> 1; False -> 0
instance Equality ('E ⟶ 'E ⟶ 'T) where
  equals (NCon (Special (Relation m))) (NCon (Special (Relation n))) =
    NCon $ General $ Incl $ case m == n of True -> 1; False -> 0
instance Equality ('R ⟶ 'R ⟶ 'T) where
  equals (NCon (Special GTE)) (NCon (Special GTE)) = one
instance Equality 'Γ where
  equals (NCon (General Empty)) (NCon (General Empty)) = one
instance Equality ('E ⟶ 'Γ ⟶ 'Γ) where
  equals (NCon (General Upd)) (NCon (General Upd)) = one
instance Equality ('Γ ⟶ 'E) where
  equals (NCon (Special (Sel i))) (NCon (Special (Sel j))) =
    case i == j of
      True -> one
      False -> NCon (General (Incl 0))
  equals (NCon (General (Pi i))) (NCon (General (Pi j))) =
    case i == j of
      True -> one
      False -> NCon (General (Incl 0))

u :: Int -> γ ⊢ 'U
u i = Con $ General $ Utt i

u' :: γ ⊢ 'R -> γ ⊢ 'U
u' = App $ Con $ General Utt'

u'' :: [Maybe (Special 'E)] -> NF γ 'U
u'' as = Neu $ NeuCon $ General $ Utt'' as


prop i = Con $ Special $ Property i
rel i = Con $ Special $ Relation i
vlad = Con $ Special Vlad
jp = Con $ Special JP
entity i = Con $ Special $ Entity i
height = Con $ Special Height
human = Con $ Special Human
θ = Con $ Special Theta
(≥) = Con $ Special GTE
emp = Con $ General Empty
upd = Con $ General Upd
upd' x c = App (App upd x) c
sel n = Con $ Special $ Sel n
sel' n c = App (sel n) c

(/\) :: γ ⊢ 'T -> γ ⊢ 'T -> γ ⊢ 'T
p /\ q = App (App (Con (Logical And)) p) q

(\/) :: γ ⊢ 'T -> γ ⊢ 'T -> γ ⊢ 'T
p \/ q = App (App (Con (Logical Or)) p) q

(-->) :: γ ⊢ 'T -> γ ⊢ 'T -> γ ⊢ 'T
p --> q = App (App (Con (Logical Imp)) p) q

exists :: γ ⊢ (α ⟶ 'T) -> γ ⊢ 'T
exists φ = App (Con (Logical Exists)) φ

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

can'Reduce :: γ ⊢ α -> Bool
can'Reduce = \case
  App (Con (General Mult)) (Con (General (Incl 1))) -> True
  App (App (Con (General Mult)) x) (Con (General (Incl 1))) -> True
  Var i -> False
  Con c -> False
  App (can'Reduce -> m) (can'Reduce -> n) -> m || n
  Lam m -> can'Reduce m
  Fst m -> can'Reduce m
  Snd m -> can'Reduce m
  TT -> False
  Pair (can'Reduce -> m) (can'Reduce -> n) -> m || n

reduce1s :: γ ⊢ α -> γ ⊢ α
reduce1s m = if can'Reduce m then reduce1s (reduce1step m) else m

clean :: γ ⊢ α -> γ ⊢ α
clean = reduce1s . evalβ 

showR :: Rational -> String
showR (\x -> (numerator x, denominator x) -> (num, den))
  = case (num, den) of
      (0, _) -> "0"
      (_, 1) -> show num
      (_, _) -> "(" ++ show num ++ " / " ++ show den ++ ")"

data Logical α where
  Tru :: Logical 'T
  Fal :: Logical 'T
  And :: Logical ('T ⟶ 'T ⟶ 'T)
  Or :: Logical ('T ⟶ 'T ⟶ 'T)
  Imp :: Logical ('T ⟶ 'T ⟶ 'T)
  Forall :: Logical ((α ⟶ 'T) ⟶ 'T)
  Exists :: Logical ((α ⟶ 'T) ⟶ 'T)
  Equals :: Logical (α ⟶ α ⟶ 'T)

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
  Incl :: Rational -> General 'R
  Indi :: General ('T ⟶ 'R)
  Addi :: General ('R ⟶ 'R ⟶ 'R)
  Mult :: General ('R ⟶ 'R ⟶ 'R)
  Expo :: General ('R ⟶ 'R ⟶ 'R)
  Divi :: General ('R ⟶ 'R ⟶ 'R)
  EqGen :: Equality α => General ((α × α) ⟶ 'R)
  EqRl :: General ('R ⟶ 'R ⟶ 'R)
  Utt :: Int -> General 'U
  Utt' :: General ('R ⟶ 'U)
  Utt'' :: [Maybe (Special 'E)] -> General 'U
  MakeUtts :: Witness n -> General ((Context n × 'U) ⟶ (('U ⟶ 'R) ⟶ 'R))
  Cau :: General (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Les :: General (('R ⟶ 'R) ⟶ 'R)
  Nml :: General (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Qua :: General (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Uni :: General (('R × 'R) ⟶ ('R ⟶ 'R) ⟶ 'R)
  Interp :: Witness n -> General ('U ⟶ Context n ⟶ 'T)
  Empty :: General 'Γ
  Upd :: General ('E ⟶ 'Γ ⟶ 'Γ)
  Pi :: Int -> General ('Γ ⟶ 'E)

instance Additive (γ ⊢ 'R) where
  zero = Con (General (Incl 0))
  x + y  = Con (General Addi) `App` x `App` y
instance Additive (NF γ 'R) where
  zero = normalForm zero
  x + y = normalForm (nf_to_λ x + nf_to_λ y)
instance AbelianAdditive (γ ⊢ 'R)
instance AbelianAdditive (NF γ 'R)
instance Group (γ ⊢ 'R) where
  negate = App (App (Con (General Mult)) (Con (General (Incl (-1)))))
instance Group (NF γ 'R) where
  negate = normalForm . negate . nf_to_λ
instance Multiplicative (γ ⊢ 'R) where
  one = Con (General (Incl 1))
  x * y  = Con (General Mult) `App` x `App` y
  x ^+ n = Con (General Expo) `App` x `App` Con (General (Incl (fromInteger n)))
instance Multiplicative (NF γ 'R) where
  one = normalForm one
  x * y = normalForm (nf_to_λ x * nf_to_λ y)
instance Division (γ ⊢ 'R) where
  x / y  = Con (General Divi) `App` x `App` y
instance Division (NF γ 'R) where
  x / y = normalForm (nf_to_λ x Algebra.Classes./ nf_to_λ y)
instance Roots (γ ⊢ 'R) where
  x ^/ n = Con (General Expo) `App` x `App` Con (General (Incl n))
instance Show (General α) where
  show (Incl x) = showR x
  show Indi = "𝟙"
  show Expo = "(^)"
  show Addi = "(+)"
  show Mult = "(*)"
  show Divi = "(/)"
  show Nml = "Normal"
  show Uni = "Uniform"
  show Cau = "Cauchy"
  show Les = "Lesbegue"
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

data Special α where
  Entity :: Int -> Special 'E
  MeasureFun :: Int -> Special ('E ⟶ 'R)
  Property :: Int -> Special ('E ⟶ 'T)
  Relation :: Int -> Special ('E ⟶ 'E ⟶ 'T)
  Degree :: Int -> Special 'R
  GTE :: Special ('R ⟶ 'R ⟶ 'T)
  Sel :: Int -> Special ('Γ ⟶ 'E)

pattern JP = Entity 0
pattern Vlad = Entity 1
pattern Height = MeasureFun 1
pattern Human = Property 1
pattern Theta = Degree 1
  
instance Show (Special α) where
  show JP = "jp"
  show Vlad = "v"
  show (Entity n) = "entity" ++ show n
  show Height = "height"
  show (MeasureFun n) = "measurefun" ++ show n
  show Human = "human"
  show (Property n) = "property" ++ show n
  show (Relation n) = "relation" ++ show n
  show Theta = "θ"
  show (Degree n) = "degree" ++ show n
  show GTE = "(≥)"
  show (Sel n) = "sel" ++ show n

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
  TT :: γ ⊢ Unit
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
      (NeuCon (General (Pi i))) -> listFromContext u !! i
      (NeuCon (General (MakeUtts n))) ->
        case u of
          NFPair k (Neu (NeuCon u''))
            -> if checkk n k then makeUtts' n k (Neu (NeuCon u'')) else deflt
          _ -> deflt
        where checkk :: Witness n -> NF γ (Context n) -> Bool
              checkk (S Z) = \case
                NFPair (NFPair _ (Neu (NeuCon (Special _))))
                  (Neu (NeuCon (Special _))) -> True
                _ -> False
              checkk (S (S Z)) = \case
                NFPair (NFPair _ (Neu (NeuCon (Special _))))
                  (Neu (NeuCon (Special _))) -> True
                _ -> False
      (NeuCon (General EqGen)) -> equals (fst' u) (snd' u)
      (NeuCon (General (Interp i))) -> case nf_to_λ u of
         Con (General (Utt 1)) -> morph $ App (App (≥) (App height vlad)) θ -- 'Vlad is tall'
         Con (General (Utt 2)) -> morph $ App (App (≥) θ) (App height vlad) -- 'Vlad is not tall'
         Con (General (Utt 3)) -> morph $ Con $ Logical Tru -- silence
         App (Con (General Utt')) x ->
           morph $ App (App (≥) (App height vlad)) x
         Con (General (Utt'' [Nothing])) -> morph $ App (prop 0) (sel' 0 ctx)
         Con (General (Utt'' [Just e0])) ->
           morph $ App (prop 0) (Con $ Special e0)
         Con (General (Utt'' [Nothing, Nothing]))
           -> morph $ App (App (rel 0) (sel' 0 ctx)) (sel' 1 ctx)
         Con (General (Utt'' [Just e0, Nothing])) ->
           morph $ App (App (rel 0) (Con $ Special e0)) (sel' 1 ctx)
         Con (General (Utt'' [Nothing, Just e1])) ->
           morph $ App (App (rel 0) (sel' 0 ctx)) (Con $ Special e1)
         Con (General (Utt'' [Just e0, Just e1])) ->
           morph $ App (App (rel 0) (Con $ Special e0)) (Con $ Special e1)
         _ -> deflt
         where morph = normalForm . hmorph i
               ctx = upd' jp (upd' vlad emp) 
      _ -> deflt
      where deflt = Neu (NeuApp m' u)
            listFromContext :: NF γ 'Γ -> [NF γ 'E]
            listFromContext u = case nf_to_λ u of
              Con (General Empty) -> []
              App (App (Con (General Upd)) x) c
                -> normalForm x : listFromContext (normalForm c)

toFinite :: [NF γ α] -> NF γ ((α ⟶ 'R) ⟶ 'R)
toFinite [] = NFLam $ normalForm zero
toFinite (t:ts) = NFLam $ (Neu $ NeuApp (NeuVar Get) (wknNF t)) +
                  case toFinite (map wknNF ts) of
                    NFLam m -> substNF0 m (Neu (NeuVar Get))
                    Neu m -> Neu $ NeuApp m (Neu (NeuVar Get))

makeUtts :: [Special 'E] -> General 'U -> NF γ (('U ⟶ 'R) ⟶ 'R)
makeUtts [e0, e1] = \case
  Utt'' [Nothing, Nothing] -> toFinite $
    u'' [Nothing, Nothing] :
    [ u'' [Just e0', Nothing] | e0' <- [e0, e1] ] ++
    [ u'' [Nothing, Just e1'] | e1' <- [e0, e1] ] ++
    [ u'' [Just e0', Just e1'] | e0' <- [e0, e1], e1' <- [e0, e1] ]
  Utt'' [Just e0', Nothing] -> toFinite $
    u'' [Just e0', Nothing] : [ u'' [Just e0', Just e1'] | e1' <- [e0, e1] ]
  Utt'' [Nothing, Just e1'] -> toFinite $
    u'' [Nothing, Just e1'] : [ u'' [Just e0', Just e1'] | e0' <- [e0, e1] ]
  u@(Utt'' [Just _, Just _]) -> normalForm $ η $ Con $ General u
  Utt'' [Nothing] -> toFinite $
    [ u'' [Just e0'] | e0' <- [e0, e1] ]
  u@(Utt'' [Just _]) -> normalForm $ η $ Con $ General u

makeUtts' :: Witness n -> NF γ (Context n) -> NF γ 'U -> NF γ (('U ⟶ 'R) ⟶ 'R)
makeUtts' (S Z) k u =
  let Pair (Pair _ (Con (Special e0))) (Con (Special e1)) = nf_to_λ k
      Con (General u') = nf_to_λ u
  in makeUtts [e0, e1] u'
makeUtts' (S (S Z)) k u =
  let Pair (Pair _ (Con (Special e0))) (Con (Special e1)) = nf_to_λ k
      Con (General u') = nf_to_λ u
  in makeUtts [e0, e1] u'

-- >>> makeUtts [Vlad, JP] $ Utt'' [Nothing, Nothing]
-- λ((x(U[Just v,Just v]) + (x(U[Just v,Just jp]) + (x(U[Just jp,Just v]) + (x(U[Just jp,Just jp]) + 0)))))

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
    App (Con (General EqGen)) (Pair (show -> m) (show -> n))
      -> "(" ++ m ++ " ≐ " ++ n ++ ")"
    App (App (Con (General EqRl)) (show -> m)) (show -> n)
      -> "(" ++ m ++ " ≐ " ++ n ++ ")"
    App (Con (General (Interp n))) (show -> u) -> "⟦" ++ u ++ "⟧"
    App (App (Con (General Upd)) (show -> m)) (show -> n)
      -> m ++ "∷" ++ n
    App (App (Con (Special GTE)) (show -> m)) (show -> n)
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
  App (Con (General EqGen)) (Pair (dd -> m) (dd -> n))
    -> "(" ++ m ++ " ≐ " ++ n ++ ")"
  App (App (Con (General EqRl)) (dd -> m)) (dd -> n)
    -> "(" ++ m ++ " ≐ " ++ n ++ ")"
  App (Con (General (Interp n))) (dd -> u) -> "⟦" ++ u ++ "⟧"
  App (App (Con (General Upd)) (dd -> m)) (dd -> n)
    -> m ++ "∷" ++ n
  App (App (Con (Special GTE)) (dd -> m)) (dd -> n)
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
lft' _ (Get) = pure Get
lft' f (Weaken x) = Weaken <$> (f x)


lft :: (α ∈ γ -> α ∈ δ) -> α ∈ (γ × β) -> α ∈ (δ × β)
lft f = \case
  Get -> Get
  Weaken i -> Weaken $ f i

π :: α ∈ κ -> γ ⊢ κ -> γ ⊢ α
π Get κ = Snd κ
π (Weaken i) κ = π i (Fst κ)

type Context0 = Unit × ('R ⟶ 'R ⟶ 'T) × 'R × ('E ⟶ 'T) × ('E ⟶ 'R) × 'E
type Context1 = Unit ×
                ('Γ ⟶ 'E) ×
                ('Γ ⟶ 'E) ×
                ('E ⟶ 'E ⟶ 'T) ×
                ('E ⟶ 'E ⟶ 'T) ×
                ('E ⟶ 'T) × 'E × 'E
type Context2 = Unit × ('Γ ⟶ 'E) × ('E ⟶ 'T) × 'E × 'E

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

findC :: Witness n -> Special α -> α ∈ Context n
findC = \case
  Z -> \case
    Vlad -> Get
    Height -> Weaken Get
    Human -> Weaken (Weaken Get)
    Theta -> Weaken (Weaken (Weaken Get))
    GTE -> Weaken (Weaken (Weaken (Weaken (Get))))
  S Z -> \case
    Entity 0 -> Get
    Entity 1 -> Weaken Get
    Property 0 -> Weaken (Weaken Get)
    Relation 0 -> Weaken (Weaken (Weaken Get))
    Relation 1 -> Weaken (Weaken (Weaken (Weaken Get)))
    Sel 0 -> Weaken (Weaken (Weaken (Weaken (Weaken Get))))
    Sel 1 -> Weaken (Weaken (Weaken (Weaken (Weaken (Weaken Get)))))
  S (S Z) -> \case
    Entity 0 -> Get
    Entity 1 -> Weaken Get
    Property 0 -> Weaken (Weaken Get)
    Sel 0 -> Weaken (Weaken (Weaken Get))
           
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
  Con (Special c) -> π (findC n c) (Var Get)
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
