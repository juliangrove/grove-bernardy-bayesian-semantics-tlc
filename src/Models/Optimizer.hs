{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}


module Models.Optimizer where

import Data.List
import TLC.Terms

type Re = Double

data Domain γ α = Domain {domainConditions :: [Cond (γ, α)]
                         ,domainLoBounds,domainHiBounds :: [Expr γ α]}


positive :: Expr γ Re -> Cond γ
positive e = InEqlty e -- TODO: suggests renaming

negative :: Expr γ Re -> Cond γ
negative e = positive ((-1) *^ e)

lessThan :: Expr γ Re -> Expr γ Re -> Cond γ
t `lessThan` u = negative (t ++ (-1) *^ u)


greaterThan :: Expr γ Re -> Expr γ Re -> Cond γ
greaterThan = flip lessThan


domainToConditions :: Expr γ Re -> Domain γ Re -> P γ -> P γ
domainToConditions i = \case
  Domain [] [] [] -> id
  Domain (c:cs) los his
    -> Cond (substCond (\Here -> i) c) . domainToConditions i (Domain cs los his)
  Domain cs (e:los) his
    -> Cond (e `lessThan` i) . domainToConditions i (Domain cs los his)
  Domain cs los (e:his)
    -> Cond (i `lessThan` e) . domainToConditions i (Domain cs los his)


data Available α γ where
  Here :: Available α (γ, α)
  There :: Available α γ -> Available α (γ, β)
deriving instance Show (Available α γ)
 
type Expr γ α = [(Re, Available α γ)]
  -- linear combination. list of coefficients and variables [x is a ring]
  -- Example u - v is represented by [(1,"u"), (-1,"v")]



data Cond γ = InEqlty {condExpr :: (Expr γ Re)}
              -- Meaning of this constructor:  expression ≤ 0
              -- Example: u ≤ v is represented by u - v ≤ 0
            | Eqlty {condExpr :: (Expr γ Re)}
              -- Meaning of this constructor:  expression = 0
              -- Example: u = v is represented by u - v = 0
            

restrictDomain :: α ~ Re => Cond (γ, α) -> Domain γ α -> Domain γ α
  -- restrictDomain c (Domain cs' lowBounds highBounds) = Domain (c : cs') lowBounds highBounds
  -- basic version
restrictDomain c (Domain cs los his) = case solve' c of -- version with solver
  (LT, e) -> Domain cs los (e:his) 
  (GT, e) -> Domain cs (e:los) (his)

data P γ where
  Integrate :: (Re ~ d) => Domain γ d -> P (γ, d) -> P γ
  Cond :: Cond γ -> P γ -> P γ
  Ret  :: Expr γ Re -> P γ
  One :: P γ -- TODO: make sure expressions have constants too

type Subst γ δ = (forall x. Available x γ -> Expr δ x)

wkSubst :: Subst γ δ -> Subst (γ,x) (δ,x)
wkSubst f = \case
  Here -> [(1,Here)]
  There x -> [(c, There y) | (c,y) <- f x]

substExpr :: Subst γ δ -> forall x. Expr γ x -> Expr δ x
substExpr f e = concat [c *^ f x | (c,x) <- e]

substCond :: Subst γ δ -> Cond γ -> Cond δ
substCond f (InEqlty e) = InEqlty (substExpr f e)
substCond f (Eqlty e) = Eqlty (substExpr f e)

substDomain :: Subst γ δ -> Domain γ d -> Domain δ d
substDomain f (Domain c lo hi) = Domain (substCond (wkSubst f) <$> c) (substExpr f <$> lo) (substExpr f <$> hi)

substP :: Subst γ δ -> P γ -> P δ
substP f p0 = case p0 of
  Ret e -> Ret (substExpr f e)
  Cond c p -> Cond (substCond f c) (substP f p)
  One -> One
  Integrate d p -> Integrate (substDomain f d) (substP (wkSubst f) p)

type family Eval γ where
  Eval R = Re
  Eval Unit = ()
  Eval (γ × α) = (Eval γ, Eval α)

type family RepOf γ where
  RepOf Re = R
  RepOf () = Unit
  RepOf (γ, α) = (RepOf γ × RepOf α)

evalVar :: α ∈ γ -> Available (Eval α) (Eval γ)
evalVar = \case
  Get -> Here
  Weaken (evalVar -> i) -> There i

pattern Eqs i j
  = Neu (NeuApp (NeuApp (NeuCon (Rl EqRl)) (Neu (NeuVar i))) (Neu (NeuVar j)))

-- evalP :: NF γ R -> P (Eval γ)
-- evalP = \case
--   Eqs (evalVar -> i) (evalVar -> j) -> Cond (Eqlty i j) One

type Vars γ  = forall v. Available v γ -> String

showExpr :: Show α => Vars γ -> Expr γ α -> String
showExpr _ [] = "0"
showExpr v xs = intercalate " + " $
  map parens [ show k ++ " * " ++ v x | (k, x) <- xs ]

showCond :: Vars γ -> Cond γ -> String
showCond v = \case
  c@(InEqlty c') -> "𝟙" <> (parens $ showExpr v c' <> " ≤ 0")
  c@(Eqlty c') -> parens $ showExpr v c' ++ " ≐ 0"

parens :: [Char] -> [Char]
parens x = "(" ++ x ++ ")"

braces :: [Char] -> [Char]
braces x = "{" ++ x ++ "}"

showBounds :: Show α => Vars γ -> Bool -> [Expr γ α] -> [Char]
showBounds _ lo [] = (if lo then "-" else "+") <> "∞"
showBounds v lo xs = (intercalate (if lo then "⊔" else "⊓") $ map (showExpr v) xs)

when :: [a] -> [Char] -> [Char]
when [] _ = ""
when _ x = x

showP :: [String] -> Vars γ -> P γ -> String
showP freshes@(f:fs) v = \case
  One -> "1"
  Ret x -> parens (showExpr v x)
  Integrate (Domain cs los his) e -> "∫"  ++ (when cs $ f ++ "∈" ++ braces (intercalate "∧" $ map (showCond (\case Here -> f; There i -> v i)) cs))
                 ++ (when (los ++ his) (braces (showBounds v True los
                            ++ "≤" ++ f ++ "≤" ++
                            showBounds v False his)))
                 ++ showP fs (\case Here -> f; There i -> v i) e
  Cond c e -> showCond v c ++ "*" ++ showP freshes v e

showProg :: P () -> String
showProg = showP freshes (\case)

freshes :: [String]
freshes = "" : map show ints >>= \i -> map (:i) ['x', 'y', 'z', 'u', 'v', 'w']
  where ints = 1 : map succ ints

instance Show (P ()) where
  show = showProg

type Solution γ d  = (Ordering, Expr γ d)

-- @solve e x@ returns the coefficient of the 1st variable in the expression, and the rest (terms not involving the 1st variable).
-- ie. c x + e = 0
solve :: (x ~ Re) => Expr (γ,x) x -> (x, Expr γ x)
solve [] = (0, [])
solve ((c, Here) : xs) = (c + c', e)
  where (c', e) = solve xs
solve ((c, There x) : xs) = (c', (c, x) : e)
  where (c', e) = solve xs 

solve' :: Cond (γ, Re) -> Solution γ Re
solve' c0 = case c0 of
      Eqlty _ -> (EQ, (-1/c) *^ e)
      InEqlty _ -> if c < 0 then (GT, (1 / (-c)) *^ e) else (LT, (1 / c) *^ e)
    where (c, e) = solve (condExpr c0)
  
-- multiplication by scalar (expresions are linear)
(*^) :: Num t => t -> [(t, b)] -> [(t, b)]
_ *^ [] = []
c *^ ((c', v) : xs) = (c * c', v) : c *^ xs

shallower :: SomeVar γ -> SomeVar γ -> Bool
SomeVar Here `shallower` _ = False
SomeVar (There _) `shallower` SomeVar Here = True
SomeVar (There x) `shallower` SomeVar (There y) = SomeVar x `shallower` SomeVar y

data SomeVar γ where
  SomeVar :: Available v γ -> SomeVar γ

minVar :: SomeVar γ -> SomeVar γ -> SomeVar γ
minVar (SomeVar Here) _ = SomeVar Here
minVar _ (SomeVar Here)  = SomeVar Here 
minVar (SomeVar (There x)) (SomeVar (There y)) = case minVar (SomeVar x) (SomeVar y) of
  SomeVar z -> SomeVar (There z)

deepest :: Cond γ -> SomeVar γ
deepest = \case
  InEqlty e -> foldr1 minVar . map SomeVar . map snd $ e
  Eqlty e -> foldr1 minVar . map SomeVar . map snd $ e

travExpr :: Applicative f => (forall v. Available v γ -> f (Available v δ)) -> Expr γ t -> f (Expr δ t)
travExpr f xs = traverse (\(k, e) -> (k,) <$> f e) xs

occurExpr :: Expr (γ, x) t -> Maybe (Expr γ t)
occurExpr = travExpr $ \case
  Here -> Nothing
  There x -> Just x

integrate :: d ~ Re => Domain γ d -> P (γ, d) -> P γ
integrate d (Cond c@(InEqlty c') e) = case occurExpr c' of
  Nothing -> integrate (restrictDomain c d) e
  Just c'' -> cond (InEqlty c'') (integrate d e)
integrate d (Cond (Eqlty c') e) = case occurExpr c' of
  Nothing ->
    -- We apply the rule: ∫ f(x) δ(c x + k) dx = f(-k/c)
    
    -- (The correct rule is: ∫ f(x) δ(c x + k) dx = 1/c f(-k/c)
    -- HOWEVER, due to the way we generate the equalities, my hunch is
    -- that we already take into account this coefficient. To be
    -- investigated.)

    domainToConditions x0 d $ substP (\Here -> x0) e
    
    where (coef,expr) = solve c'
          x0 = (-1/coef) *^ expr
  Just c'' -> cond (Eqlty c'') (integrate d e)
integrate d e = Integrate d e

cond :: Cond γ -> P γ -> P γ
cond c (Cond c' e) = if (deepest c) `shallower` (deepest c') then Cond c (Cond c' e) else Cond c' (cond c e)
cond c (normalise -> e) = Cond c e

normalise :: P γ -> P γ
normalise = \case
  Cond c (normalise -> e) -> cond c e
  Integrate d (normalise -> e) -> integrate d e
  Ret x -> Ret x
  One -> One

-- Domain without restriction
full :: Domain γ x
full = Domain [] [] []

example :: P ()
example = Integrate full $ Integrate full $ Cond (InEqlty [(3, There Here), (2, Here)]) $ Cond (InEqlty [(1, There Here)]) One

example1 :: P ()
example1 = Integrate full $ Integrate full $ Cond (Eqlty [(1,(There Here)),(-1,Here)] ) One

-- >>> example
-- ∫∫𝟙((3.0 * x) + (2.0 * y) ≤ 0)*𝟙((1.0 * x) ≤ 0)*1

-- >>> normalise example
-- ∫{-∞≤x≤0}∫{-∞≤y≤(1.5 * x)}1

-- >>> example1
-- ∫∫((1.0 * x) + (-1.0 * y) ≐ 0)*1

-- >>> normalise example1
-- ∫1
