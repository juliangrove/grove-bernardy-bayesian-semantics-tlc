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

data Domain γ α = Domain { domainConditions :: [Cond (γ, α)]
                         , domainLoBounds, domainHiBounds :: [Expr γ α] }

-- positive :: Expr γ Re -> Cond γ
-- positive e = negative ((-1) *^ e)

negative :: Expr γ Re -> Cond γ
negative e = IsNegative e -- TODO: suggests renaming IsNegative ↦ Negative

lessThan :: Expr γ Re -> Expr γ Re -> Cond γ
t `lessThan` u = negative (t `add` ((-1) *^ u))

-- greaterThan :: Expr γ Re -> Expr γ Re -> Cond γ
-- greaterThan = flip lessThan

-- | @domainToConditions x₀ d@ creates the conditions corresponding to x₀ ∈ d.
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
 
data Expr γ α = Expr α [(α, Available α γ)]
  -- linear combination. list of coefficients and variables [α is a vector space]
  -- Example u - v is represented by [(1,"u"), (-1,"v")]


-- Induced vector space structure over Expr γ α:

-- multiplication by scalar (expresions are linear)
(*^) :: Num α => α -> Expr γ α -> Expr γ α
c *^ Expr k0 xs = Expr (c * k0) [ (c * c', v) | (c',v) <- xs ]

-- addition
add :: Num α => Expr γ α -> Expr γ α -> Expr γ α
add (Expr a xs) (Expr a' xs') = Expr (a + a') (xs ++ xs')

zero = Expr 0 []

data Cond γ = IsNegative { condExpr :: (Expr γ Re) }
              -- Meaning of this constructor:  expression ≤ 0
              -- Example: u ≤ v is represented by u - v ≤ 0
            | IsZero { condExpr :: (Expr γ Re) }
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

type Subst γ δ = (forall x. Num x => Available x γ -> Expr δ x)

wkSubst :: Subst γ δ -> Subst (γ, x) (δ, x)
wkSubst f = \case
  Here -> Expr 0 [(1,Here)]
  There x -> Expr k0 [(c, There y) | (c,y) <- xs]
    where Expr k0 xs = f x

substExpr :: Subst γ δ -> forall x. Num x => Expr γ x -> Expr δ x
substExpr f (Expr k0 e) = foldr add (Expr k0 []) [c *^ f x | (c,x) <- e]

substCond :: Subst γ δ -> Cond γ -> Cond δ
substCond f (IsNegative e) = IsNegative (substExpr f e)
substCond f (IsZero e) = IsZero (substExpr f e)

substDomain :: Num d => Subst γ δ -> Domain γ d -> Domain δ d
substDomain f (Domain c lo hi) = Domain (substCond (wkSubst f) <$> c) (substExpr f <$> lo) (substExpr f <$> hi)

substP :: Subst γ δ -> P γ -> P δ
substP f p0 = case p0 of
  Ret e -> Ret (substExpr f e)
  Cond c p -> Cond (substCond f c) (substP f p)
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

pattern Mults x y
  = Neu (NeuApp (NeuApp (NeuCon (Rl Mult)) x) y)

evalP :: NF γ R -> P (Eval γ) -> P (Eval γ)
evalP = \case
  Eqs (evalVar -> i) (evalVar -> j) -> Cond (IsZero $ Expr 1 [(1, i), (-1, j)])
  Mults (evalP -> x) (evalP -> y) -> x . y
  
type Vars γ  = forall v. Available v γ -> String

showExpr :: Show α => Vars γ -> Expr γ α -> String
showExpr v (Expr k0 xs) = intercalate " + " $
                          show k0 : [ parens $ show k ++ " * " ++ v x |
                                      (k, x) <- xs ]

showCond :: Vars γ -> Cond γ -> String
showCond v = \case
  c@(IsNegative c') -> "𝟙" <> (parens $ showExpr v c' <> " ≤ 0")
  c@(IsZero c') -> parens $ showExpr v c' ++ " ≐ 0"

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
solve :: (α ~ Re) => Expr (γ, α) α -> (α, Expr γ α)
solve (Expr k0 xs) = (c', Expr k0 e)
  where (c', e) = solveAffine xs

solveAffine :: (α ~ Re)
            => [(Re, Available Re (γ, α))] -> (α, [(Re, Available Re γ)])
solveAffine ([]) = (0, [])
solveAffine ((c, Here) : xs) = (c + c', e)
  where (c', e) = solveAffine xs
solveAffine ((c, There x) : xs) = (c', (c, x) : e)
  where (c', e) = solveAffine xs 

-- FIXME: detect always true and always false cases.
solve' :: Cond (γ, Re) -> Solution γ Re
solve' c0 = case c0 of
  IsZero _ -> (EQ, (-1 / c) *^ e)
  IsNegative _ -> if c < 0 then (GT, (1 / (-c)) *^ e) else (LT, (1 / c) *^ e)
  where (c, e) = solve (condExpr c0)
  
shallower :: SomeVar γ -> SomeVar γ -> Bool
SomeVar Here `shallower` _ = False
SomeVar (There _) `shallower` SomeVar Here = True
SomeVar (There x) `shallower` SomeVar (There y) = SomeVar x `shallower` SomeVar y

data SomeVar γ where
  SomeVar :: Available v γ -> SomeVar γ

minVar :: SomeVar γ -> SomeVar γ -> SomeVar γ
minVar (SomeVar Here) _ = SomeVar Here
minVar _ (SomeVar Here)  = SomeVar Here 
minVar (SomeVar (There x)) (SomeVar (There y))
  = case minVar (SomeVar x) (SomeVar y) of
      SomeVar z -> SomeVar (There z)

deepest :: Cond γ -> SomeVar γ
deepest c = case condExpr c of
   (Expr _ e) -> foldr1 minVar . map SomeVar . map snd $ e

travExpr :: Applicative f => (forall v. Available v γ -> f (Available v δ)) -> Expr γ t -> f (Expr δ t)
travExpr f (Expr k0 xs) = Expr k0 <$> (traverse (\(k, e) -> (k,) <$> f e) xs)

occurExpr :: Expr (γ, x) t -> Maybe (Expr γ t)
occurExpr = travExpr $ \case
  Here -> Nothing
  There x -> Just x

integrate :: d ~ Re => Domain γ d -> P (γ, d) -> P γ
integrate d (Cond c@(IsNegative c') e) = case occurExpr c' of
  Nothing -> integrate (restrictDomain c d) e
  Just c'' -> cond (IsNegative c'') (integrate d e)
integrate d (Cond (IsZero c') e) = case occurExpr c' of
  Nothing ->
    -- We apply the rule: ∫ f(x) δ(c x + k) dx = f(-k/c)   
    -- (The correct rule is: ∫ f(x) δ(c x + k) dx = (1/abs c) * f(-k/c)
    -- HOWEVER, due to the way we generate the equalities, my hunch is
    -- that we already take into account this coefficient. To be
    -- investigated.)
    domainToConditions x0 d $ substP (\Here -> x0) e   
    where (coef, expr) = solve c'
          x0 = (-1 / coef) *^ expr
  Just c'' -> cond (IsZero c'') (integrate d e)
integrate d e = Integrate d e

cond :: Cond γ -> P γ -> P γ
cond c (Cond c' e) = if (deepest c) `shallower` (deepest c')
                     then Cond c (Cond c' e)
                     else Cond c' (cond c e)
cond c (normalise -> e) = Cond c e

normalise :: P γ -> P γ
normalise = \case
  Cond c (normalise -> e) -> cond c e
  Integrate d (normalise -> e) -> integrate d e
  Ret x -> Ret x

-- Domain without restriction
full :: Domain γ x
full = Domain [] [] []


exampleInEq :: P ()
exampleInEq = Integrate full $
              Cond (IsNegative (Expr 7 [(-1, Here)])) $
              Ret $ Expr 10 [(1, Here)]

-- >>> exampleInEq
-- ∫𝟙(7.0 + -1.0 * x ≤ 0)*(10.0 + 1.0 * x)

-- >>> normalise exampleInEq
-- ∫{7.0≤x≤+∞}(10.0 + 1.0 * x)

exampleEq :: P ()
exampleEq = Integrate full $
            Cond (IsZero (Expr 7 [(-1,Here)])) $
            Ret $ Expr 10 [(1, Here)]

-- >>> exampleEq
-- ∫(7.0 + -1.0 * x ≐ 0)*(10.0 + 1.0 * x)

-- >>> normalise exampleEq
-- (17.0)

example :: P ()
example = Integrate full $ Integrate full $
          Cond (IsNegative (Expr 0 [(3, There Here), (2, Here)])) $
          Cond (IsNegative (Expr 2 [(1, There Here)])) $
          Ret $ Expr 1 []

-- >>> example
-- ∫∫𝟙(0.0 + 3.0 * x + 2.0 * y ≤ 0)*𝟙(2.0 + 1.0 * x ≤ 0)*(1.0)

-- >>> normalise example
-- ∫{-∞≤x≤2.0}∫{-∞≤y≤0.0 + 1.5 * x}(1.0)

example1 :: P ()
example1 = Integrate full $ Integrate full $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)])) $
           Ret $ Expr 1 []

-- >>> example1
-- ∫∫(4.0 + (1.0 * x) + (-1.0 * y) ≐ 0)*(1.0)

-- >>> normalise example1
-- ∫(1.0)

example2 :: P ()
example2 = Integrate full $
           Integrate (Domain [] [Expr 1 [(1, Here)]] []) $
           Cond (IsZero (Expr 4 [(2, There Here), (-1, Here)]) ) $
           Ret $ Expr 0 [(1, Here)]

-- >>> example2
-- ∫∫{1.0 + (1.0 * x)≤y≤+∞}(4.0 + (2.0 * x) + (-1.0 * y) ≐ 0)*(0.0 + (1.0 * y))

-- >>> normalise example2
-- ∫{-3.0≤x≤+∞}(4.0 + (2.0 * x))

example3 :: P ()
example3 = Integrate full $
           Integrate full $
           Cond (IsNegative (Expr 3 [(-1, Here)])) $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)]) ) $
           Ret $ Expr 0 [(1,Here)]

-- >>> example3
-- ∫∫𝟙(3.0 + (-1.0 * y) ≤ 0)*(4.0 + (1.0 * x) + (-1.0 * y) ≐ 0)*(0.0 + (1.0 * y))

-- >>> normalise example3
-- ∫{-1.0≤x≤+∞}(4.0 + (1.0 * x))
