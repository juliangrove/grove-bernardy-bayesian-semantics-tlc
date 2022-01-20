{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
{-# LANGUAGE ViewPatterns #-}

module Models.Optimizer where

import Data.List (intercalate, nub)
import Data.Ratio
import Algebra.Classes hiding (isZero)
import Prelude hiding (Num(..), Fractional(..), (^), product, sum)
import TLC.Terms hiding ((>>))
import Data.Map (Map)
import qualified Data.Map as M

type Rat = Rational

data Domain γ α = Domain { domainConditions :: [Cond (γ, α)]
                         , domainLoBounds, domainHiBounds :: [Expr γ α] }

isPositive :: Expr γ Rat -> Cond γ
isPositive e = isNegative ((-1) *< e)

isNegative :: Expr γ Rat -> Cond γ
isNegative e = IsNegative e

lessThan :: Expr γ Rat -> Expr γ Rat -> Cond γ
t `lessThan` u = isNegative (t + ((-1) *< u))

greaterThan :: Expr γ Rat -> Expr γ Rat -> Cond γ
t `greaterThan` u = u `lessThan` t

domainToConditions :: Expr γ Rat -> Domain γ Rat -> P γ α -> P γ α
domainToConditions e0 = \case
  Domain [] [] [] -> id
  Domain (c:cs) los his ->
    Cond (substCond (\Here -> e0) c) . domainToConditions e0 (Domain cs los his)
  Domain cs (e:los) his ->
    Cond (e `lessThan` e0) . domainToConditions e0 (Domain cs los his)
  Domain cs los (e:his) ->
    Cond (e0 `lessThan` e) . domainToConditions e0 (Domain cs los his)

data Available α γ where
  Here :: Available α (γ, α)
  There :: Available α γ -> Available α (γ, β)
deriving instance Eq (Available α γ)
deriving instance Ord (Available α γ)
deriving instance Show (Available α γ)

data Expr γ α = Expr α [(α, Available α γ)] deriving Eq
  -- Linear combination. List of coefficients and variables (α is a Ring).
  -- Example: u - v is represented by @Expr 0 [(1, u), (-1,v)]@.

type Mono γ a = Exponential (Map (Either (Available a γ) (Poly γ a)) Natural)
deriving instance Eq a => Eq (Mono γ a)
deriving instance Ord a => Ord (Mono γ a)

-- map each monomial to its coefficient
newtype Poly γ a = P (Map (Mono γ a) a) deriving (Additive,Group,AbelianAdditive,Ord,Eq)
deriving instance (Ord a,Ring a) => Module a (Poly γ a)

instance (Eq a, Ord a,Ring a) => Multiplicative (Poly γ a) where
  one = P (M.singleton one one)
  P p * P q = P (M.fromListWith (+) [(m1 * m2, coef1 * coef2) | (m1,coef1) <- M.toList p, (m2,coef2) <- M.toList q])

instance (Eq a, Ord a,Ring a) => Module (Poly γ a) (Poly γ a) where
  (*^) = (*)

instance (Eq a, Ord a,Ring a) => Ring (Poly γ a) where

same :: Eq α => [α] -> [α] -> Bool
same xs ys = and $ xs >>= \x -> ys >>= \y -> [x `elem` ys && y `elem` xs]


-- | Induced vector space structure over Expr γ α:

-- | Multiplication by a scalar (expresions are linear)
(*<) :: Ring α => α -> Expr γ α -> Expr γ α
c *< Expr k0 xs = Expr (c * k0) [ (c * c', v) | (c', v) <- xs ]

instance Additive α => Additive (Expr γ α) where
  (Expr c1 xs1) + (Expr c2 xs2) = Expr (c1 + c2) (xs1 ++ xs2)
  zero = Expr zero []

data Cond γ = IsNegative { condExpr :: (Expr γ Rat) }
              -- Meaning of this constructor: expression ≤ 0
              -- Example: u ≤ v is represented by @IsNegative [(1, u), (-1, v)]@
            | IsZero { condExpr :: (Expr γ Rat) }
              -- Meaning of this constructor: expression = 0
              -- Example: u = v is represented by @IsZero [(1, u), (-1, v)]@
   deriving (Eq)

-- | Restrict the bounds by moving the bounds. Also return conditions that
-- ensure that the bounds are in the right order.
restrictDomain :: α ~ Rat => Cond (γ, α) -> Domain γ α -> (Domain γ α, [Cond γ])
restrictDomain c (Domain cs los his) = case solve' c of -- version with solver
  (LT, e) -> (Domain cs los (e:his), [ lo `lessThan` e | lo <- los ]) 
  (GT, e) -> (Domain cs (e:los) his, [ e `lessThan` hi | hi <- his ])

data P γ α where
  Integrate :: d ~ Rat => Domain γ d -> P (γ, d) α -> P γ α
  Cond :: Cond γ -> P γ α -> P γ α
  Add :: P γ α -> P γ α -> P γ α
  Div :: P γ α -> P γ α -> P γ α -- Can this be replaced by "factor" ? No, because we do integration in these factors as well.
  Ret :: Poly γ α -> P γ α

multP :: P γ Rat -> P γ Rat -> P γ Rat
multP (Integrate d p1) (wkP -> p2) = Integrate d $ multP p1 p2
multP (Cond c p1) p2 = Cond c $ multP p1 p2
multP (Ret e) (Integrate d p) = Integrate d $ multP (wkP $ Ret e) p
multP (Ret e) (Cond c p) = Cond c $ multP (Ret e) p
multP (Ret e1) (Ret e2) = Ret $ e1 * e2
multP (Add p1 p1') p2 = Add (multP p1 p2) (multP p1' p2)
multP p1 (Add p2 p2') = Add (multP p1 p2) (multP p1 p2')
multP (Div p1 p1') (Div p2 p2') = Div (multP p1 p1') (multP p2 p2')
multP (Div p1 p1') p2 = Div (multP p1 p2) p1'
multP p1 (Div p2 p2') = Div (multP p1 p2) p2'
  
type Subst γ δ = forall α. Ring α => Available α γ -> Expr δ α

wkSubst :: Ring α => Subst γ δ -> Subst (γ, α) (δ, α)
wkSubst f = \case
  Here -> Expr zero [(one, Here)]
  There x -> Expr k0 [ (c, There y) | (c, y) <- xs ]
    where Expr k0 xs = f x

substExpr :: Subst γ δ -> forall α. Ring α => Expr γ α -> Expr δ α
substExpr f (Expr k0 e) = foldr (+) (Expr k0 []) [ c *< f x | (c, x) <- e ]


exprToPoly :: Ord α => (Eq α, Ring α) => Expr γ α -> Poly γ α
exprToPoly (Expr c xs) = constPoly c + sum [ monoPoly c' (varMono x) | (c', x) <- xs ] 

constPoly :: Ord α => α -> Poly γ α
constPoly k = monoPoly k one

monoPoly :: α -> Mono γ α -> Poly γ α
monoPoly c m = P (M.singleton m c)

varMono :: Available α γ -> Mono γ α
varMono v = Exponential $ M.singleton (Left v) one

varPoly :: Ring α => Available α γ -> Poly γ α
varPoly = monoPoly one . varMono 

exponential :: Ring α => Poly γ α -> Poly γ α
exponential p = monoPoly one (Exponential $ M.singleton (Right p) one) 

substElem :: Ord α => (Ring α, Eq α) => Subst γ δ -> (Either (Available α γ) (Poly γ α)) -> Poly δ α
substElem f (Left x) = exprToPoly (f x)
substElem f (Right p) = exponential (substPoly f p)

substMono :: (Ring α, Ord α) => Subst γ δ -> Mono γ α -> Poly δ α
substMono f (Exponential m) = product [ substElem f v ^+ e  | (v,e) <- M.assocs m] 

substPoly :: (Ring α, Ord α) => Subst γ δ -> Poly γ α -> Poly δ α
substPoly f (P p) = sum [ c *^ substMono f m | (m,c) <- M.assocs p]
   
substCond :: Subst γ δ -> Cond γ -> Cond δ
substCond f (IsNegative e) = IsNegative $ substExpr f e
substCond f (IsZero e) = IsZero $ substExpr f e

substDomain :: Ring α => Subst γ δ -> Domain γ α -> Domain δ α
substDomain f (Domain c lo hi) = Domain
                                 (substCond (wkSubst f) <$> c)
                                 (substExpr f <$> lo)
                                 (substExpr f <$> hi)

substP :: Subst γ δ -> P γ Rat -> P δ Rat
substP f p0 = case p0 of
  Ret e -> Ret (substPoly f e)
  Add (substP f -> p1) (substP f -> p2) -> Add p1 p2
  Div (substP f -> p1) (substP f -> p2) -> Div p1 p2
  Cond c p -> Cond (substCond f c) (substP f p)
  Integrate d p -> Integrate (substDomain f d) (substP (wkSubst f) p)

wkP :: P γ Rat -> P (γ, α) Rat
wkP = substP $ \i -> Expr zero [(one, There i)] 

type family Eval γ where
  Eval 'R = Rat
  Eval 'Unit = ()
  Eval (γ × α) = (Eval γ, Eval α)

type family RepOf γ where
  RepOf Rat = 'R
  RepOf () = 'Unit
  RepOf (γ, α) = (RepOf γ × RepOf α)

pattern NNVar :: Available (Eval α) (Eval γ) -> NF γ α
pattern NNVar i <- Neu (NeuVar (evalVar -> i))
pattern Equ x y = Neu (NeuApp (NeuApp (NeuCon (General EqRl)) x) y)
pattern EqVars :: 'R ∈ γ -> 'R ∈ γ -> NF γ 'R
pattern EqVars i j = Neu (NeuApp (NeuApp (NeuCon (General EqRl))
                                  (Neu (NeuVar i))) (Neu (NeuVar j)))
pattern Mults :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Mults x y = Neu (NeuApp (NeuApp (NeuCon (General Mult)) x) y)
pattern Adds :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Adds x y = Neu (NeuApp (NeuApp (NeuCon (General Addi)) x) y)
pattern MultsVar :: NF γ 'R -> 'R ∈ γ -> NF γ 'R
pattern MultsVar x j = Neu (NeuApp
                            (NeuApp (NeuCon (General Mult)) x) (Neu (NeuVar j)))
pattern InEqVars :: 'R ∈ γ -> 'R ∈ γ -> NF γ 'R
pattern InEqVars i j = Neu (NeuApp (NeuCon (General Indi))
                            (Neu (NeuApp (NeuApp (NeuCon (Special GTE))
                                          (Neu (NeuVar i)))
                                  (Neu (NeuVar j)))))
pattern InEq :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern InEq x y = Neu (NeuApp (NeuCon (General Indi))
                            (Neu (NeuApp (NeuApp (NeuCon (Special GTE))
                                          x)
                                  y)))
pattern Normal :: Rat -> Rat -> NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Normal x y f = Neu (NeuApp (NeuApp (NeuCon (General Nml))
                                    (NFPair (Neu (NeuCon (General (Incl x))))
                                     (Neu (NeuCon (General (Incl y)))))) f)
pattern Uniform :: Rat -> Rat -> NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Uniform x y f = Neu (NeuApp (NeuApp (NeuCon (General Uni))
                                     (NFPair (Neu (NeuCon (General (Incl x))))
                                      (Neu (NeuCon (General (Incl y)))))) f)
pattern Lesbegue :: NF γ ('R ⟶ 'R) -> NF γ 'R
pattern Lesbegue f = Neu (NeuApp (NeuCon (General Les)) f)
pattern Divide :: NF γ 'R -> NF γ 'R -> NF γ 'R
pattern Divide x y = Neu (NeuApp (NeuApp (NeuCon (General Divi)) x) y)
pattern NNCon :: forall (γ :: Type) (α :: Type).
                   () =>
                   (α ~ 'R) => Rational -> NF γ α
pattern NNCon x = Neu (NeuCon (General (Incl x)))

evalP :: NF 'Unit 'R -> P () Rat
evalP = evalP'

evalP' :: NF γ 'R -> P (Eval γ) Rat
evalP' = \case
  NNCon x -> Ret $ constPoly x
  Neu (NeuApp (NeuApp (NeuCon (General EqRl))
                 (Adds (NNVar i) (NNVar j))) (NNVar k))
    -> Cond (IsZero $ Expr 0 [(1, i), (1, j), (-1, k)]) $
       Ret $ one
  EqVars (evalVar -> i) (evalVar -> j) ->
    Cond (IsZero $ Expr 0 [(1, i), (-1, j)]) $ Ret $ one
  InEqVars (evalVar -> i) (evalVar -> j) ->    
    Cond (IsNegative $ Expr 0 [(-1, i), (1, j)]) $ Ret $ one
  Equ (NNVar i) (NNCon x) ->  Cond (IsZero $ Expr x [(-1, i)]) $ Ret $ one
  InEq (NNVar i) (NNCon x) ->  Cond (IsNegative $ Expr x [(-1, i)]) $ Ret $ one
  Adds (evalP' -> x) (evalP' -> y) -> Add x y
  Mults (evalP' -> x) (evalP' -> y) -> multP x y
  Normal μ σ f -> Integrate full $ multP
                  (Ret $ constPoly (1 / (σ * sqrt2pi)) * exponential (constPoly (-1/2) * (sqr ((1/σ) *^ (constPoly μ - varPoly Here)))))
                  (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
    where sqrt2pi = 250662827463 % 100000000000
  Uniform x y f -> Integrate (Domain [] [Expr x []] [Expr y []]) $ multP
                   (Ret $ constPoly (1 / (y - x)))
                   (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Lesbegue f -> Integrate (Domain [] [] []) $ multP
                   (Ret $ one)
                   (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Neu (NeuVar (evalVar -> i)) -> Ret $ monoPoly one $ varMono i
  Divide x y -> Div (evalP' x) (evalP' y)
  t -> error ("evalP': unknown input: " ++ (show . nf_to_λ) t)

sqr :: Multiplicative a => a -> a
sqr x = x * x
          
evalVar :: α ∈ γ -> Available (Eval α) (Eval γ)
evalVar = \case
  Get -> Here
  Weaken (evalVar -> i) -> There i

data ShowType = Maxima | Mathematica | LaTeX

type Vars γ  = forall v. Available v γ -> String

showExpr :: Vars γ -> Expr γ Rat -> String
showExpr v (Expr k0 xs) = intercalate " + " $
                          (if k0 /= 0 || xs == [] then (showR k0 :) else id) $
                          [ (if c /= 1 then parens else id) $
                            (if c /= 1 || xs == []
                             then showR c ++ " * "
                             else "") ++ v x | (c, x) <- xs ]

showExp :: Natural -> String -> String
showExp e
  | e == 1 = id
  | otherwise = (++ "^" ++ show e)
           
showElem :: Vars γ -> Either (Available v γ) (Poly γ Rat) -> ShowType -> String
showElem vs (Left v) _ = vs v
showElem vs (Right p) st
  = (case st of Maxima -> ("exp"<>) . parens; Mathematica -> ("Exp"<>) . brackets; LaTeX -> ("e^"<>) . braces)
    (showPoly vs p st)
showMono :: Rat -> Vars γ -> Mono γ Rat -> ShowType -> String
showMono coef vs (Exponential m) st = foldrAlt (binOp "*") "1" ([showR coef | coef /= 1] ++[showExp e (showElem vs m st)  | (m,e) <- M.toList m, e /= zero])
showPoly :: Vars γ -> Poly γ Rat -> ShowType -> String
showPoly v (P m) st = foldrAlt  (binOp " + ") "0" ([showMono coef v m st  | (m,coef) <- M.toList m, coef /= zero])

binOp op x y = x ++ op ++ y

showCond :: ShowType -> Vars γ -> Cond γ -> String
showCond t v c0 = case c0 of
  c@(IsNegative c') -> (case t of Mathematica -> "Boole"; Maxima -> "charfun") <> (brackets $ showExpr v c' <> " ≤ 0")
  c@(IsZero c') -> "DiracDelta" ++ (brackets $ showExpr v c')

parens :: String -> String
parens x = "(" ++ x ++ ")"

brackets :: String -> String
brackets x = "[" ++ x ++ "]"

braces :: String -> String
braces x = "{" ++ x ++ "}"

foldrAlt :: (p -> p -> p) -> p -> [p] -> p
foldrAlt _ k [] = k
foldrAlt f _ xs = foldr1 f xs

showBounds :: Vars γ -> Bool -> [Expr γ Rat] -> ShowType -> String
showBounds v lo (nub -> xs) = \case
  Maxima -> if lo
            then foldrAlt
                 (\x y -> "max(" ++ x ++ ", " ++ y ++ ")")
                 "-inf" $
                 map (showExpr v) xs
            else foldrAlt
                 (\x y -> "min(" ++ x ++ ", " ++ y ++ ")")
                 "inf" $
                 map (showExpr v) xs
  Mathematica -> if lo
                 then foldrAlt
                      (\x y -> "Max[" ++ x ++ ", " ++ y ++ "]")
                      "-Infinity" $
                      map (showExpr v) xs
                 else foldrAlt
                      (\x y -> "Min[" ++ x ++ ", " ++ y ++ "]")
                      "Infinity" $
                      map (showExpr v) xs
  LaTeX -> if lo
           then foldrAlt
                (\x y -> "Max[" ++ x ++ ", " ++ y ++ "]")
                "-\\infty" $
                map (showExpr v) xs
           else foldrAlt
                (\x y -> "Min[" ++ x ++ ", " ++ y ++ "]")
                "\\infty" $
                map (showExpr v) xs

when :: [a] -> [Char] -> [Char]
when [] _ = ""
when _ x = x


(+!) :: String -> Vars γ -> Vars (γ, d)
f +! v = \case Here -> f
               There i -> v i

showP :: [String] -> Vars γ -> P γ Rat -> ShowType -> String
showP freshes@(f:fs) v = \case
  Ret e -> parens . showPoly v e
  Add p1 p2 -> \st -> "(" ++ showP freshes v p1 st ++ ") + (" ++
                      showP freshes v p2 st ++ ")"
  Div p1 p2 -> \st -> case st of
                        LaTeX -> "\\frac{" ++ showP freshes v p1 LaTeX ++
                                 "}{" ++ showP freshes v p2 LaTeX ++ "}"
                        _ -> "(" ++ showP freshes v p1 st ++ ") / (" ++
                             showP freshes v p2 st ++ ")"
  Integrate (Domain cs los his) e ->
    \st -> case st of
             LaTeX -> "\\int_{" ++ showBounds v True los LaTeX ++ "}^{" ++
                      showBounds v False his LaTeX ++ "}" ++
                      showP fs (f +! v) e LaTeX ++
                      "\\,d" ++ f 
             _ -> (\(integrand,dom) -> case st of
                              Maxima -> "integrate" ++ parens (integrand ++ ", " ++ dom)
                              Mathematica -> "Integrate" ++ brackets (integrand ++ ", " ++ braces dom)) $
                  (showP fs (f +! v) e st,
                  (when cs $ f ++ "∈" ++
                   braces (intercalate "∧" $ map (showCond st (f +! v))
                           cs)) ++ f ++ ", " ++
                  showBounds v True los st ++ ", " ++
                  showBounds v False his st)
  Cond c e -> \st -> showCond st v c ++ " * " ++ showP freshes v e st

showProg :: P () Rat -> ShowType -> String
showProg = showP freshes (\case)

printAs :: ShowType -> P γ Rat -> String
printAs = flip $ showP freshes (\case)

instance Show (P () Rat) where
  show = flip showProg Maxima

mathematica' :: [String] -> Vars γ -> P γ Rat -> IO ()
mathematica' fs vars = putStrLn . flip (showP fs vars) Mathematica

latex' :: [String] -> Vars γ -> P γ Rat -> IO ()
latex' fs vars = putStrLn . flip (showP fs vars) LaTeX

type Solution γ d = (Ordering, Expr γ d)

-- | @solve e x@ returns the coefficient of the 1st variable in the expression,
-- and the rest (terms not involving the 1st variable). I.e., c x + e = 0.
solve :: Expr (γ, Rat) Rat -> (Rat, Expr γ Rat)
solve (Expr k0 xs) = (c', Expr k0 e)
  where (c', e) = solveAffine xs

solveAffine :: [(Rat, Available Rat (γ, Rat))]
            -> (Rat, [(Rat, Available Rat γ)])
solveAffine ([]) = (0, [])
solveAffine ((c, Here) : xs) = (c + c', e)
  where (c', e) = solveAffine xs
solveAffine ((c, There x) : xs) = (c', (c, x) : e)
  where (c', e) = solveAffine xs 

-- FIXME: detect always true and always false cases.
solve' :: Cond (γ, Rat) -> Solution γ Rat
solve' c0 = case c0 of
  IsZero _ -> (EQ, (-1 / c) *< e)
  IsNegative _ -> if c < 0 then (GT, (1 / (-c)) *< e) else (LT, (-1 / c) *< e)
  where (c, e) = solve (condExpr c0)
  
shallower :: SomeVar γ -> SomeVar γ -> Bool
SomeVar Here `shallower` _ = False
SomeVar (There _) `shallower` SomeVar Here = True
SomeVar (There x) `shallower` SomeVar (There y)
  = SomeVar x `shallower` SomeVar y
NoVar `shallower` (SomeVar _) = True
(SomeVar _) `shallower` NoVar = True
_ `shallower` _ = False

data SomeVar γ where
  SomeVar :: Available v γ -> SomeVar γ
  NoVar :: SomeVar γ

minVar :: SomeVar γ -> SomeVar γ -> SomeVar γ
minVar (SomeVar Here) _ = SomeVar Here
minVar _ (SomeVar Here)  = SomeVar Here 
minVar (SomeVar (There x)) (SomeVar (There y))
  = case minVar (SomeVar x) (SomeVar y) of
      SomeVar z -> SomeVar (There z)
minVar NoVar y = y
minVar x NoVar = x

deepest :: Cond γ -> SomeVar γ
deepest c = case condExpr c of
   (Expr _ e) -> case e of
                   (_:_) -> foldr1 minVar . map SomeVar . map snd $ e
                   [] -> NoVar

travExpr :: Applicative f =>
            (forall v. Available v γ -> f (Available v δ)) ->
            Expr γ t -> f (Expr δ t)
travExpr f (Expr k0 xs) = Expr k0 <$> (traverse (\(k, e) -> (k,) <$> f e) xs)

occurExpr :: Expr (γ, x) t -> Maybe (Expr γ t)
occurExpr = travExpr $ \case
  Here -> Nothing
  There x -> Just x

isZero :: (Ring α, Eq α) => Poly γ α -> Bool
isZero (P p) = all (== zero) (M.elems p) 

integrate :: d ~ Rat => Domain γ d -> P (γ, d) Rat -> P γ Rat
integrate _ (Ret z) | isZero z = Ret $ zero
integrate d (Cond c@(IsNegative c') e) = case occurExpr c' of
  Nothing -> foldr cond (integrate d' e) cs
    where (d', cs) = restrictDomain c d
  Just c'' -> cond (IsNegative c'') (integrate d e)
integrate d (Cond (IsZero c') e) = case occurExpr c' of
  Nothing ->
    -- We apply the rule: ∫ f(x) δ(c x + k) dx = f(-k/c)   
    -- (The correct rule is: ∫ f(x) δ(c x + k) dx = (1/abs c) * f(-k/c)
    -- HOWEVER, due to the way we generate the equalities, my hunch is
    -- that we already take into account this coefficient. To be
    -- investigated.)
    domainToConditions x0 d $ substP (\i -> case i of { Here -> x0;
                                                        There i
                                                        -> Expr zero [(one, i)] }) e
    where (coef, expr) = solve c'
          x0 = (-1 / coef) *< expr
  Just c'' -> cond (IsZero c'') (integrate d e)
integrate d (Add e e') = Add (integrate d e) (integrate d e')
integrate d e = Integrate d e

adding :: P γ Rat -> P γ Rat -> P γ Rat
adding (Ret z) x | isZero z = x
adding x (Ret z) | isZero z = x
adding x y = Add x y

cond :: Cond γ -> P γ Rat -> P γ Rat
cond _ (Ret z) | isZero z = Ret $ zero
cond c (Cond c' e) | c == c' = cond c e
cond c (Cond c' e) = if (deepest c) `shallower` (deepest c')
                     then Cond c (Cond c' e)
                     else Cond c' (cond c e)
cond c (normalise -> e) = Cond c e

normalise :: P γ Rat -> P γ Rat
normalise = \case
  Cond c (normalise -> e) -> cond c e
  Integrate d (normalise -> e) -> integrate d e
  Add (normalise -> p1) (normalise -> p2) -> adding p1 p2
  Div (normalise -> p1) (normalise -> p2) -> divide p1 p2
  Ret e -> Ret e

divide :: P γ Rat -> P γ Rat -> P γ Rat
divide (Ret z) _ | isZero z = Ret $ zero
divide (Cond c n) d = Cond c (divide n d) -- this exposes conditions to the integrate function.
divide p1 p2 = Div p1 p2

-- | Take typed descriptions of real numbers onto Maxima programs. 
maxima :: (γ ⊢ 'R) -> P (Eval γ) Rat
maxima = normalise . evalP' . normalForm . clean . evalβ

-- maximaPrint :: 'Unit?m

-- | Take typed descriptions of real numbers onto Mathematica programs.
mathematica :: 'Unit ⊢ 'R -> IO ()
mathematica = mathematica' freshes (\case) . maxima

-- | Take typed descriptions of real numbers onto Mathematica programs.
mathematicaFun :: 'Unit ⊢ ('R ⟶ 'R) -> IO ()
mathematicaFun = mathematica' fs (\case Here -> f; There _ -> error "mathematicaFun: are you trying to access the end of context? (Unit)") . maxima . absInversion
  where (f:fs) = freshes

latexFun :: 'Unit ⊢ ('R ⟶ 'R) -> IO ()
latexFun = latex' fs (\case Here -> f; There _ -> error "latexFun: are you trying to access the end of context? (Unit)") . maxima . absInversion
  where (f:fs) = freshes

mathematicaFun' :: 'Unit ⊢ ('R ⟶ ('R ⟶ 'R)) -> IO ()
mathematicaFun' = mathematica' fs (\case Here -> f; There Here -> f'; There (There _) -> error "mathematicaFun: are you trying to access the end of context? (Unit)") . maxima . absInversion . absInversion
  where (f:f':fs) = freshes

-- >>> :t absInversion
-- absInversion :: (γ ⊢ ('R ⟶ 'R)) -> (γ × 'R) ⊢ 'R

-- Domain without restriction
full :: Domain γ x
full = Domain [] [] []

exampleInEq :: P () Rat
exampleInEq = Integrate full $
              Cond (IsNegative (Expr 7 [(-1, Here)])) $
              Ret $ constPoly 10 + varPoly Here

-- >>> exampleInEq
-- integrate(charfun[7 + (-1 * x) ≤ 0] * 10 + x, x, -inf, inf)

-- >>> normalise exampleInEq
-- integrate(10 + x, x, 7, inf)

exampleEq :: P () Rat
exampleEq = Integrate full $
            Cond (IsZero (Expr 7 [(-1, Here)])) $
            Ret $ constPoly 10 + varPoly Here

-- >>> exampleEq
-- integrate(DiracDelta[7 + (-1 * x)] * 10 + x, x, -inf, inf)

-- >>> normalise exampleEq
-- 17

example :: P () Rat
example = Integrate full $ Integrate full $
          Cond (IsNegative (Expr 0 [(3, There Here), (2, Here)])) $
          Cond (IsNegative (Expr 2 [(1, There Here)])) $
          Ret $ one

-- >>> example
-- integrate(integrate(charfun[(3 * x) + (2 * y) ≤ 0] * charfun[2 + x ≤ 0] * 1, y, -inf, inf), x, -inf, inf)

-- >>> normalise example
-- integrate(integrate(1, y, -inf, ((-3 / 2) * x)), x, -inf, -2)

example1 :: P () Rat
example1 = Integrate full $ Integrate full $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)])) $
           Ret $ one

-- >>> example1
-- integrate(integrate(DiracDelta[4 + x + (-1 * y)] * 1, y, -inf, inf), x, -inf, inf)

-- >>> normalise example1
-- integrate((1), x, -inf, inf)

example2 :: P () Rat
example2 = Integrate full $
           Integrate (Domain [] [Expr 1 [(1, Here)]] []) $
           Cond (IsZero (Expr 4 [(2, There Here), (-1, Here)]) ) $
           Ret $ varPoly Here

-- >>> example2
-- integrate(integrate(DiracDelta[4 + (2 * x) + (-1 * y)] * y, y, 1 + x, inf), x, -inf, inf)

-- >>> normalise example2
-- integrate(4 + 2*x, x, -3, inf)

example3 :: P () Rat
example3 = Integrate full $
           Integrate full $
           Cond (IsNegative (Expr 3 [(-1, Here)])) $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)])) $
           Ret $ constPoly 2 + sqr (varPoly Here) + (2::Rat) *^ (varPoly (There Here))

-- >>> example3
-- integrate(integrate(charfun[3 + (-1 * y) ≤ 0] * DiracDelta[4 + x + (-1 * y)] * 2 + y^2 + 2*x, y, -inf, inf), x, -inf, inf)

-- >>> normalise example3
-- integrate(18 + 10*x + x^2, x, -1, inf)

example4 :: P () Rat
example4 = Integrate full $
           Integrate full $
           Cond (IsNegative (Expr 3 [(-1, Here)])) $
           Cond (IsZero (Expr 0 [(1, (There Here)), (-1, Here)])) $
           Ret $ exponential $ varPoly Here + varPoly (There Here)
