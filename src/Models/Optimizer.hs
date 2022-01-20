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

import Data.List
import Data.Ratio
import Data.String.Utils
import TLC.Terms hiding ((>>))


type Rat = Rational

data Domain γ α = Domain { domainConditions :: [Cond (γ, α)]
                         , domainLoBounds, domainHiBounds :: [Expr γ α] }

isPositive :: Expr γ Rat -> Cond γ
isPositive e = isNegative ((-1) *^ e)

isNegative :: Expr γ Rat -> Cond γ
isNegative e = IsNegative e

lessThan :: Expr γ Rat -> Expr γ Rat -> Cond γ
t `lessThan` u = isNegative (t `add` ((-1) *^ u))

greaterThan :: Expr γ Rat -> Expr γ Rat -> Cond γ
t `greaterThan` u = u `lessThan` t

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
deriving instance Show (Available α γ)

data Expr γ α = Expr α [(α, Available α γ)] deriving Eq
  -- Linear combination. List of coefficients and variables (α is a vector
  -- space).
  -- Example u - v is represented by @Expr 0 [(1, u), (-1,v)]@.

data Monomial γ α = Mono { monoCoef :: α,
                           monoVars :: [(Available α γ, α)],
                           monoExponential :: Polynomial γ α }
  -- E.g., @Mono c [(x, c1), (y, c2)] p@ represents c * x^c1 * y^c2 * exp(p).

same :: Eq α => [α] -> [α] -> Bool
same xs ys = and $ xs >>= \x -> ys >>= \y -> [x `elem` ys && y `elem` xs]

instance Eq α => Eq (Monomial γ α) where
  Mono c vs e == Mono c' vs' e' = c == c' && vs `same` vs' && e == e'

data Polynomial γ α = Poly α [Monomial γ α]

instance Eq α => Eq (Polynomial γ α) where
  Poly c ms == Poly c' ms' = c == c' && ms `same` ms'

type Returned γ α = Polynomial γ α

multConst :: Num α => α -> Polynomial γ α -> Polynomial γ α
multConst c (Poly c1 cs)
  = case cs of
      [] -> Poly (c * c1) []
      Mono c' xs e : cs' -> case multConst c (Poly c1 cs') of
                              Poly c1' cs'' ->
                                Poly c1' ((Mono (c * c') xs e) : cs'')

compactMons :: (Num α, Eq α) => [Monomial γ α] -> [Monomial γ α]
compactMons = \case
  [] -> []
  m@(Mono c xs e) : (compactMons -> ms) ->
    if (xs, e) `elem` (map (\(Mono _ xs' e') -> (xs', e')) ms)
    then [ Mono (c + c') xs' e'
         | Mono c' xs' e' <- ms, xs' `same` xs, e' == e' ] ++
         filter (\(Mono _ xs' e') -> not (xs' `same` xs) || e' /= e) ms
    else Mono c xs e : ms

compactVars :: (Num α, Eq α) => [(Available α γ, α)] -> [(Available α γ, α)]
compactVars = \case
  [] -> []
  (x, c) : (compactVars -> xs) -> if x `elem` map fst xs
                                  then [ (y, c' + c) | (y, c') <- xs, y == x ]
                                       ++ filter (\(y, _) -> y /= x) xs
                                  else (x, c) : xs
                                
multComp :: (Num α, Eq α) => Polynomial γ α -> Monomial γ α -> [Monomial γ α]
multComp (Poly c1 cs) m@(Mono c xs e)
  = case cs of
      [] -> [Mono (c1 * c) xs e]
      Mono c' xs' e' : cs' ->
        Mono (c * c') (compactVars $ xs ++ xs') (e `addPoly` e') :
        multComp (Poly c1 cs') m

multPoly :: (Num α, Eq α) => Polynomial γ α -> Polynomial γ α -> Polynomial γ α
multPoly (Poly c1 cs1) p2
  = case multConst c1 p2 of
      Poly c2' cs2' -> Poly c2' $ filter (\(Mono c _ _) -> c /= 0) $
                       cs2' ++ (concat $ map (multComp p2) cs1)

expPoly :: (Num α, Eq α) => α -> Polynomial γ α -> Polynomial γ α
expPoly 1 e = e
expPoly n e = multPoly e (expPoly (n - 1) e)

-- | Induced vector space structure over Expr γ α:

-- | Multiplication by a scalar (expresions are linear)
(*^) :: Num α => α -> Expr γ α -> Expr γ α
c *^ Expr k0 xs = Expr (c * k0) [ (c * c', v) | (c', v) <- xs ]

-- | Addition
add :: Num α => Expr γ α -> Expr γ α -> Expr γ α
add (Expr c1 xs1) (Expr c2 xs2) = Expr (c1 + c2) (xs1 ++ xs2)

addPoly :: (Num α, Eq α) => Polynomial γ α -> Polynomial γ α -> Polynomial γ α
addPoly (Poly c1 cs1) (Poly c2 cs2) = Poly (c1 + c2) $ compactMons $ cs1 ++ cs2

zero = Expr 0 []

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
  Ret :: Returned γ α -> P γ α

multP :: P γ Rat -> P γ Rat -> P γ Rat
multP (Integrate d p1) (wkP -> p2) = Integrate d $ multP p1 p2
multP (Cond c p1) p2 = Cond c $ multP p1 p2
multP (Ret e) (Integrate d p) = Integrate d $ multP (wkP $ Ret e) p
multP (Ret e) (Cond c p) = Cond c $ multP (Ret e) p
multP (Ret e1) (Ret e2) = Ret $ multPoly e1 e2
multP (Add p1 p1') p2 = Add (multP p1 p2) (multP p1' p2)
multP p1 (Add p2 p2') = Add (multP p1 p2) (multP p1 p2')
multP (Div p1 p1') (Div p2 p2') = Div (multP p1 p1') (multP p2 p2')
multP (Div p1 p1') p2 = Div (multP p1 p2) p1'
multP p1 (Div p2 p2') = Div (multP p1 p2) p2'
  
type Subst γ δ = forall α. Num α => Available α γ -> Expr δ α

wkSubst :: Subst γ δ -> Subst (γ, α) (δ, α)
wkSubst f = \case
  Here -> Expr 0 [(1, Here)]
  There x -> Expr k0 [ (c, There y) | (c, y) <- xs ]
    where Expr k0 xs = f x

substExpr :: Subst γ δ -> forall α. Num α => Expr γ α -> Expr δ α
substExpr f (Expr k0 e) = foldr add (Expr k0 []) [ c *^ f x | (c, x) <- e ]

exprToPoly :: Num α => Expr γ α -> Polynomial γ α
exprToPoly (Expr c xs)
  = Poly c [ (Mono c' [(x, 1)] zeroPoly) | (c', x) <- xs ] 

exponential :: Num α => Polynomial γ α -> Polynomial γ α
exponential p = Poly 0 [Mono 1 [] p]

substMono :: (Num α, Eq α) => Subst γ δ -> Monomial γ α -> Polynomial δ α
substMono f (Mono c xs e) = multConst c
                            (foldr multPoly onePoly
                                   [ expPoly c' (exprToPoly (f x))
                                   | (x, c') <- xs ])
                            `multPoly` exponential (substPoly f e)

substPoly :: (Num α, Eq α) => Subst γ δ -> Polynomial γ α -> Polynomial δ α
substPoly f (Poly k0 cs) = foldr addPoly (Poly k0 []) (map (substMono f) cs)
   
substCond :: Subst γ δ -> Cond γ -> Cond δ
substCond f (IsNegative e) = IsNegative $ substExpr f e
substCond f (IsZero e) = IsZero $ substExpr f e

substDomain :: Num α => Subst γ δ -> Domain γ α -> Domain δ α
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
wkP = substP $ \i -> Expr 0 [(1, There i)] 

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
pattern NNCon x = Neu (NeuCon (General (Incl x)))

evalP :: NF 'Unit 'R -> P () Rat
evalP = evalP'

zeroPoly :: Num α => Polynomial γ α
zeroPoly = Poly 0 []

onePoly :: Num α => Polynomial γ α
onePoly = Poly 1 []

evalP' :: NF γ 'R -> P (Eval γ) Rat
evalP' = \case
  NNCon x -> Ret $ Poly x []
  Neu (NeuApp (NeuApp (NeuCon (General EqRl))
                 (Adds (NNVar i) (NNVar j))) (NNVar k))
    -> Cond (IsZero $ Expr 0 [(1, i), (1, j), (-1, k)]) $
       Ret $ Poly 1 []
  EqVars (evalVar -> i) (evalVar -> j) ->
    Cond (IsZero $ Expr 0 [(1, i), (-1, j)]) $ Ret $ Poly 1 []
  InEqVars (evalVar -> i) (evalVar -> j) ->    
    Cond (IsNegative $ Expr 0 [(-1, i), (1, j)]) $ Ret $ Poly 1 []
  InEq (NNVar i) (NNCon x) ->  Cond (IsNegative $ Expr x [(-1, i)]) $ Ret $ Poly 1 []
  Adds (evalP' -> x) (evalP' -> y) -> Add x y
  Mults (evalP' -> x) (evalP' -> y) -> multP x y
  Normal x y f -> Integrate full $ multP
                  (Ret $ 
                   Poly 0 [Mono (1 / (y * sqrt2pi)) []
                            (Poly (-(sqr x) / (2 * sqr y))
                            [Mono (-1 / (2 * sqr y)) [(Here, 2)] zeroPoly,
                             Mono (x / sqr y) [(Here, 1)] zeroPoly])])
                  (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
    where sqr x = x * x
          sqrt2pi = 250662827463 % 100000000000
  Uniform x y f -> Integrate (Domain [] [Expr x []] [Expr y []]) $ multP
                   (Ret $ 
                    Poly (1 / (y - x)) [])
                   (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Lesbegue f -> Integrate (Domain [] [] []) $ multP
                   (Ret $ 
                    Poly 1 [])
                   (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
  Neu (NeuVar (evalVar -> i)) -> Ret $ Poly 0 [Mono 1 [(i,1)] zeroPoly]
  Divide x y -> Div (evalP' x) (evalP' y)

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

showPoly :: Vars γ -> Polynomial γ Rat -> ShowType -> String
showPoly v (Poly k0 cs) = \case
  Maxima -> parens $ intercalate " + " $
            (if k0 /= 0 || cs == [] then (showR k0 :) else id) $
            filter (/= "")
            [ case c of
                0 -> ""
                _ -> parens $ intercalate " * " $ 
                     (if c /= 1 then (showR c :) else id) 
                     [ v x ++ (case c' of
                                 1 -> ""
                                 _ -> "^" ++ showR c') | (x, c') <- xs ]
                     ++ [ "exp(" ++ showPoly v e Maxima ++")" | not (isZero e) ]
            | Mono c xs e <- cs ]
  Mathematica -> parens $ intercalate " + " $
                 (if k0 /= 0 || cs == [] then (showR k0 :) else id) $
                 filter (/= "")
                 [ case c of
                     0 -> ""
                     _ -> parens $ intercalate " * " $ 
                          (if c /= 1 then (showR c :) else id) 
                          [ v x ++ (case c' of
                                      1 -> ""
                                      _ -> "^" ++ showR c') | (x, c') <- xs ]
                          ++ [ "Exp[" ++ showPoly v e Maxima ++"]"
                             | not (isZero e) ]
                 | Mono c xs e <- cs ]
  LaTeX -> parens $ intercalate " + " $
           (if k0 /= 0 || cs == [] then (showR k0 :) else id) $
           filter (/= "")
           [ case c of
               0 -> ""
               _ -> parens $ intercalate " * " $ 
                    (if c /= 1 then (showR c :) else id) 
                    [ v x ++ (case c' of
                                1 -> ""
                                _ -> "^" ++ showR c') | (x, c') <- xs ]
                    ++ [ "e^{" ++ showPoly v e LaTeX ++"}" | not (isZero e) ]
           | Mono c xs e <- cs ]

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
showBounds _ lo [] = \case
  Maxima -> (if lo then "-" else "") <> "inf"
  Mathematica -> (if lo then "-" else "") <> "Infinity"
  LaTeX -> (if lo then "-" else "") <> "\\infty"
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
  Ret e -> showPoly v e
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
  IsZero _ -> (EQ, (-1 / c) *^ e)
  IsNegative _ -> if c < 0 then (GT, (1 / (-c)) *^ e) else (LT, (-1 / c) *^ e)
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
                   (e':es) -> foldr1 minVar . map SomeVar . map snd $ e
                   [] -> NoVar

travExpr :: Applicative f =>
            (forall v. Available v γ -> f (Available v δ)) ->
            Expr γ t -> f (Expr δ t)
travExpr f (Expr k0 xs) = Expr k0 <$> (traverse (\(k, e) -> (k,) <$> f e) xs)

occurExpr :: Expr (γ, x) t -> Maybe (Expr γ t)
occurExpr = travExpr $ \case
  Here -> Nothing
  There x -> Just x

isZero :: (Num α, Eq α) => Polynomial γ α -> Bool
isZero (Poly 0 ms) = and [ c == 0 | Mono c _ _ <- ms ]
isZero _ = False

integrate :: d ~ Rat => Domain γ d -> P (γ, d) Rat -> P γ Rat
integrate _ (Ret z) | isZero z = Ret $ zeroPoly
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
                                                        -> Expr 0 [(1, i)] }) e
    where (coef, expr) = solve c'
          x0 = (-1 / coef) *^ expr
  Just c'' -> cond (IsZero c'') (integrate d e)
integrate d (Add e e') = Add (integrate d e) (integrate d e')
integrate d e = Integrate d e

adding :: P γ Rat -> P γ Rat -> P γ Rat
adding (Ret z) x | isZero z = x
adding x (Ret z) | isZero z = x
adding x y = Add x y

cond :: Cond γ -> P γ Rat -> P γ Rat
cond _ (Ret z) | isZero z = Ret $ zeroPoly
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
divide (Ret z) _ | isZero z = Ret $ zeroPoly
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

mathematicaFun' :: 'Unit ⊢ ('R ⟶ ('R ⟶ R)) -> IO ()
mathematicaFun' = mathematica' fs (\case Here -> f; There Here -> f'; There (There _) -> error "mathematicaFun: are you trying to access the end of context? (Unit)") . maxima . absInversion . absInversion
  where (f:f':fs) = freshes

-- >>> :t absInversion
-- absInversion :: (γ ⊢ ('R ⟶ 'R)) -> (γ × 'R) ⊢ 'R

-- Domain without restriction
full :: Domain γ x
full = Domain [] [] []

var :: Available Rational γ -> Monomial γ Rational
var x = (Mono 1 [(x,1)] zeroPoly )

exampleInEq :: P () Rat
exampleInEq = Integrate full $
              Cond (IsNegative (Expr 7 [(-1, Here)])) $
              Ret $ Poly 10 [var Here]

-- >>> exampleInEq
-- integrate(charfun[7 + (-1 * x) ≤ 0] * (10 + (x)), x, -inf, inf)

-- >>> normalise exampleInEq
-- integrate((10 + (x)), x, 7, inf)

exampleEq :: P () Rat
exampleEq = Integrate full $
            Cond (IsZero (Expr 7 [(-1, Here)])) $
            Ret $ Poly 10 [var Here]

-- >>> exampleEq
-- integrate(DiracDelta[7 + (-1 * x)] * (10 + (x)), x, -inf, inf)

-- >>> normalise exampleEq
-- (10 + (7))

example :: P () Rat
example = Integrate full $ Integrate full $
          Cond (IsNegative (Expr 0 [(3, There Here), (2, Here)])) $
          Cond (IsNegative (Expr 2 [(1, There Here)])) $
          Ret $ Poly 1 []

-- >>> example
-- integrate(integrate(charfun[(3 * x) + (2 * y) ≤ 0] * charfun[2 + x ≤ 0] * (1), y, -inf, inf), x, -inf, inf)

-- >>> normalise example
-- integrate(integrate((1), y, -inf, ((-3 / 2) * x)), x, -inf, -2)

example1 :: P () Rat
example1 = Integrate full $ Integrate full $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)])) $
           Ret $ Poly 1 []

-- >>> example1
-- integrate(integrate(DiracDelta[4 + x + (-1 * y)] * (1), y, -inf, inf), x, -inf, inf)

-- >>> normalise example1
-- integrate((1), x, -inf, inf)

example2 :: P () Rat
example2 = Integrate full $
           Integrate (Domain [] [Expr 1 [(1, Here)]] []) $
           Cond (IsZero (Expr 4 [(2, There Here), (-1, Here)]) ) $
           Ret $ Poly 0 [var Here]

-- >>> example2
-- integrate(integrate(DiracDelta[4 + (2 * x) + (-1 * y)] * ((y)), y, 1 + x, inf), x, -inf, inf)

-- >>> normalise example2
-- integrate(((4) + (2 * x)), x, -3, inf)

example3 :: P () Rat
example3 = Integrate full $
           Integrate full $
           Cond (IsNegative (Expr 3 [(-1, Here)])) $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)])) $
           Ret $ Poly 2 $ compactMons [Mono 1 [(Here, 2), (There Here, 1)] zeroPoly, Mono 1 [(Here, 2), (There Here, 1)] zeroPoly]

-- >>> example3
-- integrate(integrate(Boole[3 + (-1 * y) ≤ 0] * DiracDelta[4 + x + (-1 * y)] * (2 + (2 * y^2 * x)), y, -inf, inf), x, -inf, inf)

-- >>> normalise example3
-- integrate((2 + (32 * x) + (16 * x^2) + (2 * x^3)), x, -1, inf)

example4 :: P () Rat
example4 = Integrate full $
           Integrate full $
           Cond (IsNegative (Expr 3 [(-1, Here)])) $
           Cond (IsZero (Expr 0 [(1, (There Here)), (-1, Here)])) $
           Ret $ Poly 0 [Mono 1 [] (Poly 0 [Mono 1 [(Here, 2)] zeroPoly,
                                            Mono 1 [(Here, 1)] zeroPoly])]

