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

import Control.Monad (ap)
import Data.List
import Data.Ratio
import Data.String.Utils
import TLC.Terms hiding ((>>))


-- >>> replace "%" "/" "2 % 2"
-- "2 / 2"

type Re = Rational

data Domain γ α = Domain { domainConditions :: [Cond (γ, α)]
                         , domainLoBounds, domainHiBounds :: [Expr γ α] }

isPositive :: Expr γ Re -> Cond γ
isPositive e = isNegative ((-1) *^ e)

isNegative :: Expr γ Re -> Cond γ
isNegative e = IsNegative e

lessThan :: Expr γ Re -> Expr γ Re -> Cond γ
t `lessThan` u = isNegative (t `add` ((-1) *^ u))

greaterThan :: Expr γ Re -> Expr γ Re -> Cond γ
greaterThan = flip lessThan

-- | @domainToConditions x₀ d@ creates the conditions corresponding to x₀ ∈ d.
domainToConditions :: Expr γ Re -> Domain γ Re -> P γ Re -> P γ Re
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

data Expr γ α = Expr α [(α, Available α γ)]
  -- Linear combination. List of coefficients and variables (α is a vector
  -- space).
  -- Example u - v is represented by @Expr 0 [(1, u), (-1,v)]@.

type Component γ α = (α, [(Available α γ, α)])
  -- E.g., @(c1, [(x, c2), (y, c3)])@ represents c1 * x^c2 * y^c3.

type Exponentiated γ α = (α, Returned γ α)
  -- E.g., @(c1, p)@ represents c1 * exp(p).

data Polynomial γ α = Poly α [Component γ α] deriving Eq
data Exponentials γ α = Exps α [Exponentiated γ α] deriving Eq

data Returned γ α = RetPoly (Polynomial γ α)
                  | RetExps (Exponentials γ α)
                  | Plus (Polynomial γ α) (Exponentials γ α)
                  | Plus' (Returned γ α) (Returned γ α)
                  | Times (Polynomial γ α) (Exponentials γ α)
                  | Times' (Returned γ α) (Returned γ α)
                  -- @Poly c cs@ represents c + sum of cs.
                  -- @Exp c cs@ represents c + sum of cs.
                  -- @Plus x y@ represents x + y.
                  -- @Times x y@ represents x * y.
deriving instance Eq α => Eq (Returned γ α)

multConst :: Num α => α -> Polynomial γ α -> Polynomial γ α
multConst c (Poly c1 cs) = case cs of
                             [] -> Poly (c * c1) []
                             (c', xs) : cs' ->
                               case multConst c (Poly c1 cs') of
                                 Poly c1' cs'' -> Poly c1' ((c * c', xs) : cs'')
multComp :: Num α =>
            Polynomial γ α -> (α, [(Available α γ, α)]) ->
            [(α, [(Available α γ, α)])]           
multComp (Poly c1 cs) (c, xs) = case cs of
                                  [] -> [(c1 * c, xs)]
                                  (c', xs') : cs' ->
                                    (c' * c, xs' ++ xs) :
                                    multComp (Poly c1 cs') (c, xs)

multPoly :: (Num α, Eq α) => Polynomial γ α -> Polynomial γ α -> Polynomial γ α
multPoly (Poly c1 cs1) p2
  = case multConst c1 p2 of
      Poly c2' cs2' -> Poly c2' $ filter (\(c, _) -> c /= 0) $
                       cs2' ++ (concat $ map (multComp p2) cs1)

multReturned :: (Num α, Eq α) => Returned γ α -> Returned γ α -> Returned γ α
multReturned = \case
  RetPoly p@(Poly c1 cs1) -> \case
    RetPoly p2 -> RetPoly $ multPoly p p2  
    RetExps e -> Times p e
    e@(Plus _ _) -> Times' (RetPoly p) e
    Times (multReturned (RetPoly p) . RetPoly -> RetPoly p') e -> Times p' e
    e@(Plus' _ _) -> Times' (RetPoly p) e
    e@(Times' _ _) -> Times' (RetPoly p) e
  RetExps e@(Exps c1 es1) -> \case
    RetPoly p -> Times p e
    RetExps (Exps c2 es2) -> RetExps $ Exps (c1 * c2) $
      ((\(x, e1) -> (c2 * x, e1)) <$> es1) ++
      ((\(y, e2) -> (c1 * y, e2)) <$> es2) ++
      ((\(x, e1) (y, e2) -> (x * y, e1 `addReturned` e2)) <$> es1 <*> es2)
    e'@(Plus _ _) -> Times' (RetExps e) e'
    Times p (multReturned (RetExps e) . RetExps -> RetExps e') -> Times p e'
    e'@(Plus' _ _) -> Times' (RetExps e) e'
    e'@(Times' _ _) -> Times' (RetExps e) e'
  Times p e -> \case
    RetPoly p' -> multReturned (RetPoly p') (Times p e)
    RetExps e' -> multReturned (RetExps e') (Times p e)
    e'@(Plus _ _) -> Times' (Times p e) e'
    Times
      (multReturned (RetPoly p) . RetPoly -> RetPoly p')
      (multReturned (RetExps e) . RetExps -> RetExps e') -> Times p' e'
    e'@(Plus' _ _) -> Times' (Times p e) e'
    e'@(Times' _ _) -> Times' (Times p e) e'
  e@(Plus' _ _) -> \e' -> Times' e e'
  e@(Times' _ _) -> \e' -> Times' e e'

expReturned :: (Num α, Eq α) => α -> Returned γ α -> Returned γ α
expReturned 1 e = e
expReturned n e = multReturned e (expReturned (n - 1) e)

-- | Induced vector space structure over Expr γ α:

-- | Multiplication by a scalar (expresions are linear)
(*^) :: Num α => α -> Expr γ α -> Expr γ α
c *^ Expr k0 xs = Expr (c * k0) [ (c * c', v) | (c', v) <- xs ]

(**^) :: (Num α, Eq α) => α -> Returned γ α -> Returned γ α
c **^ e = multReturned (RetPoly $ Poly c []) e
  
-- | Addition
add :: Num α => Expr γ α -> Expr γ α -> Expr γ α
add (Expr a xs) (Expr a' xs') = Expr (a + a') (xs ++ xs')

addReturned :: Num α => Returned γ α -> Returned γ α -> Returned γ α
addReturned = \case
  RetPoly p@(Poly c1 cs1) -> \case
    RetPoly (Poly c2 cs2) -> RetPoly $ Poly (c1 + c2) $ cs1 ++ cs2
    RetExps e -> Plus p e
    Plus (addReturned (RetPoly p) . RetPoly -> RetPoly p') e -> Plus p' e
    e@(Times _ _) -> Plus' (RetPoly p) e
    e@(Plus' _ _) -> Plus' (RetPoly p) e
    e@(Times' _ _) -> Plus' (RetPoly p) e
  RetExps e@(Exps c1 es1) -> \case
    RetPoly p -> Plus p e
    RetExps (Exps c2 es2) -> RetExps $ Exps (c1 + c2) $ es1 ++ es2
    Plus p (addReturned (RetExps e) . RetExps -> RetExps e') -> Plus p e'
    e'@(Times _ _) -> Plus' (RetExps e) e'
    e'@(Plus' _ _) -> Plus' (RetExps e) e'
    e'@(Times' _ _) -> Plus' (RetExps e) e'
  p1@(Plus p e) -> \case
    p2@(RetPoly _) -> addReturned p2 p1
    e@(RetExps _) -> addReturned e p1
    Plus
      (addReturned (RetPoly p) . RetPoly -> RetPoly p')
      (addReturned (RetExps e) . RetExps -> RetExps e') -> Plus p' e'
    e@(Times _ _) -> Plus' p1 e
    e@(Plus' _ _) -> Plus' p1 e
    e@(Times' _ _) -> Plus' p1 e
  e@(Times _ _) -> \e' -> Plus' e e'
  e@(Times' _ _) -> \e' -> Plus' e e'
  e@(Plus' _ _) -> \e' -> Plus' e e'

zero = Expr 0 []

data Cond γ = IsNegative { condExpr :: (Expr γ Re) }
              -- Meaning of this constructor: expression ≤ 0
              -- Example: u ≤ v is represented by @IsNegative [(1, u), (-1, v)]@
            | IsZero { condExpr :: (Expr γ Re) }
              -- Meaning of this constructor: expression = 0
              -- Example: u = v is represented by @IsZero [(1, u), (-1, v)]@

restrictDomain :: α ~ Re => Cond (γ, α) -> Domain γ α -> Domain γ α
  -- @restrictDomain c (Domain cs' lowBounds highBounds) = Domain (c : cs')
  -- lowBounds highBounds@                                  
  -- basic version
restrictDomain c (Domain cs los his) = case solve' c of -- version with solver
  (LT, e) -> Domain cs los (e:his) 
  (GT, e) -> Domain cs (e:los) (his)

data P γ α where
  Integrate :: (Re ~ d) => Domain γ d -> P (γ, d) α -> P γ α
  Cond :: Cond γ -> P γ α -> P γ α
  Add :: P γ α -> P γ α -> P γ α
  Div :: P γ α -> P γ α -> P γ α
  Ret :: Returned γ α -> P γ α

multP :: P γ Re -> P γ Re -> P γ Re
multP (Integrate d p1) (wkP -> p2) = Integrate d $ multP p1 p2
multP (Cond c p1) p2 = Cond c $ multP p1 p2
multP (Ret e) (Integrate d p) = Integrate d $ multP (wkP $ Ret e) p
multP (Ret e) (Cond c p) = Cond c $ multP (Ret e) p
multP (Ret e1) (Ret e2) = Ret $ multReturned e1 e2
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

exprToPoly :: Num α => Expr γ α -> Returned γ α
exprToPoly (Expr c xs) = RetPoly $ Poly c [ (c', [(x, 1)]) | (c', x) <- xs ] 

substReturned :: Subst γ δ ->
                 forall α. (Num α, Eq α) => Returned γ α -> Returned δ α
substReturned f = \case
  RetPoly (Poly k0 cs) -> foldr addReturned (RetPoly $ Poly k0 [])
                          [ c **^ (foldr multReturned (RetPoly $ Poly 1 [])
                                   [ expReturned c' $ exprToPoly (f x)
                                   | (x, c') <- xs ])
                          | (c, xs) <- cs ]
  RetExps (Exps k0 es) -> RetExps $ Exps k0 $
                          [ (c, substReturned f e) | (c, e) <- es ]
  Plus
    (substReturned f . RetPoly -> RetPoly p)
    (substReturned f . RetExps -> RetExps e) -> Plus p e
  Plus' (substReturned f -> p) (substReturned f -> e) -> Plus' p e
  Times
    (substReturned f . RetPoly -> RetPoly p)
    (substReturned f . RetExps -> RetExps e) -> Times p e
  Times' (substReturned f -> p) (substReturned f -> e) -> Times' p e
    
substCond :: Subst γ δ -> Cond γ -> Cond δ
substCond f (IsNegative e) = IsNegative $ substExpr f e
substCond f (IsZero e) = IsZero $ substExpr f e

substDomain :: Num d => Subst γ δ -> Domain γ d -> Domain δ d
substDomain f (Domain c lo hi) = Domain
                                 (substCond (wkSubst f) <$> c)
                                 (substExpr f <$> lo)
                                 (substExpr f <$> hi)

substP :: Subst γ δ -> P γ Re -> P δ Re
substP f p0 = case p0 of
  Ret e -> Ret (substReturned f e)
  Add (substP f -> p1) (substP f -> p2) -> Add p1 p2
  Div (substP f -> p1) (substP f -> p2) -> Div p1 p2
  Cond c p -> Cond (substCond f c) (substP f p)
  Integrate d p -> Integrate (substDomain f d) (substP (wkSubst f) p)

wkP :: P γ Re -> P (γ, α) Re
wkP = substP $ \i -> Expr 0 [(1, There i)] 

type family Eval γ where
  Eval R = Re
  Eval Unit = ()
  Eval (γ × α) = (Eval γ, Eval α)

type family RepOf γ where
  RepOf Re = R
  RepOf () = Unit
  RepOf (γ, α) = (RepOf γ × RepOf α)

pattern EqVars i j
  = Neu (NeuApp (NeuApp (NeuCon (General EqRl))
                 (Neu (NeuVar i))) (Neu (NeuVar j)))
pattern Mults x y
  = Neu (NeuApp (NeuApp (NeuCon (General Mult)) x) y)
pattern Adds x y
  = Neu (NeuApp (NeuApp (NeuCon (General Addi)) x) y)
pattern MultsVar x j
  = Neu (NeuApp (NeuApp (NeuCon (General Mult)) x) (Neu (NeuVar j)))
pattern InEqVars i j
  = Neu (NeuApp (NeuCon (General Indi))
         (Neu (NeuApp (NeuApp (NeuCon (Special GTE))
                       (Neu (NeuVar i)))
               (Neu (NeuVar j)))))
pattern Normal x y f
  = Neu (NeuApp (NeuApp (NeuCon (General Nml))
                 (NFPair (Neu (NeuCon (General (Incl x))))
                  (Neu (NeuCon (General (Incl y)))))) f)
pattern Uniform x y f
  = Neu (NeuApp (NeuApp (NeuCon (General Uni))
                 (NFPair (Neu (NeuCon (General (Incl x))))
                  (Neu (NeuCon (General (Incl y)))))) f)
pattern Divide x y
  = Neu (NeuApp (NeuApp (NeuCon (General Divi)) x) y)

evalP :: NF Unit R -> P () Re
evalP = evalP' where
  evalP' :: NF γ R -> P (Eval γ) Re
  evalP' = \case
    Neu (NeuCon (General (Incl x))) -> Ret $ RetPoly $ Poly x []
    EqVars (evalVar -> i) (evalVar -> j) ->
      Cond (IsZero $ Expr 0 [(1, i), (-1, j)]) $ Ret $ RetPoly $ Poly 1 []
    InEqVars (evalVar -> i) (evalVar -> j) ->    
      Cond (IsNegative $ Expr 0 [(-1, i), (1, j)]) $ Ret $ RetPoly $ Poly 1 []
    Adds (evalP' -> x) (evalP' -> y) -> Add x y
    Mults (evalP' -> x) (evalP' -> y) -> multP x y
    Normal x y f -> Integrate full $ multP
                    (Ret $ RetExps $
                     Exps 0 [(1 / (y * sqrt2pi),
                              RetPoly $ Poly (-(sqr x) / (2 * sqr y))
                              [(-1 / (2 * sqr y), [(Here, 2)]),
                               (x / sqr y, [(Here, 1)])])])
                    (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
      where sqr x = x * x
            sqrt2pi = 1
    Uniform x y f -> Integrate (Domain [] [Expr x []] [Expr y []]) $ multP
                     (Ret $ RetPoly $
                      Poly (1 / (y - x)) [])
                     (evalP' $ normalForm $ App (wkn $ nf_to_λ f) (Var Get))
    Neu (NeuVar (evalVar -> i)) -> Ret $ RetPoly $ Poly 0 [(1, [(i, 1)])]
    Divide x y -> Div (evalP' x) (evalP' y)
  evalVar :: α ∈ γ -> Available (Eval α) (Eval γ)
  evalVar = \case
    Get -> Here
    Weaken (evalVar -> i) -> There i

type Vars γ  = forall v. Available v γ -> String

showExpr :: (Show α, Num α, Eq α) => Vars γ -> Expr γ α -> String
showExpr v (Expr k0 xs) = intercalate " + " $
                          (if k0 /= 0 || xs == [] then [show k0] else []) ++
                          [ (if k /= 1 then parens else id) $
                            (if k /= 1 || xs == []
                                      then show k ++ " * "
                                      else "") ++
                            v x | (k, x) <- xs ]

showReturned :: (Show α, Num α, Eq α) => Vars γ -> Returned γ α -> String
showReturned v = \case
  RetPoly (Poly k0 cs) -> parens $ intercalate " + " $
                          (if k0 /= 0 || cs == [] then [show k0] else []) ++
                          filter (/= "")
                          [ case c of
                              0 -> ""
                              1 -> (if length xs > 1 then parens else id)
                                   (intercalate "*" $
                                           map (\(x, c') -> v x ++
                                                 case c' of
                                                   1 -> ""
                                                   _ -> "^" ++ show c')
                                          xs)
                              _ -> parens (show c ++ " * " ++ (intercalate "*" $
                                           map (\(x, c') -> v x ++
                                                 case c' of
                                                   1 -> ""
                                                   _ -> "^" ++ show c')
                                          xs)) | (c, xs) <- cs ]
  RetExps (Exps k0 es) -> parens $ intercalate " + " $
                          (if k0 /= 0 || es == [] then [show k0] else []) ++
                          filter (/= "")
                          [ case c of
                              0 -> ""
                              1 -> "exp" ++ showReturned v e
                              _ -> parens $
                                   show c ++ " * exp" ++
                                   showReturned v e | (c, e) <- es ]
  Plus p e -> case p of
                Poly 0 [] -> showReturned v (RetExps e)
                _ -> case e of
                       Exps 0 [] -> showReturned v (RetPoly p)
                       _ -> showReturned v (RetPoly p) ++ " + " ++
                            showReturned v (RetExps e)
  Times p e -> case p of
                 Poly 0 [] -> "0"
                 Poly 1 [] -> showReturned v (RetExps e)
                 _ -> case e of
                        Exps 0 [] -> "0"
                        Exps 1 [] -> showReturned v (RetPoly p)
                        _ -> showReturned v (RetPoly p) ++ " * " ++
                             showReturned v (RetExps e)
  Plus' p e -> "(" ++ showReturned v p ++ ") + (" ++ showReturned v e ++ ")"
  Times' p e -> "(" ++ showReturned v p ++ ") * (" ++ showReturned v e ++ ")"

mathematicaReturned :: (Show α, Num α, Eq α) => Vars γ -> Returned γ α -> String
mathematicaReturned v = \case
  RetPoly (Poly k0 cs) -> parens $ intercalate " + " $
                          (if k0 /= 0 || cs == [] then [show k0] else []) ++
                          filter (/= "")
                          [ case c of
                              0 -> ""
                              1 -> (if length xs > 1 then parens else id)
                                   (intercalate "*" $
                                           map (\(x, c') -> v x ++
                                                 case c' of
                                                   1 -> ""
                                                   _ -> "^" ++ show c')
                                          xs)
                              _ -> parens (show c ++ " * " ++ (intercalate "*" $
                                           map (\(x, c') -> v x ++
                                                 case c' of
                                                   1 -> ""
                                                   _ -> "^" ++ show c')
                                          xs)) | (c, xs) <- cs ]
  RetExps (Exps k0 es) -> parens $ intercalate " + " $
                          (if k0 /= 0 || es == [] then [show k0] else []) ++
                          filter (/= "")
                          [ case c of
                              0 -> ""
                              1 -> "exp" ++ mathematicaReturned v e
                              _ -> parens $
                                   show c ++ " * Exp" ++ (brackets $
                                   mathematicaReturned v e) | (c, e) <- es ]
  Plus p e -> case p of
                Poly 0 [] -> mathematicaReturned v (RetExps e)
                _ -> case e of
                       Exps 0 [] -> mathematicaReturned v (RetPoly p)
                       _ -> mathematicaReturned v (RetPoly p) ++ " + " ++
                            mathematicaReturned v (RetExps e)
  Times p e -> case p of
                 Poly 0 [] -> "0"
                 Poly 1 [] -> mathematicaReturned v (RetExps e)
                 _ -> case e of
                        Exps 0 [] -> "0"
                        Exps 1 [] -> mathematicaReturned v (RetPoly p)
                        _ -> mathematicaReturned v (RetPoly p) ++ " * " ++
                             mathematicaReturned v (RetExps e)
  Plus' p e -> "(" ++ mathematicaReturned v p ++ ") + (" ++
               mathematicaReturned v e ++ ")"
  Times' p e -> "(" ++ mathematicaReturned v p ++ ") * (" ++
                mathematicaReturned v e ++ ")"

showCond :: Vars γ -> Cond γ -> String
showCond v = \case
  c@(IsNegative c') -> "𝟙" <> (parens $ showExpr v c' <> " ≤ 0")
  c@(IsZero c') -> parens $ showExpr v c' ++ " ≐ 0"

parens :: String -> String
parens x = "(" ++ x ++ ")"

brackets :: String -> String
brackets x = "[" ++ x ++ "]"

braces :: String -> String
braces x = "{" ++ x ++ "}"

showBounds :: (Show α, Num α, Eq α) => Vars γ -> Bool -> [Expr γ α] -> String
showBounds _ lo [] = (if lo then "-" else "") <> "inf"
showBounds v lo xs = if lo
                     then foldr
                          (\x y -> "max(" ++ x ++ ", " ++ y ++ ")")
                          "-inf" $
                          map (showExpr v) xs
                     else foldr
                          (\x y -> "min(" ++ x ++ ", " ++ y ++ ")")
                          "inf" $
                          map (showExpr v) xs

mathematicaBounds :: (Show α, Num α, Eq α)
                  => Vars γ -> Bool -> [Expr γ α] -> String
mathematicaBounds _ lo [] = (if lo then "-" else "") <> "Infinity"
mathematicaBounds v lo xs = if lo
                            then foldr
                                 (\x y -> "Max[" ++ x ++ ", " ++ y ++ "]")
                                 "-Infinity" $
                                 map (showExpr v) xs
                            else foldr
                                 (\x y -> "Min[" ++ x ++ ", " ++ y ++ "]")
                                 "Infinity" $
                                 map (showExpr v) xs

when :: [a] -> [Char] -> [Char]
when [] _ = ""
when _ x = x

showP :: [String] -> Vars γ -> P γ Re -> String
showP freshes@(f:fs) v = \case
  Ret e -> showReturned v e
  Add p1 p2 -> "(" ++ showP freshes v p1 ++ ") + (" ++ showP freshes v p2 ++ ")"
  Div p1 p2 -> "(" ++ showP freshes v p1 ++ ") / (" ++ showP freshes v p2 ++ ")"
  Integrate (Domain cs los his) e -> ("integrate" ++) $ parens $
    showP fs (\case Here -> f; There i -> v i) e ++
    (when cs $ f ++ "∈" ++
     braces (intercalate "∧" $ map (showCond (\case Here -> f; There i -> v i))
             cs)) ++ ", " ++ f ++ (when (los ++ his)
                                   (", " ++ showBounds v True los ++
                                    ", " ++ showBounds v False his))
  Cond c e -> showCond v c ++ " * " ++ showP freshes v e

mathematicaP :: [String] -> Vars γ -> P γ Re -> String
mathematicaP freshes@(f:fs) v = \case
  Ret e -> showReturned v e
  Add p1 p2 -> "(" ++ mathematicaP freshes v p1 ++ ") + (" ++
               mathematicaP freshes v p2 ++ ")"
  Div p1 p2 -> "(" ++ mathematicaP freshes v p1 ++ ") / (" ++
               mathematicaP freshes v p2 ++ ")"
  Integrate (Domain cs los his) e -> ("Integrate" ++) $ brackets $
    mathematicaP fs (\case Here -> f; There i -> v i) e ++
    (when cs $ f ++ "∈" ++
     braces (intercalate "∧" $ map (showCond (\case Here -> f; There i -> v i))
             cs)) ++ ", " ++ (braces $ f ++ (when (los ++ his)
                                   (", " ++ mathematicaBounds v True los ++
                                    ", " ++ mathematicaBounds v False his)))
  Cond c e -> showCond v c ++ " * " ++ mathematicaP freshes v e

showProg :: P () Re -> String
showProg = showP freshes (\case)

instance Show (P () Re) where
  show = replace "%" "/" . showProg

mathematica' :: P () Re -> IO ()
mathematica' = putStrLn . replace "%" "/" . mathematicaP freshes (\case)

type Solution γ d = (Ordering, Expr γ d)

-- | @solve e x@ returns the coefficient of the 1st variable in the expression,
-- and the rest (terms not involving the 1st variable). I.e., c x + e = 0.
solve :: Expr (γ, Re) Re -> (Re, Expr γ Re)
solve (Expr k0 xs) = (c', Expr k0 e)
  where (c', e) = solveAffine xs

solveAffine :: [(Re, Available Re (γ, Re))] -> (Re, [(Re, Available Re γ)])
solveAffine ([]) = (0, [])
solveAffine ((c, Here) : xs) = (c + c', e)
  where (c', e) = solveAffine xs
solveAffine ((c, There x) : xs) = (c', (c, x) : e)
  where (c', e) = solveAffine xs 

-- FIXME: detect always true and always false cases.
solve' :: Cond (γ, Re) -> Solution γ Re
solve' c0 = case c0 of
  IsZero _ -> (EQ, (-1 / c) *^ e)
  IsNegative _ -> if c < 0 then (GT, (1 / (-c)) *^ e) else (LT, ((-1) / c) *^ e)
  where (c, e) = solve (condExpr c0)
  
shallower :: SomeVar γ -> SomeVar γ -> Bool
SomeVar Here `shallower` _ = False
SomeVar (There _) `shallower` SomeVar Here = True
SomeVar (There x) `shallower` SomeVar (There y)
  = SomeVar x `shallower` SomeVar y

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

travExpr :: Applicative f =>
            (forall v. Available v γ -> f (Available v δ)) ->
            Expr γ t -> f (Expr δ t)
travExpr f (Expr k0 xs) = Expr k0 <$> (traverse (\(k, e) -> (k,) <$> f e) xs)

occurExpr :: Expr (γ, x) t -> Maybe (Expr γ t)
occurExpr = travExpr $ \case
  Here -> Nothing
  There x -> Just x

integrate :: d ~ Re => Domain γ d -> P (γ, d) Re -> P γ Re
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
    domainToConditions x0 d $ substP (\i -> case i of { Here -> x0;
                                                        There i
                                                        -> Expr 0 [(1, i)] }) e
    where (coef, expr) = solve c'
          x0 = (-1 / coef) *^ expr
  Just c'' -> cond (IsZero c'') (integrate d e)
integrate d (Add e e') = Add (integrate d e) (integrate d e')
integrate d (Div e e') = Div (integrate d e) (integrate d e')
integrate d e = Integrate d e

cond :: Cond γ -> P γ Re -> P γ Re
cond c (Cond c' e) = if (deepest c) `shallower` (deepest c')
                     then Cond c (Cond c' e)
                     else Cond c' (cond c e)
cond c (normalise -> e) = Cond c e

normalise :: P γ Re -> P γ Re
normalise = \case
  Cond c (normalise -> e) -> cond c e
  Integrate d (normalise -> e) -> integrate d e
  Add (normalise -> p1) (normalise -> p2) -> Add p1 p2
  Div (normalise -> p1) (normalise -> p2) -> Div p1 p2
  Ret e -> Ret e

-- | Take typed descriptions of real numbers onto Maxima programs. 
maxima :: Unit ⊢ R -> P () Re
maxima = normalise . evalP . normalForm . clean . evalβ

-- | Take typed descriptions of real numbers onto Mathematica programs.
mathematica :: Unit ⊢ R -> IO ()
mathematica = mathematica' . maxima

-- Domain without restriction
full :: Domain γ x
full = Domain [] [] []

exampleInEq :: P () Re
exampleInEq = Integrate full $
              Cond (IsNegative (Expr 7 [(-1, Here)])) $
              Ret $ RetPoly $ Poly 10 [(1, [(Here, 1)])]
              

-- >>> exampleInEq
-- integrate(𝟙(7.0 + (-1.0 * x) ≤ 0) * (10.0 + x), x)

-- >>> normalise exampleInEq
-- integrate((10.0 + x), x, max(7.0, -inf), inf)

exampleEq :: P () Re
exampleEq = Integrate full $
            Cond (IsZero (Expr 7 [(-1, Here)])) $
            Ret $ RetPoly $ Poly 10 [(1, [(Here, 1)])]

-- >>> exampleEq
-- integrate((7.0 + (-1.0 * x) ≐ 0) * (10.0 + x), x)

-- >>> normalise exampleEq
-- (17.0)

example :: P () Re
example = Integrate full $ Integrate full $
          Cond (IsNegative (Expr 0 [(3, There Here), (2, Here)])) $
          Cond (IsNegative (Expr 2 [(1, There Here)])) $
          Ret $ RetPoly $ Poly 1 []

-- >>> example
-- integrate(integrate(𝟙((3.0 * x) + (2.0 * y) ≤ 0) * 𝟙(2.0 + x ≤ 0) * (1.0), y), x)

-- >>> normalise example
-- integrate(integrate((1.0), y, -inf, min((-1.5 * x), inf)), x, -inf, min(-2.0, inf))

example1 :: P () Re
example1 = Integrate full $ Integrate full $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)])) $
           Ret $ RetPoly $ Poly 1 []

-- >>> example1
-- integrate(integrate((4.0 + x + (-1.0 * y) ≐ 0) * (1.0), y), x)

-- >>> normalise example1
-- integrate((1.0), x)

example2 :: P () Re
example2 = Integrate full $
           Integrate (Domain [] [Expr 1 [(1, Here)]] []) $
           Cond (IsZero (Expr 4 [(2, There Here), (-1, Here)]) ) $
           Ret $ RetPoly $ Poly 0 [(1, [(Here, 1)])]

-- >>> example2
-- integrate(integrate((4.0 + (2.0 * x) + (-1.0 * y) ≐ 0) * (y), y, max(1.0 + x, -inf), inf), x)

-- >>> normalise example2
-- integrate((4.0 + (2.0 * x)), x, max(-3.0, -inf), inf)

example3 :: P () Re
example3 = Integrate full $
           Integrate full $
           Cond (IsNegative (Expr 3 [(-1, Here)])) $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)])) $
           Ret $ RetPoly $ Poly 0 [(1, [(Here, 2)])]

-- >>> example3
-- integrate(integrate(𝟙(3.0 + (-1.0 * y) ≤ 0) * (4.0 + x + (-1.0 * y) ≐ 0) * (y^2.0), y), x)

-- >>> normalise example3
-- integrate((16.0 + (4.0 * x) + (x*x) + (4.0 * x)), x, max(-1.0, -inf), inf)

example4 :: P () Re
example4 = Integrate full $
           Integrate full $
           Cond (IsNegative (Expr 3 [(-1, Here)])) $
           Cond (IsZero (Expr 0 [(1, (There Here)), (-1, Here)])) $
           Ret $ RetExps $ Exps 0 [(1, RetPoly $ Poly 0 [(1, [(Here, 2)]), (1, [(Here, 1)])])]

-- >>> example4
-- integrate(integrate(𝟙(3.0 + (-1.0 * y) ≤ 0) * (x + (-1.0 * y) ≐ 0) * (exp(y^2.0 + y)), y), x)

-- >>> normalise example4
-- integrate((exp((x*x) + x)), x, max(3.0, -inf), inf)

example5 :: Returned ((), Re) Re
example5 = RetExps $ Exps 2 [(1, RetPoly $ Poly 2 [(1, [(Here, 1)]), (2, [(Here, 1)])])]

example6 :: Returned ((), Re) Re
example6 = RetExps $ Exps 1 [(1, RetPoly $ Poly 2 [(1, [(Here, 2)]), (1, [(Here, 1)])])]  

-- >>> Integrate full $ multP (Ret example5) $ Integrate full $ wkP $ Ret example6
-- integrate(integrate((2.0 + exp(2.0 + x + (2.0 * x)) + (2.0 * exp(2.0 + (x*x) + x)) + exp(4.0 + x + (2.0 * x) + (x*x) + x)), y), x)

-- integrate((2.0 + exp(x^2.0 + x) + (2.0 * exp(2.0 + x^2.0 + x)) + exp(2.0 + x^2.0 + x + x^2.0 + x)), x)

-- >>> Integrate full $ Ret $ expReturned 3 $ RetPoly $ Poly 1 [(3,[(Here, 2)])] :: P () Re
-- integrate((1.0 + (3.0 * x^2.0) + (9.0 * x^2.0*x^2.0) + (3.0 * x^2.0) + (9.0 * x^2.0*x^2.0) + (27.0 * x^2.0*x^2.0*x^2.0) + (9.0 * x^2.0*x^2.0) + (3.0 * x^2.0)), x)
