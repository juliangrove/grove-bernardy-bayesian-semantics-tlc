{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Models.Optimizer where

import Data.List
import Prelude as Pre
import TLC.Terms

type R = Double

data Domain γ x = Domain [Cond (γ, x)] [Expr γ x] [Expr γ x]

data Available α γ where
  Here :: Available α (γ, α)
  There :: Available α γ -> Available α (γ, β)
  
restrictDomain :: x ~ R => Cond (γ, x) -> Domain γ x -> Domain γ x
-- restrictDomain c (Domain cs' lowBounds highBounds) = Domain (c : cs') lowBounds highBounds -- basic version
restrictDomain c (Domain cs los his) = case solve' c of -- version with solver
  (LT, e) -> Domain cs los (e:his) 
  (GT, e) -> Domain cs (e:los) (his)
  (EQ, _) -> error "Dirac δ not supported yet"

data P γ x where
  Integrate :: (R ~ d) => Domain γ d -> P (γ, d) x -> P γ x
  Cond :: Cond γ -> P γ x -> P γ x
  Ret  :: Expr γ x -> P γ x

type Vars γ  = forall v. Available v γ -> String

showExpr :: Show x => Vars γ -> Expr γ x -> String
showExpr _ [] = "0"
showExpr v xs = intercalate " + " [show k ++ " * " ++ v x | (k, x) <- xs]

showCond :: Vars γ -> Cond γ -> String
showCond v c = showExpr v c <> " ≤ 0"

parens :: [Char] -> [Char]
parens x = "(" ++ x ++ ")"

braces :: [Char] -> [Char]
braces x = "{" ++ x ++ "}"

showBounds :: Show x => Vars γ -> Bool -> [Expr γ x] -> [Char]
showBounds _ lo [] = (if lo then "-" else "+") <> "∞"
showBounds v lo xs = (intercalate (if lo then "⊔" else "⊓") $ map (showExpr v) xs)

when :: [a] -> [Char] -> [Char]
when [] _ = ""
when _ x = x

showP :: Show x => [String] -> Vars γ -> P γ x -> String
showP freshes v = \case
  Ret x -> parens (showExpr v x)
  Integrate (Domain cs los his) e -> case freshes of
    [] -> error "showP: need more fresh variables!"
    f:fs -> "∫"  ++ (when cs $ f ++ "∈" ++ braces (intercalate "∧" $ map (showCond (\case Here -> f; There x -> v x)) cs))
                 ++ (when (los ++ his) (braces (showBounds v True los
                            ++ "≤" ++ f ++ "≤" ++
                            showBounds v False his)))
                 ++ showP fs (\case Here -> f; There x -> v x) e
  Cond c e -> ("𝟙" ++ parens (showCond v c)) ++ "*" ++ showP freshes v e

showProg :: Show x => P () x -> String
showProg = showP freshes (\case)


freshes :: [String]
freshes = "" : map show ints Pre.>>= \i -> map (++i) ["x", "y", "z", "u", "v", "w"]
  where  ints :: [Int]
         ints = 1 : map succ ints

instance Show x => Show (P () x) where
  show = showProg

type Cond γ = Expr γ R  -- Meaning of this result of expression is ≤ 0
-- Example u ≤ v is represented by u - v ≤ 0

type Solution γ d  = (Ordering, Expr γ d)

solve :: Num x => Cond (γ, x) -> (x, Expr γ R)
solve [] = (0,[])
solve ((c,Here):xs) = (c+c',e)
  where (c',e) = solve xs
solve ((c,There x):xs) = (c', (c,x):e)
  where (c',e) = solve xs

solve' :: Cond (γ,R) -> Solution γ R
solve' xs = if c < 0 then (GT,(1/(-c)) *^ e) else (LT,(1/c) *^ e)
  where (c,e) = solve xs

-- multiplication by scalar (expresions are linear)
(*^) :: Num t => t -> [(t, b)] -> [(t, b)]
_ *^ [] = []
c *^ ((c',v):xs) = (c*c',v) : c *^ xs

type Expr γ x = [(R, Available x γ)] -- linear combination. list of coefficients and variables [x is a ring]
-- Example u - v is represented by [(1,"u"),(-1,"v")]



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
deepest = foldr1 minVar . map SomeVar . map snd

travExpr :: Applicative f => (forall v. Available v γ -> f (Available v δ)) -> Expr γ t -> f (Expr δ t)
travExpr f xs = traverse (\(k,e) -> (k,) <$> f e) xs

occurExpr :: Expr (γ,x) t -> Maybe (Expr γ t)
occurExpr = travExpr $ \case
  Here -> Nothing
  There x -> Just x

integrate :: d ~ R => Domain γ d -> P (γ, d) x -> P γ x
integrate d (Cond c e) = case occurExpr c of
  Nothing -> integrate (restrictDomain c d) e
  Just c' -> cond c' (integrate d e)
integrate d e = Integrate d e

cond :: Cond γ -> P γ x -> P γ x
cond c (Cond c' e) = if (deepest c) `shallower` (deepest c') then Cond c (Cond c' e) else Cond c' (cond c e)
cond c e = Cond c e

normalise :: P γ t -> P γ t
normalise (Cond c e) = cond c (normalise e)
normalise (Integrate d e) = integrate d (normalise e)
normalise (Ret x) = Ret x

-- Domain without restriction
full :: Domain γ x
full = Domain [] [] []

example :: P () R
example = Integrate full $ Integrate full $ Cond [(4, There Here), (2, Here)] $ Cond [(1, There Here)] $ Ret [(666, Here)]

-- >>> :t full
-- full :: Domain γ x

-- >>> example
-- ∫∫𝟙(4.0 * x + 2.0 * y ≤ 0)*𝟙(1.0 * x ≤ 0)*(666.0 * y)

-- >>> normalise example
-- ∫{-∞≤x≤0}∫{-∞≤y≤2.0 * x}(666.0 * y)
