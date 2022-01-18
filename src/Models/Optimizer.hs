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

-- import Control.Monad (ap)
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

data Expr γ α = Expr α [(α, Available α γ)]
  -- Linear combination. List of coefficients and variables (α is a vector
  -- space).
  -- Example u - v is represented by @Expr 0 [(1, u), (-1,v)]@.

data Monomial γ α = Mono { monoCoef :: α,
                           monoVars :: [(Available α γ, α)],
                           monoExponential :: Polynomial γ α } deriving Eq
  -- E.g., @Mono c1 [(x, c2), (y, c3)] p@ represents c1 * x^c2 * y^c3 * exp(p).

type Exponentiated γ α = (α, Returned γ α)
  -- E.g., @(c1, p)@ represents c1 * exp(p).

data Polynomial γ α = Poly α [Monomial γ α] deriving Eq
data Exponentials γ α = Exps α [Exponentiated γ α] deriving Eq

type Returned γ α = Polynomial γ α
                  -- | RetExps (Exponentials γ α)
                  -- | Plus (Polynomial γ α) (Exponentials γ α)
                  -- | Plus' (Returned γ α) (Returned γ α)
                  -- | Times (Polynomial γ α) (Exponentials γ α)
                  -- | Times' (Returned γ α) (Returned γ α)
                  -- @Poly c cs@ represents c + sum of cs.
                  -- @Exp c cs@ represents c + sum of cs.
                  -- @Plus x y@ represents x + y.
                  -- @Times x y@ represents x * y.

multConst :: Num α => α -> Polynomial γ α -> Polynomial γ α
multConst c (Poly c1 cs) = case cs of
                             [] -> Poly (c * c1) []
                             (Mono c' xs e) : cs' ->
                               case multConst c (Poly c1 cs') of
                                 Poly c1' cs'' -> Poly c1' ((Mono (c * c')  xs e) : cs'')
multComp :: Num α => Polynomial γ α -> Monomial γ α -> [Monomial γ α]
multComp (Poly c1 cs) m@(Mono c xs e) =
                            case cs of
                                  [] -> [Mono (c1 * c)  xs e]
                                  (Mono c' xs' e') : cs' -> 
                                    Mono (c' * c) (xs' ++ xs) (e `addPoly` e') :
                                    multComp (Poly c1 cs') m


multPoly :: (Num α, Eq α) => Polynomial γ α -> Polynomial γ α -> Polynomial γ α
multPoly (Poly c1 cs1) p2
  = case multConst c1 p2 of
      Poly c2' cs2' -> Poly c2' $ filter (\(Mono c _ _) -> c /= 0) $
                       cs2' ++ (concat $ map (multComp p2) cs1)

-- multReturned :: (Num α, Eq α) => Returned γ α -> Returned γ α -> Returned γ α
-- multReturned = \case
--   RetPoly p@(Poly c1 cs1) -> \case
--     RetPoly p2 -> multPoly p p2  
    -- RetExps e -> Times p e
    -- e@(Plus _ _) -> Times' (RetPoly p) e
    -- Times (multReturned (RetPoly p) . RetPoly -> RetPoly p') e -> Times p' e
    -- e@(Plus' _ _) -> Times' (RetPoly p) e
    -- e@(Times' _ _) -> Times' (RetPoly p) e
  -- RetExps e@(Exps c1 es1) -> \case
  --   RetPoly p -> Times p e
  --   RetExps (Exps c2 es2) -> RetExps $ Exps (c1 * c2) $
  --     ((\(x, e1) -> (c2 * x, e1)) <$> es1) ++
  --     ((\(y, e2) -> (c1 * y, e2)) <$> es2) ++
  --     ((\(x, e1) (y, e2) -> (x * y, e1 `addReturned` e2)) <$> es1 <*> es2)
  --   e'@(Plus _ _) -> Times' (RetExps e) e'
  --   Times p (multReturned (RetExps e) . RetExps -> RetExps e') -> Times p e'
  --   e'@(Plus' _ _) -> Times' (RetExps e) e'
  --   e'@(Times' _ _) -> Times' (RetExps e) e'
  -- Times p e -> \case
  --   RetPoly p' -> multReturned (RetPoly p') (Times p e)
  --   RetExps e' -> multReturned (RetExps e') (Times p e)
  --   e'@(Plus _ _) -> Times' (Times p e) e'
  --   Times
  --     (multReturned (RetPoly p) . RetPoly -> RetPoly p')
  --     (multReturned (RetExps e) . RetExps -> RetExps e') -> Times p' e'
  --   e'@(Plus' _ _) -> Times' (Times p e) e'
  --   e'@(Times' _ _) -> Times' (Times p e) e'
  -- e@(Plus' _ _) -> \e' -> Times' e e'
  -- e@(Times' _ _) -> \e' -> Times' e e'

expPoly :: (Num α, Eq α) => α -> Polynomial γ α -> Polynomial γ α
expPoly 1 e = e
expPoly n e = multPoly e (expPoly (n - 1) e)

-- | Induced vector space structure over Expr γ α:

-- | Multiplication by a scalar (expresions are linear)
(*^) :: Num α => α -> Expr γ α -> Expr γ α
c *^ Expr k0 xs = Expr (c * k0) [ (c * c', v) | (c', v) <- xs ]

-- (**^) :: (Num α, Eq α) => α -> Poly γ α -> Poly γ α
-- c **^ e = multPoly (Poly c []) e
  
-- | Addition
add :: Num α => Expr γ α -> Expr γ α -> Expr γ α
add (Expr a xs) (Expr a' xs') = Expr (a + a') (xs ++ xs')

addPoly :: Num α => Polynomial γ α -> Polynomial γ α -> Polynomial γ α
addPoly = \case
  (Poly c1 cs1) -> \case
    (Poly c2 cs2) -> Poly (c1 + c2) $ cs1 ++ cs2


-- addReturned :: Num α => Returned γ α -> Returned γ α -> Returned γ α
  --   RetExps e -> Plus p e
  --   Plus (addReturned (RetPoly p) . RetPoly -> RetPoly p') e -> Plus p' e
  --   e@(Times _ _) -> Plus' (RetPoly p) e
  --   e@(Plus' _ _) -> Plus' (RetPoly p) e
  --   e@(Times' _ _) -> Plus' (RetPoly p) e
  -- RetExps e@(Exps c1 es1) -> \case
  --   RetPoly p -> Plus p e
  --   RetExps (Exps c2 es2) -> RetExps $ Exps (c1 + c2) $ es1 ++ es2
  --   Plus p (addReturned (RetExps e) . RetExps -> RetExps e') -> Plus p e'
  --   e'@(Times _ _) -> Plus' (RetExps e) e'
  --   e'@(Plus' _ _) -> Plus' (RetExps e) e'
  --   e'@(Times' _ _) -> Plus' (RetExps e) e'
  -- p1@(Plus p e) -> \case
  --   p2@(RetPoly _) -> addReturned p2 p1
  --   e@(RetExps _) -> addReturned e p1
  --   Plus
  --     (addReturned (RetPoly p) . RetPoly -> RetPoly p')
  --     (addReturned (RetExps e) . RetExps -> RetExps e') -> Plus p' e'
  --   e@(Times _ _) -> Plus' p1 e
  --   e@(Plus' _ _) -> Plus' p1 e
  --   e@(Times' _ _) -> Plus' p1 e
  -- e@(Times _ _) -> \e' -> Plus' e e'
  -- e@(Times' _ _) -> \e' -> Plus' e e'
  -- e@(Plus' _ _) -> \e' -> Plus' e e'

zero = Expr 0 []

data Cond γ = IsNegative { condExpr :: (Expr γ Rat) }
              -- Meaning of this constructor: expression ≤ 0
              -- Example: u ≤ v is represented by @IsNegative [(1, u), (-1, v)]@
            | IsZero { condExpr :: (Expr γ Rat) }
              -- Meaning of this constructor: expression = 0
              -- Example: u = v is represented by @IsZero [(1, u), (-1, v)]@


-- | restrict the bounds by moving the bounds. Also return conditions
-- that ensure that the bounds are in the right order.
restrictDomain :: α ~ Rat => Cond (γ, α) -> Domain γ α -> (Domain γ α, [Cond γ])
restrictDomain c (Domain cs los his) = case solve' c of -- version with solver
  (LT, e) -> (Domain cs los (e:his), [ lo `lessThan` e | lo <- los ]) 
  (GT, e) -> (Domain cs (e:los) his, [ e `lessThan` hi | hi <- his ])

data P γ α where
  Integrate :: d ~ Rat => Domain γ d -> P (γ, d) α -> P γ α
  Cond :: Cond γ -> P γ α -> P γ α
  Add :: P γ α -> P γ α -> P γ α
  Div :: P γ α -> P γ α -> P γ α
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
exprToPoly (Expr c xs) = Poly c [ (Mono c' [(x, 1)] (Poly 0 [])) | (c', x) <- xs ] 

exponential :: Num α => Polynomial γ α -> Polynomial γ α
exponential p = Poly 0 [Mono 1 [] p]

substMono :: Subst γ δ -> forall α. (Num α, Eq α) => Monomial γ α -> Polynomial δ α
substMono f (Mono c xs e) = multConst c
                            (foldr multPoly (Poly 1 [])
                                   [ expPoly c' (exprToPoly (f x))
                                   | (x, c') <- xs ])
                          `multPoly` exponential (substPoly f e)

substPoly :: Subst γ δ ->
                 forall α. (Num α, Eq α) => Polynomial γ α -> Polynomial δ α
substPoly f = \case
  Poly k0 cs -> foldr addPoly (Poly k0 []) (map (substMono f) cs)

  -- RetExps (Exps k0 es) -> RetExps $ Exps k0 $
  --                         [ (c, substReturned f e) | (c, e) <- es ]
  -- Plus
  --   (substReturned f . RetPoly -> RetPoly p)
  --   (substReturned f . RetExps -> RetExps e) -> Plus p e
  -- Plus' (substReturned f -> p) (substReturned f -> e) -> Plus' p e
  -- Times
  --   (substReturned f . RetPoly -> RetPoly p)
  --   (substReturned f . RetExps -> RetExps e) -> Times p e
  -- Times' (substReturned f -> p) (substReturned f -> e) -> Times' p e
    
substCond :: Subst γ δ -> Cond γ -> Cond δ
substCond f (IsNegative e) = IsNegative $ substExpr f e
substCond f (IsZero e) = IsZero $ substExpr f e

substDomain :: Num d => Subst γ δ -> Domain γ d -> Domain δ d
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

type family RpOf γ where
  RpOf Rat = 'R
  RpOf () = 'Unit
  RpOf (γ, α) = (RpOf γ × RpOf α)

pattern NNVar :: forall (γ :: Type) (α :: Type).
                   Available (Eval α) (Eval γ) -> NF γ α
pattern NNVar i <- Neu (NeuVar (evalVar -> i))
pattern EqVars :: forall (γ :: Type) (α :: Type).
                    () =>
                    forall (α2 :: Type) (α3 :: Type).
                    ((α3 ⟶ (α2 ⟶ α)) ~ ('R ':-> ('R ⟶ 'R))) =>
                    (α3 ∈ γ) -> (α2 ∈ γ) -> NF γ α
pattern EqVars i j
  = Neu (NeuApp (NeuApp (NeuCon (General EqRl))
                 (Neu (NeuVar i))) (Neu (NeuVar j)))
pattern Mults :: forall (γ :: Type) (α :: Type).
                   () =>
                   forall (α2 :: Type) (α3 :: Type).
                   ((α3 ⟶ (α2 ⟶ α)) ~ ('R ':-> ('R ⟶ 'R))) =>
                   NF γ α3 -> NF γ α2 -> NF γ α
pattern Mults x y
  = Neu (NeuApp (NeuApp (NeuCon (General Mult)) x) y)
pattern Adds :: forall (γ :: Type) (α :: Type).
                  () =>
                  forall (α2 :: Type) (α3 :: Type).
                  ((α3 ⟶ (α2 ⟶ α)) ~ ('R ':-> ('R ⟶ 'R))) =>
                  NF γ α3 -> NF γ α2 -> NF γ α
pattern Adds x y
  = Neu (NeuApp (NeuApp (NeuCon (General Addi)) x) y)
pattern MultsVar :: forall (γ :: Type) (α :: Type).
                      () =>
                      forall (α2 :: Type) (α3 :: Type).
                      ((α3 ⟶ (α2 ⟶ α)) ~ ('R ':-> ('R ⟶ 'R))) =>
                      NF γ α3 -> (α2 ∈ γ) -> NF γ α
pattern MultsVar x j
  = Neu (NeuApp (NeuApp (NeuCon (General Mult)) x) (Neu (NeuVar j)))
pattern InEqVars :: forall (γ :: Type) (α :: Type).
                      () =>
                      forall (α2 :: Type) (α3 :: Type) (α4 :: Type).
                      ((α2 ⟶ α) ~ ('T ':-> 'R),
                       (α4 ⟶ (α3 ⟶ α2)) ~ ('R ':-> ('R ⟶ 'T))) =>
                      (α4 ∈ γ) -> (α3 ∈ γ) -> NF γ α
pattern InEqVars i j
  = Neu (NeuApp (NeuCon (General Indi))
         (Neu (NeuApp (NeuApp (NeuCon (Special GTE))
                       (Neu (NeuVar i)))
               (Neu (NeuVar j)))))
pattern Normal :: forall (γ :: Type) (α :: Type).
                    () =>
                    forall (α2 :: Type) (α3 :: Type) (α4 :: Type) (β :: Type).
                    ((α3 ⟶ (α2 ⟶ α)) ~ (('R × 'R) ':-> (('R ⟶ 'R) ⟶ 'R)),
                     α3 ~ (α4 ':× β), α4 ~ 'R, β ~ 'R) =>
                    Rational -> Rational -> NF γ α2 -> NF γ α
pattern Normal x y f
  = Neu (NeuApp (NeuApp (NeuCon (General Nml))
                 (NFPair (Neu (NeuCon (General (Incl x))))
                  (Neu (NeuCon (General (Incl y)))))) f)
pattern Uniform :: forall (γ :: Type) (α :: Type).
                     () =>
                     forall (α2 :: Type) (α3 :: Type) (α4 :: Type) (β :: Type).
                     ((α3 ⟶ (α2 ⟶ α)) ~ (('R × 'R) ':-> (('R ⟶ 'R) ⟶ 'R)),
                      α3 ~ (α4 ':× β), α4 ~ 'R, β ~ 'R) =>
                     Rational -> Rational -> NF γ α2 -> NF γ α
pattern Uniform x y f
  = Neu (NeuApp (NeuApp (NeuCon (General Uni))
                 (NFPair (Neu (NeuCon (General (Incl x))))
                  (Neu (NeuCon (General (Incl y)))))) f)
pattern Lesbegue :: forall (γ :: Type) (α :: Type).
                      () =>
                      forall (α1 :: Type).
                      ((α1 ⟶ α) ~ (('R ⟶ 'R) ':-> 'R)) =>
                      NF γ α1 -> NF γ α
pattern Lesbegue f
  = Neu (NeuApp (NeuCon (General Leb)) f)
pattern Divide :: forall (γ :: Type) (α :: Type).
                    () =>
                    forall (α2 :: Type) (α3 :: Type).
                    ((α3 ⟶ (α2 ⟶ α)) ~ ('R ':-> ('R ⟶ 'R))) =>
                    NF γ α3 -> NF γ α2 -> NF γ α
pattern Divide x y
  = Neu (NeuApp (NeuApp (NeuCon (General Divi)) x) y)

evalP :: NF 'Unit 'R -> P () Rat
evalP = evalP'

zeroPoly :: Polynomial γ Rational
zeroPoly = Poly 0 []

evalP' :: NF γ 'R -> P (Eval γ) Rat
evalP' = \case
  Neu (NeuCon (General (Incl x))) -> Ret $ Poly x []
  Neu (NeuApp (NeuApp (NeuCon (General EqRl))
                 (Adds (NNVar i) (NNVar j))) (NNVar k))
    -> Cond (IsZero $ Expr 0 [(1, i), (1, j), (-1, k)]) $
       Ret $ Poly 1 []
  EqVars (evalVar -> i) (evalVar -> j) ->
    Cond (IsZero $ Expr 0 [(1, i), (-1, j)]) $ Ret $ Poly 1 []
  InEqVars (evalVar -> i) (evalVar -> j) ->    
    Cond (IsNegative $ Expr 0 [(-1, i), (1, j)]) $ Ret $ Poly 1 []
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

type Vars γ  = forall v. Available v γ -> String

showExpr :: Vars γ -> Expr γ Rat -> String
showExpr v (Expr k0 xs) = intercalate " + " $
                          (if k0 /= 0 || xs == [] then [showR k0] else []) ++
                          [ (if k /= 1 then parens else id) $
                            (if k /= 1 || xs == []
                                      then showR k ++ " * "
                                      else "") ++ v x | (k, x) <- xs ]


showPoly :: Vars γ -> Polynomial γ Rat -> String
showPoly v
  (Poly k0 cs) = parens $ intercalate " + " $
                          (if k0 /= 0 || cs == [] then [showR k0] else []) ++
                          filter (/= "")
                          [ case c of
                              0 -> ""
                              _ -> parens $ intercalate " * " $ 
                                    (if c /= 1 then (showR c :) else id) 
                                    [v x ++ (case c' of 1 -> ""; _ -> "^" ++ showR c') | (x, c') <- xs]
                                    ++ ["Exp[" ++ showPoly v e ++"]" | not (isZero e)]
                                   | (Mono c xs e) <- cs ]

  -- RetExps (Exps k0 es) -> parens $ intercalate " + " $
  --                         (if k0 /= 0 || es == [] then [showR k0] else []) ++
  --                         filter (/= "")
  --                         [ case c of
  --                             0 -> ""
  --                             1 -> "exp" ++ showReturned v e
  --                             _ -> parens $
  --                                  showR c ++ " * exp" ++
  --                                  showReturned v e | (c, e) <- es ]
  -- Plus p e -> case p of
  --               Poly 0 [] -> showReturned v (RetExps e)
  --               _ -> case e of
  --                      Exps 0 [] -> showReturned v (RetPoly p)
  --                      _ -> showReturned v (RetPoly p) ++ " + " ++
  --                           showReturned v (RetExps e)
  -- Times p e -> case p of
  --                Poly 0 [] -> "0"
  --                Poly 1 [] -> showReturned v (RetExps e)
  --                _ -> case e of
  --                       Exps 0 [] -> "0"
  --                       Exps 1 [] -> showReturned v (RetPoly p)
  --                       _ -> showReturned v (RetPoly p) ++ " * " ++
  --                            showReturned v (RetExps e)
  -- Plus' p e -> "(" ++ showReturned v p ++ ") + (" ++ showReturned v e ++ ")"
  -- Times' p e -> "(" ++ showReturned v p ++ ") * (" ++ showReturned v e ++ ")"

mathematicaReturned :: Vars γ -> Returned γ Rat -> String
mathematicaReturned v = \case
   (Poly k0 cs) -> parens $ intercalate " + " $
                          (if k0 /= 0 || cs == [] then [showR k0] else []) ++
                          filter (/= "")
                          [ case c of
                              0 -> ""
                              1 -> (if length xs > 1 then parens else id)
                                   (intercalate "*" $
                                           map (\(x, c') -> v x ++
                                                 case c' of
                                                   1 -> ""
                                                   _ -> "^" ++ showR c')
                                          xs)
                              _ -> parens (showR c ++ " * " ++
                                           (intercalate "*" $
                                            map (\(x, c') -> v x ++
                                                  case c' of
                                                    1 -> ""
                                                    _ -> "^" ++ showR c')
                                            xs)) | (Mono c xs e) <- cs ]
  -- RetExps (Exps k0 es) -> parens $ intercalate " + " $
  --                         (if k0 /= 0 || es == [] then [showR k0] else []) ++
  --                         filter (/= "")
  --                         [ case c of
  --                             0 -> ""
  --                             1 -> "exp" ++ mathematicaReturned v e
  --                             _ -> parens $
  --                                  showR c ++ " * Exp" ++ (brackets $
  --                                  mathematicaReturned v e) | (c, e) <- es ]
  -- Plus p e -> case p of
  --               Poly 0 [] -> mathematicaReturned v (RetExps e)
  --               _ -> case e of
  --                      Exps 0 [] -> mathematicaReturned v (RetPoly p)
  --                      _ -> mathematicaReturned v (RetPoly p) ++ " + " ++
  --                           mathematicaReturned v (RetExps e)
  -- Times p e -> case p of
  --                Poly 0 [] -> "0"
  --                Poly 1 [] -> mathematicaReturned v (RetExps e)
  --                _ -> case e of
  --                       Exps 0 [] -> "0"
  --                       Exps 1 [] -> mathematicaReturned v (RetPoly p)
  --                       _ -> mathematicaReturned v (RetPoly p) ++ " * " ++
  --                            mathematicaReturned v (RetExps e)
  -- Plus' p e -> "(" ++ mathematicaReturned v p ++ ") + (" ++
  --              mathematicaReturned v e ++ ")"
  -- Times' p e -> "(" ++ mathematicaReturned v p ++ ") * (" ++
  --               mathematicaReturned v e ++ ")"

showCond :: Vars γ -> Cond γ -> String
showCond v = \case
  c@(IsNegative c') -> "Boole" <> (brackets $ showExpr v c' <> " ≤ 0")
  c@(IsZero c') -> "DiracDelta" ++ (brackets $ showExpr v c')

parens :: String -> String
parens x = "(" ++ x ++ ")"

brackets :: String -> String
brackets x = "[" ++ x ++ "]"

braces :: String -> String
braces x = "{" ++ x ++ "}"

showBounds :: Vars γ -> Bool -> [Expr γ Rat] -> String
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

mathematicaBounds :: Vars γ -> Bool -> [Expr γ Rat] -> String
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

showP :: [String] -> Vars γ -> P γ Rat -> String
showP freshes@(f:fs) v = \case
  Ret e -> showPoly v e
  Add p1 p2 -> "(" ++ showP freshes v p1 ++ ") + (" ++ showP freshes v p2 ++ ")"
  Div p1 p2 -> "(" ++ showP freshes v p1 ++ ") / (" ++ showP freshes v p2 ++ ")"
  Integrate (Domain cs los his) e -> ("integrate" ++) $ parens $
    showP fs (\case Here -> f; There i -> v i) e ++
    (when cs $ f ++ "∈" ++
     braces (intercalate "∧" $ map (showCond (\case Here -> f; There i -> v i))
              cs)) ++ ", " ++ f ++ ", " ++ showBounds v True los ++ ", " ++
    showBounds v False his
  Cond c e -> showCond v c ++ " * " ++ showP freshes v e

mathematicaP :: [String] -> Vars γ -> P γ Rat -> String
mathematicaP freshes@(f:fs) v = \case
  Ret e -> mathematicaReturned v e
  Add p1 p2 -> "(" ++ mathematicaP freshes v p1 ++ ") + (" ++
               mathematicaP freshes v p2 ++ ")"
  Div p1 p2 -> "(" ++ mathematicaP freshes v p1 ++ ") / (" ++
               mathematicaP freshes v p2 ++ ")"
  Integrate (Domain cs los his) e -> ("Integrate" ++) $ brackets $
    mathematicaP fs (\case Here -> f; There i -> v i) e ++
    (when cs $ f ++ "∈" ++
     braces (intercalate "∧" $ map (showCond (\case Here -> f; There i -> v i))
             cs)) ++ ", " ++ (braces $ f ++ ", " ++ mathematicaBounds v True los
                              ++ ", " ++ mathematicaBounds v False his)
  Cond c e -> showCond v c ++ " * " ++ mathematicaP freshes v e

showProg :: P () Rat -> String
showProg = showP freshes (\case)

instance Show (P () Rat) where
  show = replace "%" "/" . showProg

mathematica' :: [String] -> Vars γ -> P γ Rat -> IO ()
mathematica' fs vars = putStrLn . replace "%" "/" . mathematicaP fs vars

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

isZero :: Num α => Eq α => Polynomial γ α -> Bool
isZero (Poly 0 ms) = and [c == 0 | Mono c _ _ <- ms]
isZero _ = False




integrate :: d ~ Rat => Domain γ d -> P (γ, d) Rat -> P γ Rat
integrate d (Ret z) | isZero z = Ret $ zeroPoly
integrate d (Cond c@(IsNegative c') e) = case occurExpr c' of
  -- Nothing -> integrate d' e
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

-- | Take typed descriptions of real numbers onto Mathematica programs.
mathematica :: 'Unit ⊢ 'R -> IO ()
mathematica = mathematica' freshes (\case) . maxima

-- | Take typed descriptions of real numbers onto Mathematica programs.
mathematicaFun :: 'Unit ⊢ ('R ⟶ 'R) -> IO ()
mathematicaFun = mathematica' fs (\case Here -> f; There _ -> error "mathematicaFun: are you trying to access the end of context? (Unit)") . maxima . absInversion
  where (f:fs) = freshes

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
-- integrate(𝟙(7 / 1 + ((-1) / 1 * x) ≤ 0) * (10 / 1 + x), x)

-- >>> normalise exampleInEq
-- integrate((10 / 1 + x), x, max(7 / 1, -inf), inf)

exampleEq :: P () Rat
exampleEq = Integrate full $
            Cond (IsZero (Expr 7 [(-1, Here)])) $
            Ret $ Poly 10 [var Here]

-- >>> exampleEq
-- integrate((7.0 + (-1.0 * x) ≐ 0) * (10.0 + x), x)

-- >>> normalise exampleEq
-- (17.0)

example :: P () Rat
example = Integrate full $ Integrate full $
          Cond (IsNegative (Expr 0 [(3, There Here), (2, Here)])) $
          Cond (IsNegative (Expr 2 [(1, There Here)])) $
          Ret $ Poly 1 []

-- >>> example
-- integrate(integrate(𝟙((3.0 * x) + (2.0 * y) ≤ 0) * 𝟙(2.0 + x ≤ 0) * (1.0), y), x)

-- >>> normalise example
-- integrate(integrate((1.0), y, -inf, min((-1.5 * x), inf)), x, -inf, min(-2.0, inf))

example1 :: P () Rat
example1 = Integrate full $ Integrate full $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)])) $
           Ret $ Poly 1 []

-- >>> example1
-- integrate(integrate((4.0 + x + (-1.0 * y) ≐ 0) * (1.0), y), x)

-- >>> normalise example1
-- integrate((1.0), x)

example2 :: P () Rat
example2 = Integrate full $
           Integrate (Domain [] [Expr 1 [(1, Here)]] []) $
           Cond (IsZero (Expr 4 [(2, There Here), (-1, Here)]) ) $
           Ret $ Poly 0 [var Here]

-- >>> example2
-- integrate(integrate((4.0 + (2.0 * x) + (-1.0 * y) ≐ 0) * (y), y, max(1.0 + x, -inf), inf), x)

-- >>> normalise example2
-- integrate((4.0 + (2.0 * x)), x, max(-3.0, -inf), inf)

example3 :: P () Rat
example3 = Integrate full $
           Integrate full $
           Cond (IsNegative (Expr 3 [(-1, Here)])) $
           Cond (IsZero (Expr 4 [(1, (There Here)), (-1, Here)])) $
           Ret $ Poly 0 [Mono 1 [(Here,2)] zeroPoly]

-- >>> example3
-- integrate(integrate(𝟙(3 / 1 + ((-1) / 1 * y) ≤ 0) * (4 / 1 + x + ((-1) / 1 * y) ≐ 0) * (y^2 / 1), y), x)

-- >>> normalise example3
-- integrate((16 / 1 + (4 / 1 * x) + (x*x) + (4 / 1 * x)), x, max((-1) / 1, -inf), inf)

example4 :: P () Rat
example4 = Integrate full $
           Integrate full $
           Cond (IsNegative (Expr 3 [(-1, Here)])) $
           Cond (IsZero (Expr 0 [(1, (There Here)), (-1, Here)])) $
           Ret $ Poly 0 [Mono 1 [] (Poly 0 [Mono 1 [(Here,2)] zeroPoly
                                           ,Mono 1 [(Here,1)] zeroPoly])]

-- >>> example4
-- integrate(integrate(Boole[3 + (-1 * y) ≤ 0] * DiracDelta[x + (-1 * y)] * ((Exp[((y^2) + (y))])), y, -inf, inf), x, -inf, inf)

-- >>> normalise example4
-- integrate(((exp(((x * x) + (x))))), x, max(3, -inf), inf)

-- example5 :: Returned ((), Rat) Rat
-- example5 = RetExps $ Exps 2 [(1, Poly 2 [(1, [(Here, 1)]), (2, [(Here, 1)])])]

-- example6 :: Returned ((), Rat) Rat
-- example6 = RetExps $ Exps 1 [(1, Poly 2 [(1, [(Here, 2)]), (1, [(Here, 1)])])]  

-- >>> Integrate full $ multP (Ret example5) $ Integrate full $ wkP $ Ret example6
-- integrate(integrate((2 / 1 + exp(2 / 1 + x + (2 / 1 * x)) + (2 / 1 * exp(2 / 1 + (x*x) + x)) + exp(4 / 1 + x + (2 / 1 * x) + (x*x) + x)), y), x)

-- integrate((2.0 + exp(x^2.0 + x) + (2.0 * exp(2.0 + x^2.0 + x)) + exp(2.0 + x^2.0 + x + x^2.0 + x)), x)

-- >>> Integrate full $ Ret $ expReturned 3 $ Poly 1 [(3,[(Here, 2)])] :: P () Rat
-- integrate((1 / 1 + (3 / 1 * x^2 / 1) + (9 / 1 * x^2 / 1*x^2 / 1) + (3 / 1 * x^2 / 1) + (9 / 1 * x^2 / 1*x^2 / 1) + (27 / 1 * x^2 / 1*x^2 / 1*x^2 / 1) + (9 / 1 * x^2 / 1*x^2 / 1) + (3 / 1 * x^2 / 1)), x)
