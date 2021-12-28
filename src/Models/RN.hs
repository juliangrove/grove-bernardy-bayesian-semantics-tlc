{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Models.RN where

import Control.Monad (ap)
import Examples.RSA
import TLC.Terms


-- | Variables
data V = V Char Int

instance Enum V where
  succ (V c i) = case c of
                     'x' -> V 'y' i
                     'y' -> V 'z' i
                     'z' -> V 'u' i
                     'u' -> V 'v' i
                     'v' -> V 'w' i
                     'w' -> V 'x' (succ i)
  toEnum i = case mod i 6 of
               0 -> V 'x' (div i 6)
               1 -> V 'y' (div i 6)
               2 -> V 'z' (div i 6)
               3 -> V 'u' (div i 6)
               4 -> V 'v' (div i 6)
               5 -> V 'w' (div i 6)
  fromEnum (V c i) = case c of
                         'x' -> i*6
                         'y' -> i*6 + 1
                         'z' -> i*6 + 2
                         'u' -> i*6 + 3
                         'v' -> i*6 + 4
                         'w' -> i*6 + 5

instance Show V where
  show (V c i) = if i == 0 then [c] else c : show i

data UnOp = Neg | Exp | Dirac
data BinOp = Add | Sub | Mul | Div | Equal

data RN = Lit Double
        | Inf
        | RNV V
        | Ind Tr
        | UnOp UnOp RN
        | BinOp BinOp RN RN
        | Bernoulli RN (V -> RN)
        | Normal RN RN RN RN (V -> RN)
        | Uniform RN RN (V -> RN)

data En = EV V
data Tr = TV V | Gte RN RN
data Ut = UV V
data Ga = Ga V

type family Eval α where
  Eval E = En
  Eval T = Tr
  Eval U = Ut
  Eval Γ = Ga
  Eval R = RN
  Eval (α ⟶ β) = Eval α -> Eval β
  Eval Unit = ()
  Eval (α × β) = (Eval α, Eval β)

instance Show Tr where
  show (TV v) = show v
  show (Gte x y) = show x ++ " \\geq " ++ show y

data Env γ where
  Emp :: Env Unit
  Cons :: Eval α -> Env γ -> Env (γ × α)

lookUp :: α ∈ γ -> Env γ -> Eval α
lookUp Get (Cons x env) = x
lookUp (Weaken i) (Cons x env) = lookUp i env 

evalRN :: Env γ -> γ ⊢ α -> Eval α
evalRN env (Var i) = lookUp i env
evalRN env (Con (Rl (Incl x))) = Lit x
evalRN env (Con (Rl Indi)) = Ind
evalRN env (Con (Rl Mult)) = BinOp Mul
evalRN env (Con (Rl Divi)) = BinOp Div
evalRN env (Con (Rl Nml))
  = \(x, y) f -> Normal x y (UnOp Neg Inf) Inf (f . RNV)
evalRN env (Con (Rl Uni))
  = \(x, y) f -> Uniform x y (f . RNV)
evalRN env (Con (Rl EqRl)) = \x y -> UnOp Dirac (BinOp Sub x y)
evalRN env (Con (Special GTE)) = Gte
evalRN env (App m n) = evalRN env m (evalRN env n)
evalRN env (Lam m) = \x -> evalRN (Cons x env) m
evalRN env (Fst m) = fst (evalRN env m)
evalRN env (Snd m) = snd (evalRN env m)
evalRN env TT = ()
evalRN env (Pair m n) = (evalRN env m, evalRN env n)

-- >>> evalRN Emp $ clean $ evalβ $ expectedValue $ App l1 (u 1) >>= Lam (η (App (hmorph (App height vlad)) (Var Get)))
-- \frac{\int_{0.0}^{100.0}\left(\frac{1}{100.0 - 0.0}\int_{-\infty}^{\infty}\left(\frac{1}{3.0\sqrt{2\pi}}e^{-\frac{(y - 68.0)^2}{2 * (3.0)^2}} * (\int_{0.0}^{100.0}\left(\frac{1}{100.0 - 0.0}\int_{-\infty}^{\infty}\left(\frac{1}{3.0\sqrt{2\pi}}e^{-\frac{(u - 68.0)^2}{2 * (3.0)^2}} * (\mathds{1}(u \geq z) * (\delta((u - y)) * \delta((z - x))))\right)du\right)dz * y)\right)dy\right)dx}{\int_{0.0}^{100.0}\left(\frac{1}{100.0 - 0.0}\int_{-\infty}^{\infty}\left(\frac{1}{3.0\sqrt{2\pi}}e^{-\frac{(y - 68.0)^2}{2 * (3.0)^2}} * \int_{0.0}^{100.0}\left(\frac{1}{100.0 - 0.0}\int_{-\infty}^{\infty}\left(\frac{1}{3.0\sqrt{2\pi}}e^{-\frac{(u - 68.0)^2}{2 * (3.0)^2}} * (\mathds{1}(u \geq z) * (\delta((u - y)) * \delta((z - x))))\right)du\right)dz\right)dy\right)dx}

helpShow :: RN -> V -> String
helpShow (RNV i) j = show i
helpShow (Ind i) j = "\\mathds{1}(" ++ show i ++ ")"
helpShow (Lit d) i = show d
helpShow Inf i = "\\infty"
helpShow (UnOp Neg x) i = "-" ++ helpShow x i
helpShow (UnOp Exp x) i = "e^{" ++ helpShow x i ++ "}"
helpShow (UnOp Dirac x) i = "\\delta(" ++ helpShow x i ++ ")"
helpShow (BinOp Add x y) i = "(" ++ helpShow x i ++ " + " ++ helpShow y i ++ ")"
helpShow (BinOp Mul x y) i = "(" ++ helpShow x i ++ " * " ++ helpShow y i ++ ")"
helpShow (BinOp Div x y) i
  = "\\frac{" ++ helpShow x i ++ "}{" ++ helpShow y i ++ "}"
helpShow (BinOp Sub x y) i
  = "(" ++ helpShow x i ++ " - " ++ helpShow y i ++ ")"
helpShow (BinOp Equal x y) i
  = "(" ++ helpShow x i ++ " = " ++ helpShow y i ++ ")"
helpShow (Bernoulli x f) i
  = "\\begin{cases}" ++ helpShow x i ++ " * " ++ helpShow (f i) (succ i)
  ++ " &" ++ show i ++ " = \\top\\\\" ++ helpShow (BinOp Sub (Lit 1) x) i
  ++ " * " ++ helpShow (f i) (succ i) ++ " &" ++ show i
  ++ " = \\bot\\end{cases}"
helpShow (Normal x y z w f) i
  = "\\int_{" ++ helpShow z i ++ "}^{" ++ helpShow w i ++ "}"
  ++ "\\left(\\frac{1}{" ++ helpShow y i ++ "\\sqrt{2\\pi}}e^{-\\frac{("
  ++ show i ++ " - " ++ helpShow x i ++ ")^2}{2 * (" ++ helpShow y i
  ++ ")^2}} * " ++ helpShow (f i) (succ i) ++ "\\right)d" ++ show i
helpShow (Uniform x y f) i
  = "\\int_{" ++ helpShow x i ++ "}^{" ++ helpShow y i ++ "}"
  ++ "\\left(\\frac{1}{" ++ helpShow y i ++ " - " ++ helpShow x i  ++ "}"
  ++ helpShow (f i) (succ i) ++  "\\right)d" ++ show i

instance Show RN where
  show x = helpShow x (toEnum 0)

rToDouble :: RN -> Double
rToDouble (Lit x) = x
rToDouble (UnOp Neg x) = -(rToDouble x)
rToDouble (BinOp Add x y) = rToDouble x + rToDouble y
rToDouble (BinOp Mul x y) = rToDouble x * rToDouble y
rToDouble (BinOp Sub x y) = rToDouble x - rToDouble y

instance Num RN where
  x + y = BinOp Add x y
  x * y = BinOp Mul x y
  abs = \case
    Lit x -> Lit x
    UnOp Neg x -> abs x
    UnOp Dirac x -> UnOp Dirac (abs x)
    BinOp Add x y -> BinOp Add (abs x) (abs y)
    BinOp Mul x y -> BinOp Mul (abs x) (abs y)
    x -> x
  signum = \case
    UnOp Dirac x -> Lit 1
    x -> Lit $ rToDouble x
  fromInteger x = Lit (fromInteger x)
  negate = UnOp Neg
 
-- data PP α = PP { expect :: (α -> RN) -> RN }

-- instance Functor PP where
--   fmap f (PP m) = PP $ \k -> m (k . f)
-- instance Applicative PP where
--   pure = PP . flip ($)
--   (<*>) = ap
-- instance Monad PP where
--   return x = PP (\k -> k x)
--   (PP a) >>= f = PP (\k -> a $ \x -> expect (f x) k) 

-- pf :: Sampleable a => PP a -> a -> RN
-- pf (PP p) y = p (equal y)

-- class Sampleable a where
--   equal :: a -> a -> RN

-- instance Sampleable RN where
--   equal x y = UnOp Dirac (x - y)

-- instance (Sampleable a, Sampleable b) => Sampleable (a, b) where
--   equal (x1, x2) (y1, y2) = equal x1 y1 * equal x2 y2
