{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Models.RN where

import Control.Monad (ap)
import Fragments.RSA
import TLC.Terms

data Discrete1P = Bernoulli
data Continuous2P = Normal | Uniform

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
data BinOp = Add | Sub | Mul | Equal

data RN = Lit Double
        | Inf
        | RNV V
        | Ind V
        | UnOp UnOp RN
        | BinOp BinOp RN RN
        | Integral1 Discrete1P RN (V -> RN)
        | Integral2 Continuous2P RN RN RN RN (V -> RN)

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
helpShow (BinOp Sub x y) i = "(" ++ helpShow x i ++ " - " ++ helpShow y i ++ ")"
helpShow (BinOp Equal x y) i = "(" ++ helpShow x i ++ " = " ++ helpShow y i ++ ")"
helpShow (Integral1 Bernoulli x f) i = "\\begin{cases}" ++ helpShow x i ++ " * " ++ helpShow (f i) (succ i) ++ " &" ++ show i ++ " = \\top\\\\" ++ helpShow (BinOp Sub (Lit 1) x) i ++ " * " ++ helpShow (f i) (succ i) ++ " &" ++ show i ++ " = \\bot\\end{cases}"
helpShow (Integral2 Normal x y z w f) i = "\\int_{" ++ helpShow z i ++ "}^{" ++ helpShow w i ++ "}" ++ "\\left(\\frac{1}{" ++ helpShow y i ++ "\\sqrt{2\\pi}}e^{-\\frac{(" ++ show i ++ " - " ++ helpShow x i ++ ")^2}{2 * (" ++ helpShow y i ++ ")^2}} * " ++ helpShow (f i) (succ i) ++ "\\right)d" ++ show i
helpShow (Integral2 Uniform x y z w f) i = "\\int_{" ++ helpShow z i ++ "}^{" ++ helpShow w i ++ "}" ++ "\\left(\\begin{cases}\\frac{" ++ helpShow (f i) (succ i) ++ "}{" ++ helpShow y i ++ " - " ++ helpShow x i  ++ "} &" ++ helpShow x i ++ " \\le " ++ show i ++ " \\le " ++ helpShow y i ++ "\\\\0 &o.w.\\end{cases}\\right)d" ++ show i

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
 
data PP α = PP { expect :: (α -> RN) -> RN }

instance Functor PP where
  fmap f (PP m) = PP $ \k -> m (k . f)
instance Applicative PP where
  pure = PP . flip ($)
  (<*>) = ap
instance Monad PP where
  return x = PP (\k -> k x)
  (PP a) >>= f = PP (\k -> a $ \x -> expect (f x) k) 

pf :: Sampleable a => PP a -> a -> RN
pf (PP p) y = p (equal y)

class Sampleable a where
  equal :: a -> a -> RN

instance Sampleable RN where
  equal x y = UnOp Dirac (x - y)

instance (Sampleable a, Sampleable b) => Sampleable (a, b) where
  equal (x1, x2) (y1, y2) = equal x1 y1 * equal x2 y2
