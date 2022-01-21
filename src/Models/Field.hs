{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RebindableSyntax #-}
module Field where

import Data.Ratio
import Algebra.Classes
import Prelude hiding (Num(..),Fractional(..),recip)

data BinOp = Plus | Times

data Fld x = R Rational | Inject x | Op BinOp (Fld x) (Fld x) | Pow (Fld x) Rational

instance Additive (Fld x) where
  zero = R zero
  R x + R y = R (x + y)
  x + y = Op Plus x y

instance Multiplicative (Fld x) where
  one = R one
  R x * R y = R (x * y)
  x * y = Op Times x y

instance Group (Fld x) where
  negate = Op Times (negate one)

instance Division (Fld x) where
  recip x = Pow x (-1)

instance AbelianAdditive (Fld x)

instance Ring (Fld x)
instance Module (Fld x) (Fld x) where
  (*^) = (*)

instance Field (Fld x)

showR :: Int -> Rational -> ShowS
showR p (\x -> (numerator x, denominator x) -> (num, den))
  = case (num, den) of
      (0, _) -> showString "0"
      (_, 1) -> showsPrec p num
      (_, _) -> showParen (p > 6) (showsPrec 6 num . showString "/" . showsPrec 5 den)

instance Show x => Show (Fld x) where
  showsPrec p = \case 
       (R x) -> showR p x
       (Inject x) -> showsPrec p x
       Pow x e -> showsPrec 8 x . showString "^" . showR 10 e
       Op op x y -> showParen (p > opPrec op) $ showsPrec (opPrec op) x . showString (showOp op) . showsPrec (opPrec op + 1) y

opPrec :: BinOp -> Int
opPrec = \case
  Plus -> 5
  Times -> 6

showOp :: BinOp -> String
showOp = \case
  Plus -> "+"
  Times -> "*"

ex1 :: Fld String
ex1 = Inject "pi" + 6

-- >>> ex1
-- "pi"+6 % 1

ex2 :: Fld String
ex2 = Inject "pi" / 2

-- >>> ex2
-- "pi"*2^(-1)


ex3 :: Fld String
ex3 = Inject "pi" `Pow` (1/2)

-- >>> ex3
-- "pi"^(1/2)

