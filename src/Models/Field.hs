{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RebindableSyntax #-}
module Models.Field where

import Data.Ratio
import Algebra.Classes
import Prelude hiding (Num(..),Fractional(..),recip,(^))

data BinOp = Plus | Times deriving (Eq,Ord)

data Fld x = Con Rational | Inject x | Op BinOp (Fld x) (Fld x) | Pow (Fld x) Int deriving (Ord,Eq)

pattern (:*) :: forall x. Fld x -> Fld x -> Fld x
pattern x :* y = Op Times x y

pow :: Fld x -> Int -> Fld x
pow (Pow x n) m = Pow x (n*m)
pow x n = Pow x n

instance Eq x => Additive (Fld x) where
  zero = Con zero
  Con x + Con y = Con (x + y)
  x + y
    | x == 0 = y
    | y == 0 = x
    | otherwise = Op Plus x y

instance Eq x => Multiplicative (Fld x) where
  one = Con one
  Con x * Con y = Con (x * y)
  (Con x) * (Con y :* z) = Con (x*y) * z
  x * y | x == zero || y == zero = zero
        | x == one = y
        | y == one = x
        | x == y = pow x 2
        | otherwise = Op Times x y

instance Eq x => Group (Fld x) where
  negate (Con x) = Con (negate x)
  negate x = Op Times (Con (-1)) x

instance Eq x => Division (Fld x) where
  recip (Con x) = Con (recip x)
  recip x = pow x (-1)

instance Eq x => AbelianAdditive (Fld x)

instance Eq x => Ring (Fld x)
instance Eq x => Module (Fld x) (Fld x) where
  (*^) = (*)

instance Eq x => Field (Fld x)

showR :: Int -> Rational -> ShowS
showR p (\x -> (numerator x, denominator x) -> (num, den))
  = case (num, den) of
      (0, _) -> showString "0"
      (_, 1) -> showsPrec p num
      (_, _) -> showParen (p > 6) (showsPrec 6 num . showString "/" . showsPrec 5 den)

instance Show x => Show (Fld x) where
  showsPrec p = \case 
       (Con x) -> showR p x
       (Inject x) -> showsPrec p x
       Pow x e -> showsPrec 8 x . showString "^" . showsPrec 10 e
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
ex1 = Inject "pi" + 66.8

-- >>> ex1
-- "pi"+334/5

-- >>> negate ex1
-- -1*("pi"+334/5)


ex2 :: Fld String
ex2 = Inject "pi" / 2

-- >>> ex2
-- "pi"*(1/2)


ex3 :: Fld String
ex3 = Inject "pi" ^ 16

-- >>> ex3
-- "pi"^16

half :: Field a => a
half = 1/2
