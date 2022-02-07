{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RebindableSyntax #-}

module Models.Field where

-- TODO: de-crappify. This is not a field any more, obvs

import Data.Ratio
import Algebra.Classes
import Prelude hiding (Num(..),Fractional(..),Floating(..),(^))
import Text.Show ()
import Data.Function

instance DecidableZero Fld where
  isZero (Con 0) = True
  isZero _ = False

-- instance Transcendental Fld where
--   pi = Pi

instance Roots Fld where
  root n x = Pow x (recip (fromInteger n))

data BinOp = Plus | Times deriving (Eq, Ord)

data Fld = Con Rational
           | Op BinOp (Fld) (Fld)
           | Pow (Fld) Rational
           | Pi

instance Ord Fld where
  compare = compare `on` eval @Double
instance Eq Fld where
  (==) = (==) `on` eval @Double

eval :: Transcendental x => Fld -> x
eval = \case
  Con c -> fromRational c
  Pow x e -> eval x ^/ e
  Pi -> pi
  Op op (eval -> x) (eval -> y) ->
    case op of
      Times -> x * y
      Plus -> x + y



pattern (:*) :: Fld -> Fld -> Fld
pattern x :* y = Op Times x y

pow :: Fld -> Rational -> Fld
pow (Pow x n) m = Pow x (n * m)
pow x n = Pow x n

instance Additive (Fld) where
  zero = Con zero
  Con x + Con y = Con (x + y)
  x + y
    | x == 0 = y
    | y == 0 = x
    | otherwise = Op Plus x y

instance Multiplicative (Fld) where
  one = Con one
  Con x * Con y = Con (x * y)
  (Con x) * (Con y :* z) = Con (x*y) * z
  x * y | x == zero || y == zero = zero
        | x == one = y
        | y == one = x
        | x == y = pow x 2
        | otherwise = Op Times x y

instance Group (Fld) where
  negate (Con x) = Con (negate x)
  negate x = Op Times (Con (-1)) x

instance Division (Fld) where
  recip (Con x) = Con (recip x)
  recip x = pow x (-1)

instance AbelianAdditive (Fld)

instance Ring (Fld)
instance Scalable (Fld) (Fld) where
  (*^) = (*)

instance Field (Fld)

showR :: Int -> Rational -> ShowS
showR p (\x -> (numerator x, denominator x) -> (num, den))
  = case (num, den) of
      (0, _) -> showString "0"
      (_, 1) -> showsPrec p num
      (_, _) -> showParen (p > 6) (showsPrec 6 num . showString "/" . showsPrec 5 den)

instance Show (Fld) where
  showsPrec p = \case
       Pi -> showString "pi"
       (Con x) -> showR p x
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

ex1 :: Fld
ex1 = Pi + 66.8

-- >>> ex1
-- pi+334/5

-- >>> negate ex1
-- -1*(pi+334/5)


ex2 :: Fld
ex2 = Pi / 2

-- >>> ex2
-- pi*(1/2)


ex3 :: Fld
ex3 = Pi ^ 16

-- >>> ex3
-- "pi"^16

half :: Field a => a
half = 1/2
