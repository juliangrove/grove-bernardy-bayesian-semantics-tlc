{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RebindableSyntax #-}

module Models.Integrals.Approx4 (toGnuPlot, approxTop, KnownContext(..), Env, FUN) where

import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp, toInteger, (**))
import Algebra.Linear.Vector
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M
import Data.Foldable hiding (sum)
import qualified Algebra.Expression as E

import Models.Integrals.Types

type family Env γ where
  Env 'Unit = ()
  Env (a ':× b) = (Env a, Env b)
  Env 'R = Double

type RR = Double

evalP :: Ret 'Unit -> RR
evalP = E.eval $ \case
     Supremum d x -> (case d of Min -> minimum; Max -> maximum) (fmap evalP x)
     Vari v -> case v of

evalX :: Expr  'Unit -> RR
evalX = A.eval evalNumber (\case)

size__ :: Int
size__ = 128

domLo, domHi :: RR
domLo = 65 - 15
domHi = 63 + 15

type WithCache a = State (Map (P ('Unit × 'R)) (Vec RR)) a

point :: Int -> RR
point i = domLo + (domHi - domLo) * (fromInt i/ fromInt (size__))


fromInt :: Ring a => Int -> a
fromInt = fromInteger . toInteger

rng :: [Int]
rng = [0..size__]


ptsrng :: [RR]
ptsrng = fmap point rng

pts :: Vec RR
pts = fromList ptsrng

-- >>> pts
-- Vec [50.0,51.75,53.5,55.25,57.0,58.75,60.5,62.25,64.0,65.75,67.5,69.25,71.0,72.75,74.5,76.25,78.0]

resolution :: RR
resolution = (domHi - domLo) / fromInt size__

-- >>> resolution
-- 1.75

approxIntegralsWithCache :: P 'Unit -> WithCache RR
approxIntegralsWithCache = 
  let aa = approxIntegralsWithCache
  in \case
      Done -> pure one
      Power a k -> (** evalNumber k) <$> aa a
      Add a b -> (+) <$> aa a <*> aa b
      Mul a b -> (*) <$> aa a <*> aa b
      Integrate d e -> do
        cachedFun <- gets (M.lookup e)
        p <- case cachedFun of
          Nothing -> do
            s <- flip traverse pts $ \x -> do
                   y <- aa (substP (\case Get -> A.constant (Number (E.Flt x)) ; Weaken v -> A.var v) e)
                   pure y
            modify (M.insert e s)
            pure s
          Just p -> pure p
        let (Domain (maximum . fmap evalX  -> lo) (minimum . fmap evalX -> hi)) = d
        pure $ (resolution *^) $ sum [ y | (x, y) <- zip ptsrng (toList p), x > lo, x < hi]
      Scale k x -> (evalP k *) <$> aa x
      Cond (IsNegative c) e -> if A.eval @RR evalNumber (\case) c <= 0 then aa e else pure 0
      Cond (IsZero _) _ -> error "approxIntegrals: equality not eliminated?"

type family FUN γ x where
  FUN 'Unit x = x
  FUN (a ':× 'R) x = Vec (FUN a x)

class KnownContext (γ :: Type) where
  approxFUN :: P γ -> WithCache (FUN γ RR)
instance KnownContext 'Unit where
  approxFUN x = approxIntegralsWithCache x
instance KnownContext γ => KnownContext (γ × 'R) where
  approxFUN e = flip traverse (fromList $ (point <$> rng)) $ \x ->
                approxFUN $
                flip substP e $ \case
                   Get -> A.constant (Number (E.Flt x))
                   Weaken v -> A.var v

runWithCache :: WithCache x -> x
runWithCache e = fst (runState e M.empty)

approxTop :: KnownContext γ => P γ -> FUN γ RR
approxTop e = runWithCache  (approxFUN e)


toGnuPlot :: String -> Vec (Vec Double) -> IO ()
toGnuPlot fn x = writeFile fn
            $   unlines $ fmap (unwords . fmap show) $
            (0 : ptsrng) :
            [ point i : toList (x ! i)  | i <- rng ]
