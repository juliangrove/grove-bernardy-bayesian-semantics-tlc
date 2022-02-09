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

module Models.Integrals.Approx4  where

import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp, toInteger)
import qualified Models.Field
import Algebra.Linear.Vector
import Data.Complex
import qualified Algebra.Morphism.Polynomial.Multi as Multi
import Algebra.Morphism.Polynomial.Multi hiding (constPoly)
import qualified Algebra.Morphism.LinComb as LC
import Control.Applicative
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M
import Data.Foldable hiding (sum)

import Models.Integrals.Types

type family Env γ where
  Env 'Unit = ()
  Env (a ':× b) = (Env a, Env b)
  Env 'R = Double

type RR = Double


evalC :: Coef 'Unit -> RR
evalC (Coef c) = LC.eval (\x -> Models.Field.eval @RR x) (exp . evalP) c

evalP :: Poly 'Unit -> RR
evalP = Multi.eval evalC evalE 

evalE :: Elem 'Unit -> RR
evalE = \case
  Supremum dir es -> case dir of
    Min ->  foldr (min) (( 1/0)) (evalP <$> es)
    Max ->  foldr (max) ((-1/0)) (evalP <$> es)
  Vari x -> case x of
  CharFun x -> if evalP x >= 0 then 1 else 0 

evalX :: Expr  'Unit -> RR
evalX = A.eval Models.Field.eval (\case)

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
      Add a b -> (+) <$> aa a <*> aa b
      Div a b -> (/) <$> aa a <*> aa b
      Integrate d e -> do
        cachedFun <- gets (M.lookup e)
        p <- case cachedFun of
          Nothing -> do
            s <- flip traverse pts $ \x -> do
                   y <- aa (substP (\case Get -> A.constant (Models.Field.Con (toRational x)) ; Weaken v -> A.var v) e)
                   pure y
            modify (M.insert e s)
            pure s
          Just p -> pure p
        let (Domain (maximum . fmap evalX  -> lo) (minimum . fmap evalX -> hi)) = d
        pure $ (resolution *^) $ sum [ y | (x, y) <- zip ptsrng (toList p), x > lo, x < hi]
      Ret x -> pure (evalP x)
      Cond (IsNegative c) e -> if A.eval @RR Models.Field.eval (\case) c <= 0 then aa e else pure 0
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
                   Get -> A.constant (Models.Field.Con (toRational x))
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
