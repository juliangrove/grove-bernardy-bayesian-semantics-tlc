{-# LANGUAGE RecordWildCards #-}
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

module Models.Integrals.Approx4 (toGnuPlot1d, toGnuPlot, approxTop, KnownContext(..), Env, FUN, PlotOptions(..)) where

import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp, toInteger, (**))
import Algebra.Linear.Vector
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M
import Data.Foldable hiding (sum, product)
import qualified Algebra.Expression as E
import System.Directory (doesFileExist)
import System.IO

import Models.Integrals.Types

type family Env γ where
  Env 'Unit = ()
  Env (a ':× b) = (Env a, Env b)
  Env R = Double

type RR = Double

evalP :: Ret 'Unit -> RR
evalP = E.eval $ \case
     Supremum d x -> (case d of Min -> minimum; Max -> maximum) (fmap evalP x)
     Vari v -> case v of

evalX :: Expr  'Unit -> RR
evalX = A.eval evalNumber (\case)

data PlotOptions = PlotOptions {
  plotResolution :: Int,
  plotDomainLo, plotDomainHi :: RR
  }
fromInt :: Ring a => Int -> a
fromInt = fromInteger . toInteger

data Eval'Options = Eval'Options {
  size__ :: Int,
  domHi, domLo :: RR,
  resolution :: RR,
  point :: Int -> RR,
  rng :: [Int],
  pts :: Vec RR,
  ptsrng :: [RR]
  }

evalOptions :: PlotOptions -> Eval'Options
evalOptions PlotOptions{..} = Eval'Options {..} where
   size__ = plotResolution
   domHi = plotDomainHi
   domLo = plotDomainLo
   pts = fromList ptsrng
   ptsrng = fmap point rng
   rng = [0..size__]
   resolution :: RR
   resolution = (domHi - domLo) / fromInt size__
   point :: Int -> RR
   point i = domLo + (domHi - domLo) * (fromInt i/ fromInt (size__))
  

type WithCache a = State (Map (P ('Unit × R)) (Vec RR)) a
-- the state maps expressions to vector of samples


-- >>> pts (evalOptions (PlotOptions 16 50 80))
-- Vec [50.0,51.875,53.75,55.625,57.5,59.375,61.25,63.125,65.0,66.875,68.75,70.625,72.5,74.375,76.25,78.125,80.0]

-- >>> resolution (evalOptions (PlotOptions 16 50 80))
-- 1.875

approxIntegralsWithCache :: Eval'Options -> P 'Unit -> WithCache RR
approxIntegralsWithCache options@Eval'Options{..} = 
  let aa = approxIntegralsWithCache options
  in \case
      Done k -> pure (evalP k)
      Add a b -> (+) <$> aa a <*> aa b
      Power a k -> (** evalNumber k) <$> aa a
      Mul as -> product <$> traverse aa as
      Integrate d e -> do
        cachedFun <- gets (M.lookup e)
        p <- case cachedFun of
          Nothing -> do
            s <- flip traverse pts $ \x -> do
              -- e has exactly one free variable. We substitute this
              -- free variable by the point at which we're sampling in
              -- the whole domain.
              y <- aa (substP (\case Get -> A.constant (Number (E.Flt x)) ; Weaken v -> A.var v) e)
              -- y is now the set of samples for the expression e.
              pure y
            modify (M.insert e s)
            pure s
          Just p -> pure p
        let (Domain (maximum . fmap evalX  -> lo) (minimum . fmap evalX -> hi)) = d
        pure $ (resolution *^) $ sum [ y | (x, y) <- zip ptsrng (toList p), x > lo, x < hi]
      Cond (IsNegative c) e -> if A.eval @RR evalNumber (\case) c <= 0 then aa e else pure 0
      Cond (IsZero _) _ -> error "approxIntegrals: equality not eliminated?"

type family FUN γ x where
  FUN 'Unit x = x
  FUN (a ':× R) x = Vec (FUN a x)

class KnownContext (γ :: Type) where
  approxFUN :: Eval'Options -> P γ -> WithCache (FUN γ RR)
instance KnownContext 'Unit where
  approxFUN o x = approxIntegralsWithCache o x
instance KnownContext γ => KnownContext (γ × R) where
  approxFUN o@Eval'Options{..} e =
    flip traverse (fromList $ (point <$> rng)) $ \x ->
      approxFUN o $
      flip substP e $ \case
         Get -> A.constant (Number (E.Flt x))
         Weaken v -> A.var v

runWithCache :: WithCache x -> x
runWithCache e = fst (runState e M.empty)

approxTop :: KnownContext γ => PlotOptions -> P γ -> FUN γ RR
approxTop o e = runWithCache (approxFUN (evalOptions o) e)



-- writeFileIfChanged :: FilePath -> String -> IO ()
-- writeFileIfChanged fn new = do
--   e <- doesFileExist fn
--   old <- if e
--     then do x <- readFile fn
--             case Data.Foldable.length x of -- force reading the whole file before we write something back to it.
--               0 -> pure Nothing
--               _ -> pure (Just x)
--     else pure Nothing
--   when (old /= Just new) $
--     writeFile fn new

  

toGnuPlot :: PlotOptions -> String -> Vec (Vec Double) -> IO ()
toGnuPlot o fn x = writeFile fn
            $   unlines $ fmap (unwords . fmap show) $
            (0 : ptsrng) :
            [ point i : toList (x ! i)  | i <- rng ]
  where Eval'Options {..} = evalOptions o

toGnuPlot1d :: PlotOptions -> String -> Vec Double -> IO ()
toGnuPlot1d o fn x = writeFile fn
            $   unlines $ fmap (unwords . fmap show) $
            [ [point i ,  (x ! i)]  | i <- rng ]
  where Eval'Options {..} = evalOptions o

