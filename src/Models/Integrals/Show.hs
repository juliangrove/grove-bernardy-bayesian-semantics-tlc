{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
module Models.Integrals.Show where

import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import qualified Algebra.Morphism.LinComb as LC
import Algebra.Morphism.Polynomial.Multi hiding (constPoly)
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp)
import TLC.Terms hiding ((>>), u, Con)
import qualified Models.Field
import Text.Pretty.Math

import Models.Integrals.Types

--------------------------------------------------------------------------------
-- | Showing stuff

class ShowableContext γ where
  -- This stupidifying interface is dictated by lack of "impredicative polymorphism"
  varsForCtx :: [String] -> Vars γ
  restOfVars :: [String] -> [String]

instance ShowableContext () where
  varsForCtx _ = \case
  restOfVars = id

instance ShowableContext γ => ShowableContext (γ,α) where
  varsForCtx [] = error "varsForCtx: panic: no more fresh variables"
  varsForCtx (f:fs) = \case
    Here -> f
    There x -> varsForCtx fs x
  restOfVars = drop 1 . restOfVars @γ

showProg :: forall γ a. Pretty a => ShowableContext γ => P γ a -> Doc
showProg = showP (restOfVars @γ freshes) (varsForCtx freshes)

-- instance (Pretty a, ShowableContext γ) => Show (P γ a) where
--   show = showProg Mathematica


instance Pretty Rat where
  pretty = Models.Field.eval

type Vars γ  = forall v. Available v γ -> String

(+!) :: String -> Vars γ -> Vars (γ, d)
f +! v = \case Here -> f
               There i -> v i

-- instance (RatLike a, Pretty a, ShowableContext γ) => Show (Expr γ a) where
--   show e = showExpr (varsForCtx freshes) e Maxima

showExpr :: DecidableZero a => Ord a => Pretty a => Vars γ -> Expr γ a -> Doc
showExpr v = A.eval pretty (text . v) 

showElem :: Pretty a => Vars γ -> Elem γ a -> Doc
showElem vs (Supremum m es) = showSupremum m [showPoly vs p | p <- es]
showElem vs (Vari v) = text (vs v)
showElem vs (CharFun e) = showCond' (IsNegative (showPoly vs e))

showCoef :: forall γ a. Pretty a => Vars γ -> Coef γ a -> Doc
showCoef v (Coef c) = LC.eval pretty (exp . showPoly v) c

showPoly :: Pretty x => Vars γ -> Poly γ x -> Doc
showPoly v = eval (showCoef v) (showElem v)

showDumb :: Pretty a => Vars γ -> Dumb (Poly γ a) -> Doc
showDumb v = evalDumb (showPoly v)

-- instance (Pretty a, ShowableContext γ) => Show (Dumb (Poly γ a)) where
--   show x = showDumb (varsForCtx freshes) x Mathematica

indicator :: [Doc] -> Doc
indicator x = withStyle $ \case
      Mathematica -> function' "Boole" x
      Maxima -> function' "charfun"  x
      LaTeX -> function' "mathbb{1}"  x

showCond' :: Cond' Doc -> Doc
showCond' c0 = withStyle $ \st -> case c0 of
  (IsNegative c') -> case st of
      Mathematica -> indicator [c' <> text " ≤ 0"]
      Maxima -> indicator [c' <> text " <= 0"]
      LaTeX -> indicator [c' <> text " \\leq 0"]
  (IsZero c') -> case st of
      LaTeX -> function "diracDelta" c'
      _ -> function "DiracDelta" c'

showCond :: (Pretty α, RatLike α) => Vars γ -> Cond γ α -> Doc
showCond v = showCond' . fmap (showExpr v)

foldrMonoid :: (p -> p -> p) -> p -> [p] -> p
foldrMonoid _ k [] = k
foldrMonoid f _ xs = foldr1 f xs

showSupremum :: Dir -> [Doc] -> Doc
showSupremum dir xs = 
  let extremum = withStyle $ \case
        Mathematica -> text "Infinity"
        Maxima -> text "inf"
        LaTeX -> function' "infty" []
      op = case dir of
          Min -> (\x y -> function' "min" [x,y])
          Max -> (\x y -> function' "max" [x,y])
  in foldrMonoid op ((case dir of Max -> negate; Min -> id) extremum) xs
      
showBounds :: Vars γ -> Dir -> [Expr γ Rat] -> Doc
showBounds v lo xs = showSupremum lo (map (showExpr v) xs)

when :: Monoid p => [a] -> p -> p
when [] _ = mempty
when _ x = x

showP :: Pretty a => [String] -> Vars γ -> P γ a -> Doc
showP [] _ = error "showP: ran out of freshes"
showP fs@(f:fsRest) v = \case
  Ret e -> showPoly v e
  Add p1 p2 -> showP fs v p1 + showP fs v p2
  Div p1 p2 -> showP fs v p1 / showP fs v p2
  Integrate (Domain cs los his) e -> withStyle $ \st -> 
    let body = showP fsRest (f +! v) e
        dom :: Doc
        dom =
          (when cs $ indicator (map (showCond (f +! v)) cs) <> text ", ") <>
          text f <> text ", " <>
          showBounds v Max los <> text ", " <>
          showBounds v Min his
    in case st of
         LaTeX -> text "\\int_{" <> showBounds v Max los <> text "}^{" <>
                  showBounds v Min his <> text "}" <>
                  showP fsRest (f +! v) e <>
                  text "\\,d" <> text f 
         _ -> function' "integrate"
              [body, (if st == Mathematica then braces else id) dom]
  Cond c e -> showCond v c * showP fs v e

mathematica :: Pretty a => ShowableContext γ => P γ a -> IO ()
mathematica = putStrLn . render Mathematica . showProg  

latex :: Pretty a => ShowableContext γ => P γ a -> IO ()
latex = putStrLn . render LaTeX .showProg

maxima :: Pretty a => ShowableContext γ => P γ a -> IO ()
maxima = putStrLn . render Maxima . showProg
