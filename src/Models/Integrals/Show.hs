{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
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
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp, (**))
import TLC.Terms hiding ((>>), u, Con)
import Text.Pretty.Math

import Models.Integrals.Types
import qualified Algebra.Expression as E

--------------------------------------------------------------------------------
-- | Showing stuff


class ShowableContext γ where
  -- This stupidifying interface is dictated by lack of "impredicative polymorphism"
  varsForCtx :: [String] -> Vars γ
  restOfVars :: [String] -> [String]

instance ShowableContext 'Unit where
  varsForCtx _ = \case
  restOfVars = id

instance ShowableContext γ => ShowableContext (γ × α) where
  varsForCtx [] = error "varsForCtx: panic: no more fresh variables"
  varsForCtx (f:fs) = \case
    Get -> f
    Weaken x -> varsForCtx fs x
  restOfVars = drop 1 . restOfVars @γ

showProg :: forall γ. ShowableContext γ => P γ -> Doc
showProg = showP (restOfVars @γ freshes) (varsForCtx freshes)

-- instance (Pretty a, ShowableContext γ) => Show (P γ a) where
--   show = showProg Mathematica

-- class RatLike a => Pretty a where
--   pretty :: a -> Doc
-- instance (RealFloat a, RatLike a, Show a) => Pretty (Complex a) where
--   pretty (a :+ b) | b < 10e-15 = case show a of
--                       "1.0" -> one
--                       "0.0" -> zero
--                       "-1.0" -> negate one
--                       x -> text x
--                   | otherwise = text (show a ++ "+" ++ show b ++ "i")


type Vars γ  = forall v. Available v γ -> String

(+!) :: String -> Vars γ -> Vars (γ × d)
f +! v = \case Get -> f
               Weaken i -> v i

-- instance (RatLike a, Pretty a, ShowableContext γ) => Show (Expr γ a) where
--   show e = showExpr (varsForCtx freshes) e Maxima

showRet :: Vars γ -> Ret γ -> Doc
showRet v = E.eval (showElem v)

showExpr :: Vars γ -> Expr γ -> Doc
showExpr v = A.eval (E.eval (\case)  . fromNumber ) (text . v) 

showElem :: Vars γ -> Elem γ -> Doc
showElem vs (Supremum m es) = showSupremum m [showRet vs p | p <- es]
showElem vs (Vari v) = text (vs v)

-- showCoef :: forall γ. Vars γ -> Coef γ -> Doc
-- showCoef v (Coef c) = LC.eval pretty (exp . showPoly v) c

-- showPoly :: Vars γ -> Poly γ -> Doc
-- showPoly v = eval (showCoef v) (showElem v)

-- showDumb :: Pretty a => Vars γ -> Dumb (Poly γ) -> Doc
-- showDumb v = evalDumb (showPoly v)

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

showCond :: Vars γ -> Cond γ -> Doc
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
      
showBounds :: Vars γ -> Dir -> [Expr γ] -> Doc
showBounds v lo xs = showSupremum lo (map (showExpr v) xs)

when :: Monoid p => [a] -> p -> p
when [] _ = mempty
when _ x = x

showP :: [String] -> Vars γ -> P γ -> Doc
showP [] _ = error "showP: ran out of freshes"
showP fs@(f:fsRest) v = \case
  Done -> one
  Scale k e -> showRet v k * showP fs v e
  Add p1 p2 -> showP fs v p1 + showP fs v p2
  Mul p1 p2 -> showP fs v p1 * showP fs v p2
  Power p (Number k) -> showP fs v p ** E.eval (\case) k
  Integrate (Domain los his) e -> withStyle $ \st -> 
    let body = showP fsRest (f +! v) e
        dom :: Doc
        dom = text f <> text ", " <>
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

mathematica :: ShowableContext γ => P γ -> IO ()
mathematica = putStrLn . render Mathematica . showProg  

latex :: ShowableContext γ => P γ -> IO ()
latex = putStrLn . render LaTeX .showProg

maxima :: ShowableContext γ => P γ -> IO ()
maxima = putStrLn . render Maxima . showProg
