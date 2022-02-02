{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module Models.Integrals (module Export, module Models.Integrals) where

import Models.Integrals.Optimizer as Export
import Models.Integrals.Conversion as Export
import Models.Integrals.Show as Export
import Models.Integrals.Types as Export (P, Cond, Rat, lessThan, greaterThan, Available(..))  
import Models.Integrals.Types  


-- import Data.Ratio
import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp)
import TLC.Terms hiding ((>>), u, Con)
import Algebra.Linear ((*<))

--------------------------------------------------------------------------------
-- | Top-level Entry points

-- | Take typed descriptions of real numbers onto integrators 
simplify :: [Cond (Eval γ) Rat] -> (γ ⊢ 'R) -> P (Eval γ) Rat
simplify cs = normalise . cleanConds [] . conds_ cs . normalise . evalP' . normalForm

-- | Take typed descriptions of functions onto integrators with a free var
simplifyFun :: [Cond ((), Rat) Rat] -> 'Unit ⊢ ('R ⟶ 'R) -> P ((), Rat) Rat
simplifyFun cs = simplify cs . absInversion

-- | Take typed descriptions of functions onto integrators with two free vars
simplifyFun2 :: [Cond (((), Rat), Rat) Rat] -> 'Unit ⊢ ('R ⟶ 'R ⟶ 'R) -> (P (((), Rat), Rat) Rat)
simplifyFun2 cs = simplify cs . absInversion . absInversion

--------------------------------------------------------------------------------
-- | Examples

example0 :: P () Rat
example0 = Integrate full $ retPoly $ constPoly 10 + varPoly Here

-- >>> maxima $ example0
-- integrate(10 + x, x, -inf, inf)

exampleInEq :: P () Rat
exampleInEq = Integrate full $
              Cond (IsNegative (A.constant 7 - A.var Here)) $
              retPoly $  constPoly 10 + varPoly Here

-- >>> maxima $ exampleInEq
-- integrate(charfun(7 - x <= 0)*(10 + x), x, -inf, inf)

-- >>> maxima $ normalise exampleInEq
-- integrate(10 + x, x, 7, inf)

exampleEq :: P () Rat
exampleEq = Integrate full $
            Cond (IsZero (A.constant 7 - A.var Here)) $
            retPoly $  constPoly 10 + varPoly Here

-- >>> mathematica $ exampleEq
-- Integrate[DiracDelta[7 - x]*(10 + x), {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise exampleEq
-- 17

example :: P () Rat
example = Integrate full $ Integrate full $
          Cond (IsNegative (3 *< A.var (There Here) + 2 *< A.var (Here))) $
          Cond (IsNegative (A.var (There Here))) one

-- >>> mathematica $ example
-- Integrate[Integrate[Boole[2*y + 3*x ≤ 0]*Boole[x ≤ 0], {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise example
-- Integrate[1/(1/(-3/2*x + Infinity)), {x, -Infinity, 0}]

example1 :: P () Rat
example1 = Integrate full $ Integrate full $
           Cond (IsZero (A.constant 4 + A.var (There Here) - A.var Here)) one

-- >>> mathematica $ example1
-- Integrate[Integrate[DiracDelta[4 - y + x], {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> maxima $ normalise example1
-- 1/(1/(inf + inf))

example2 :: P () Rat
example2 = Integrate full $
           Integrate (Domain [] [A.constant 1 + A.var Here] []) $
           Cond (IsZero (A.constant 4 + 2 *< A.var (There Here) - A.var Here) ) $
           retPoly $ varPoly Here

-- >>> mathematica $ example2
-- Integrate[Integrate[DiracDelta[4 - y + 2*x]*y, {y, 1 + x, Infinity}], {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise example2
-- Integrate[4 + 2*x, {x, -3, Infinity}]

example3 :: P () Rat
example3 = Integrate full $
           Integrate full $
           Cond (IsNegative (A.constant 3 - A.var Here)) $
           Cond (IsZero (A.constant 4 + A.var (There Here) - A.var Here)) $
           retPoly $
           constPoly 2 + (varPoly Here) ^+ 2 + 2 *< varPoly (There Here)

-- >>> mathematica $ example3
-- Integrate[Integrate[Boole[3 - y ≤ 0]*DiracDelta[4 - y + x]*(2 + y^2 + 2*x), {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise example3
-- Integrate[18 + 10*x + x^2, {x, -1, Infinity}]

example4a :: P () Rat
example4a = Integrate (Domain [] [zero] [A.constant 1]) one

-- >>> mathematica $ normalise example4a
-- 1

-- >>> mathematica $ approxIntegrals 4 (normalise example4a)
-- 1


example4 :: P () Rat
example4 = Integrate full $
           Integrate full $
           Cond (IsNegative (A.constant (-3) - A.var Here)) $
           Cond (IsNegative (A.constant (-3) + A.var Here)) $
           Cond (IsZero (A.var  (There Here) - A.var Here)) $
           retPoly $
           exponential $ negate $ varPoly Here ^+2 + (varPoly (There Here) ^+ 2)

-- >>> mathematica $ example4
-- Integrate[Integrate[Boole[-3 - y ≤ 0]*Boole[-3 + y ≤ 0]*DiracDelta[-y + x]*Exp[-y^2 - x^2], {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise example4
-- Integrate[Exp[-2*x^2], {x, -3, 3}]

-- >>> mathematica $ approxIntegrals 16 $ normalise example4
-- 1.253346416637889


example5 :: P ((),Rat) Rat
example5 = Integrate full $
           Cond (IsNegative (A.constant (-3) - A.var Here)) $
           Cond (IsNegative (A.constant (-3) + A.var Here)) $
           retPoly $
           exponential $ negate $ varPoly Here ^+2 + (varPoly (There Here) ^+ 2)

-- >>> mathematica example5
-- Integrate[Boole[-3 - y ≤ 0]*Boole[-3 + y ≤ 0]*Exp[-y^2 - x^2], {y, -Infinity, Infinity}]

-- >>> mathematica $ normalise example5
-- Integrate[Exp[-y^2 - x^2], {y, -3, 3}]

-- >>> mathematica $ approxIntegrals 8 $ normalise example5 
-- 9.523809523809527e-2*Exp[-9.0 - x^2] + 0.8773118952961091*Exp[-7.681980515339462 - x^2] + 0.8380952380952381*Exp[-4.499999999999999 - x^2] + 0.8380952380952381*Exp[-4.499999999999997 - x^2] + 1.0851535761614692*Exp[-1.318019484660537 - x^2] + 1.0851535761614692*Exp[-1.3180194846605355 - x^2] + 1.180952380952381*Exp[-4.930380657631324e-32 - x^2]

