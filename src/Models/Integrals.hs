{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module Models.Integrals (module Export, module Models.Integrals) where

import Models.Integrals.Optimizer as Export
import Models.Integrals.Conversion as Export
import Models.Integrals.Show as Export
import Models.Integrals.Types as Export (P, Cond, Rat, lessThan, greaterThan)  
import Models.Integrals.Types
import Models.Integrals.Approx4 as Export


-- import Data.Ratio
import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp)
import TLC.Terms hiding ((>>), u, Con)

--------------------------------------------------------------------------------
-- | Top-level Entry points

-- | Take typed descriptions of real numbers onto integrators 
simplify :: [Cond γ] -> (γ ⊢ 'R) -> P γ
simplify cs = normalise . cleanConds [] . conds_ cs . normalise . evalP' . normalForm

-- | Take typed descriptions of functions onto integrators with a free var
simplifyFun :: [Cond ('Unit × 'R)] -> 'Unit ⊢ ('R ⟶ 'R) -> P ('Unit × 'R)
simplifyFun cs = simplify cs . absInversion

-- | Take typed descriptions of functions onto integrators with two free vars
simplifyFun2 :: [Cond (('Unit × 'R) × 'R)] -> 'Unit ⊢ ('R ⟶ 'R ⟶ 'R) -> (P (('Unit × 'R) × 'R))
simplifyFun2 cs = simplify cs . absInversion . absInversion

--------------------------------------------------------------------------------
-- | Examples

example0 :: P 'Unit
example0 = Integrate full $ retPoly $ constPoly 10 + varPoly Get

-- >>> maxima $ example0
-- integrate(10 + x, x, -inf, inf)

exampleInEq :: P 'Unit
exampleInEq = Integrate full $
              Cond (IsNegative (A.constant 7 - A.var Get)) $
              retPoly $  constPoly 10 + varPoly Get

-- >>> maxima $ exampleInEq
-- integrate(charfun(7 - x <= 0)*(10 + x), x, -inf, inf)

-- >>> maxima $ normalise exampleInEq
-- integrate(10 + x, x, 7, inf)

exampleEq :: P 'Unit
exampleEq = Integrate full $
            Cond (IsZero (A.constant 7 - A.var Get)) $
            retPoly $  constPoly 10 + varPoly Get

-- >>> mathematica $ exampleEq
-- Integrate[DiracDelta[7 - x]*(10 + x), {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise exampleEq
-- 17

example :: P 'Unit
example = Integrate full $ Integrate full $
          Cond (IsNegative (3 *< A.var (Weaken Get) + 2 *< A.var (Get))) $
          Cond (IsNegative (A.var (Weaken Get))) Done

-- >>> mathematica $ example
-- Integrate[Integrate[Boole[2*y + 3*x ≤ 0]*Boole[x ≤ 0], {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise example
-- Integrate[1/(1/(-3/2*x + Infinity)), {x, -Infinity, 0}]

example1 :: P 'Unit
example1 = Integrate full $ Integrate full $
           Cond (IsZero (A.constant 4 + A.var (Weaken Get) - A.var Get)) Done

-- >>> mathematica $ example1
-- Integrate[Integrate[DiracDelta[4 - y + x], {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> maxima $ normalise example1
-- inf + inf

example2 :: P 'Unit
example2 = Integrate full $
           Integrate (Domain [A.constant 1 + A.var Get] []) $
           Cond (IsZero (A.constant 4 + 2 *< A.var (Weaken Get) - A.var Get) ) $
           retPoly $ varPoly Get

-- >>> mathematica $ example2
-- Integrate[Integrate[DiracDelta[4 - y + 2*x]*y, {y, 1 + x, Infinity}], {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise example2
-- Integrate[4 + 2*x, {x, -3, Infinity}]

example3 :: P 'Unit
example3 = Integrate full $
           Integrate full $
           Cond (IsNegative (A.constant 3 - A.var Get)) $
           Cond (IsZero (A.constant 4 + A.var (Weaken Get) - A.var Get)) $
           retPoly $
           constPoly 2 + (varPoly Get) ^+ 2 + (one+one) * varPoly (Weaken Get)

-- >>> mathematica $ example3
-- Integrate[Integrate[Boole[3 - y ≤ 0]*DiracDelta[4 - y + x]*(2 + y^2 + 2*x), {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise example3
-- Integrate[18 + 10*x + x^2, {x, -1, Infinity}]

example4a :: P 'Unit
example4a = Integrate (Domain [zero] [A.constant 1]) Done

-- >>> mathematica $ normalise example4a
-- 1

-- >>> mathematica $ approxIntegrals 4 (normalise example4a)
-- 1


example4 :: P 'Unit
example4 = Integrate full $
           Integrate full $
           Cond (IsNegative (A.constant (-3) - A.var Get)) $
           Cond (IsNegative (A.constant (-3) + A.var Get)) $
           Cond (IsZero (A.var  (Weaken Get) - A.var Get)) $
           retPoly $
           exp $ negate $ varPoly Get ^+2 + (varPoly (Weaken Get) ^+ 2)

-- >>> mathematica $ example4
-- Integrate[Integrate[Boole[-3 - y ≤ 0]*Boole[-3 + y ≤ 0]*DiracDelta[-y + x]*Exp[-y^2 - x^2], {y, -Infinity, Infinity}], {x, -Infinity, Infinity}]

-- >>> mathematica $ normalise example4
-- Integrate[Exp[-2*x^2], {x, -3, 3}]

-- >>> mathematica $ approxIntegrals 16 $ normalise example4
-- 1.253346416637889


example5 :: P ('Unit × 'R)
example5 = Integrate full $
           Cond (IsNegative (A.constant (-3) - A.var Get)) $
           Cond (IsNegative (A.constant (-3) + A.var Get)) $
           retPoly $
           exp $ negate $ varPoly Get ^+2 + (varPoly (Weaken Get) ^+ 2)

-- >>> mathematica example5
-- Integrate[Boole[-3 - y ≤ 0]*Boole[-3 + y ≤ 0]*Exp[-y^2 - x^2], {y, -Infinity, Infinity}]

-- >>> mathematica $ normalise example5
-- Integrate[Exp[-y^2 - x^2], {y, -3, 3}]

-- >>> mathematica $ approxIntegrals 8 $ normalise example5 
-- 9.523809523809527e-2*Exp[-9.0 - x^2] + 0.8773118952961091*Exp[-7.681980515339462 - x^2] + 0.8380952380952381*Exp[-4.499999999999999 - x^2] + 0.8380952380952381*Exp[-4.499999999999997 - x^2] + 1.0851535761614692*Exp[-1.318019484660537 - x^2] + 1.0851535761614692*Exp[-1.3180194846605355 - x^2] + 1.180952380952381*Exp[-4.930380657631324e-32 - x^2]

