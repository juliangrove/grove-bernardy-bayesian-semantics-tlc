{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}

import Examples.Anaphora (l1)
-- import Examples.HNaloma (l1)
-- import Examples.Naloma
import Models.Logical.FiniteLogical
import Prelude hiding (Num(..), Fractional(..))
import TLC.Distributions
import TLC.Terms
import Text.Pretty.Math
import Algebra.Classes
import qualified Algebra.Expression as E

main :: IO ()
main = do
  putStrLn "temp:"
  temp <- getLine
  let n = S (S Z)
      α = toRational (read temp :: Double)
      result = evalFL $ normalForm $ expectedValue $
        l1 α n @@ Con (Utt (MergeRgt (Pn 0) IsPrepared)) ⋆
        Lam (η (hmorph n
                (Con EqGen `App`
                 (sel' 0 (upd' jp (upd' vlad emp)) `Pair` jp)) `App` Var Get))
  print (E.eval id result :: Double)
