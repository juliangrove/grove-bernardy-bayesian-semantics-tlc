{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module Examples.Utterances where

import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..), Floating(..))
import TLC.HOAS
import qualified TLC.Terms as F

isTall :: Exp F.U
isTall = Con $ Utt $ F.MergeRgt F.Vl F.IsTall
isShort :: Exp F.U
isShort = Con $ Utt $ F.MergeRgt F.Vl F.IsShort
vaccuous :: Exp F.U
vaccuous = Con $ Silence
is5Feet :: Exp F.U
is5Feet = Con $ Utt $ F.MergeRgt F.Vl (F.IsThisTall 5)
is55Feet :: Exp F.U
is55Feet = Con $ Utt $ F.MergeRgt F.Vl (F.IsThisTall 5.5)
is6Feet :: Exp F.U
is6Feet = Con $ Utt $ F.MergeRgt F.Vl (F.IsThisTall 6)
is65Feet :: Exp F.U
is65Feet = Con $ Utt $ F.MergeRgt F.Vl (F.IsThisTall 65)

cost :: Rational -> Double -> Exp F.R
cost α x = Con (F.Incl (toRational (exp (- x * (fromRational α)) :: Double))) 

wordCost :: Double
wordCost = 2/3

tallShortOrSilence,tallOrSilenceOrGiven :: Rational -> Exp ((F.U ⟶ F.R) ⟶ F.R)

tallShortOrSilence α = Lam $ \k -> cost α 2 * (k @@ isTall) + k @@ vaccuous  
  -- + k @@ isShort -- makes no difference on L0[isTall] (obviously),
  -- but also S1[isTall] (and in turn L1[isTall]). This is because
  -- L0[isTall] is already zero for every world where L0[isShort] is
  -- non-zero.

tallOrSilenceOrGiven α = Lam $ \k -> cost α (wordCost*3) * (k @@ isTall) + k @@ vaccuous + cost α (wordCost*4) * (k @@ is5Feet + k @@ is55Feet + k @@ is6Feet)

