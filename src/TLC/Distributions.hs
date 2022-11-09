{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module TLC.Distributions where

import Data.Ratio
import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import TLC.Terms

factor :: γ ⊢ ('R ⟶ (('Unit ⟶ 'R) ⟶ 'R))
factor =
  Lam (Lam (App (App (Con ( Mult)) (Var (Weaken Get))) (App (Var Get) TT)))
factor' x = App factor x

observe :: γ ⊢ (T ⟶ ((Unit ⟶ R) ⟶ R))
observe = Lam (App factor (App (Con Indi) (Var Get)))
observe' φ = App observe φ
 
-- normal :: Rational -> Rational -> γ ⊢ ((R ⟶ R) ⟶ R)
-- normal x y =
--   App (Con $  Nml) (Pair (Con $ Incl x) (Con $ Incl y))

-- cauchy :: Rational -> Rational -> γ ⊢ (('R ⟶ 'R) ⟶ 'R)
-- cauchy x0 γ =
--   App (Con $  Cau) (Pair (Con $ Incl x0) (Con $ Incl γ))

-- quartic :: Rational -> Rational -> γ ⊢ (('R ⟶ 'R) ⟶ 'R)
-- quartic x y =
--   App (Con $  Qua) (Pair (Con $ Incl x) (Con $ Incl y))

-- uniform :: Rational -> Rational -> γ ⊢ (('R ⟶ 'R) ⟶ 'R)
-- uniform x y =
--   App (Con $  Uni) (Pair (Con $ Incl x) (Con $ Incl y))

lesbegue :: γ ⊢ (('R ⟶ 'R) ⟶ 'R)
lesbegue = Con $  Les

-- Convert a probabilistic program into a distribution
distr :: Equality α => γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ (α ⟶ 'R)
distr p =
  Lam (App (wkn p) (Lam ((Var Get) ≐ (Var (Weaken Get)))) / measure (wkn p))

measure :: γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ 'R
measure m = App m (Lam one)

normalize :: γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ ((α ⟶ 'R) ⟶ 'R)
normalize m = m ⋆ Lam (factor' (recip $ measure $ wkn m) >> η (Var Get))

expectedValue :: γ ⊢ (('R ⟶ 'R) ⟶ 'R) -> γ ⊢ 'R
expectedValue m = lower m / measure m
  
lower :: γ ⊢ (('R ⟶ 'R) ⟶ 'R) -> γ ⊢ 'R
lower m = App m (Lam (Var Get))
