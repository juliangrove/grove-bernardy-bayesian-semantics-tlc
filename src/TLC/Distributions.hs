{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

module TLC.Distributions where

import Data.Ratio
import Algebra.Classes hiding (normalize)
import Prelude hiding (Monad(..), Num(..), Fractional(..))
import TLC.Terms

factor :: γ ⊢ (R ⟶ ((Unit ⟶ R) ⟶ R))
factor
  = Lam (Lam (App (App (Con (General Mult)) (Var (Weaken Get))) (App (Var Get) TT)))
factor' x = App factor x

observe :: γ ⊢ (T ⟶ ((Unit ⟶ R) ⟶ R))
observe = Lam (App factor (App (Con (General Indi)) (Var Get)))
observe' φ = App observe φ
 
normal :: Rational -> Rational -> γ ⊢ ((R ⟶ R) ⟶ R)
normal x y = App (Con $ General Nml) (Pair (Con $ General $ Incl x) (Con $ General $ Incl y))

cauchy :: Rational -> Rational -> γ ⊢ (('R ⟶ 'R) ⟶ 'R)
cauchy x0 γ = App (Con $ General Cauchy) (Pair (Con $ General $ Incl x0) (Con $ General $ Incl γ))

uniform :: Rational -> Rational -> γ ⊢ ((R ⟶ R) ⟶ R)
uniform x y
  = App (Con $ General Uni) (Pair (Con $ General $ Incl x) (Con $ General $ Incl y))

lesbegue :: γ ⊢ ((R ⟶ R) ⟶ R)
lesbegue = Con $ General Les

-- Convert a probabilistic program into a distribution
distr :: Equality α => γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ (α ⟶ 'R)
distr p = Lam (App (wkn p) (Lam ((Var Get) ≐ (Var (Weaken Get)))) / measure (wkn p))

measure :: γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ 'R
measure m = App m (Lam one)

normalize :: γ ⊢ ((α ⟶ 'R) ⟶ 'R) -> γ ⊢ ((α ⟶ 'R) ⟶ 'R)
normalize m = m ⋆ Lam (factor' (recip $ measure $ wkn m) >> η (Var Get))

expectedValue :: γ ⊢ (('R ⟶ 'R) ⟶ 'R) -> γ ⊢ 'R
expectedValue m = lower m / measure m where
  lower :: γ ⊢ ((R ⟶ R) ⟶ R) -> γ ⊢ R
  lower m = App m (Lam (Var Get))
