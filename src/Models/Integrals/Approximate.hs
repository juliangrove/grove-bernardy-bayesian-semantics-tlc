{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module Models.Integrals.Approximate (approxIntegrals) where

import Algebra.Classes
import qualified Algebra.Morphism.Affine as A
import Prelude hiding (Num(..), Fractional(..), (^), product, sum, pi, sqrt
                      , exp)
import qualified Models.Field
import qualified Algebra.Linear.Chebyshev as Chebyshev

import Models.Integrals.Types

--------------------------------------------------------------------------------
-- Approximation of integrals

-- | Finite context of Rats
class IntegrableContext γ where
  type Tgt γ 
  vRatToC :: Available Rat γ -> Available C (Tgt γ)

instance IntegrableContext () where
  type Tgt () = ()
  vRatToC = \case

instance IntegrableContext γ => IntegrableContext (γ,Rat) where
  type Tgt (γ, Rat) = (Tgt γ, C)
  vRatToC = \case
     Here -> Here
     There x -> There (vRatToC x)

ratToC :: (Available Rat γ -> Available C δ) -> Poly γ Rat -> Poly δ C
ratToC v = evalPoly v (Models.Field.eval @C) varPoly

dumb :: Multiplicative a => a -> Dumb a
dumb x = x :/ one

approxIntegrals :: IntegrableContext γ => Int -> P γ Rat -> P (Tgt γ) C
approxIntegrals n e = evalDumb Ret (approxIntegralsW n vRatToC e) 

renameCond :: (Available Rat γ -> Available C δ) -> Cond γ Rat -> Cond δ C
renameCond f = fmap (A.mapVars f . fmap (Models.Field.eval @C))

approxIntegralsW
  :: forall γ δ. Int -> (Available Rat γ -> Available C δ) -> P γ Rat -> DD δ C
approxIntegralsW n v =
  let r0 :: P γ Rat -> Ret δ C
      r0 = approxIntegralsW n v
      v' :: Available Rat (γ,Rat) -> Available C (δ,C)
      v' = \case Here -> Here
                 There x -> There (v x)
  in \case
    Add a b -> r0 a + r0 b
    Div a b -> r0 a / r0 b
    Ret x -> dumb (ratToC v x)
    Cond (IsNegative c) a -> dumb (charfun (ratToC v (exprToPoly c))) * (r0 a)
    Cond (IsZero _) _ -> error "approxIntegralsW: equality not eliminated?"
    Integrate (mkSuprema -> (ratToC v -> lo, ratToC v -> hi)) e ->
      Chebyshev.integral @C @C n lo hi (\x -> substP0 x (approxIntegralsW n v' e))

substP0 :: Poly γ C -> Ret (γ,C) C -> Ret γ C
substP0 x = substDumb (\case Here -> x; There v -> varPoly v)

substDumb :: RatLike α => SubstP γ δ  -> Dumb (Poly γ α) -> Dumb (Poly δ α)
substDumb f = evalDumb (dumb . substPoly f)
