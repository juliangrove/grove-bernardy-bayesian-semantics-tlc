{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module RSA where

import Prelude hiding (Monad(..))
import TLC.RN
import TLC.Terms

normal :: γ ⊢ ((R × R) ⟶ (R ⟶ R) ⟶ R)
normal = Con Nml



-- l0 :: γ ⊢ (U ⟶ ((Context ⟶ R) ⟶ R))
-- l0 = _
