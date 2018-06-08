{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- The plugin does the real work here.
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Entailments for KnownNat.
-- To eliminate when plugins no longer cause spurious recompilation.

module ConCat.Known where

import GHC.TypeLits
import Data.Constraint

#define KNOW(nm,op) \
nm :: (KnownNat m, KnownNat n) :- KnownNat (m op n) ; \
nm = Sub Dict

-- knowAdd :: KnownNat2 m n :- KnownNat (m + n)
-- knowAdd = Sub Dict

KNOW(knownAdd,+)
KNOW(knownMul,*)
