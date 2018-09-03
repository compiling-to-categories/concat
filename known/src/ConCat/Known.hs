{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}

-- #define KNOWABLE

#ifdef KNOWABLE
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
#endif

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

-- knownAdd :: KnownNat2 m n :- KnownNat (m + n)
-- knownAdd = Sub Dict

KNOW(knownAdd,+)
KNOW(knownMul,GHC.TypeLits.*)

{--------------------------------------------------------------------
    Experiment
--------------------------------------------------------------------}

#ifdef KNOWABLE

class KnowableNat n where knownNat :: Dict (KnownNat n)

instance {-# OVERLAPPABLE #-} KnownNat n => KnowableNat n where knownNat = Dict

-- type KnownNat2 m n = (KnownNat m, KnownNat n)

-- instance KnownNat2 m n => KnowableNat (m + n) where knownNat = Dict \\ knownAdd @m @n
-- instance KnownNat2 m n => KnowableNat (m * n) where knownNat = Dict \\ knownMul @m @n

type KnowableNat2 m n = (KnowableNat m, KnowableNat n)

instance KnowableNat2 m n => KnowableNat (m + n) where knownNat = Dict \\ knownAdd @m @n
instance KnowableNat2 m n => KnowableNat (m * n) where knownNat = Dict \\ knownMul @m @n

-- Illegal type synonym family application in instance

#endif
