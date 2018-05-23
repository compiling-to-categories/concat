{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# LANGUAGE AllowAmbiguousTypes #-} -- for temporary "axioms"

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin TypeNatSolver #-}

-- | An alternative to Data.Finite from finite-typelits.
-- This version relies on GHC to verify all type arithmetic.
module ConCat.Fin where

import Data.Proxy (Proxy(..))
import GHC.TypeLits
import Data.Type.Bool
import Control.Arrow ((|||))

-- Experimental
import Data.Constraint

import ConCat.Misc ((:*),(:+))

-- Missing from GHC.TypeLits
infix 4 <, >=, >
type a <  b = a + 1 <= b
type a >= b = b <= a
type a >  b = b < a

{--------------------------------------------------------------------
    Finite
--------------------------------------------------------------------}

data Finite n = forall a. (KnownNat a, a < n) => Finite (Proxy a)

-- -- In GADT notation
-- data Finite n where Finite :: (KnownNat a, a < n) => Proxy a -> Finite n

-- TODO: Do we really need 'KnownNat a' here? I think we will, in order to
-- extract a dynamic natural number for comparisons and arithmetic.

finite :: forall a n. (KnownNat a, a < n) => Finite n
finite = Finite (Proxy @a)

zero :: (KnownNat n, 0 < n) => Finite n
zero = finite @0

-- Blows the constraint reduction stack
-- 
-- pattern Fi :: forall a n. (KnownNat a, a < n) => Finite n
-- pattern Fi = Finite (Proxy :: Proxy a)

weakenL :: forall m n. Finite m -> Finite (m + n)
weakenL (Finite (Proxy :: Proxy a)) = Finite (Proxy @a)

-- Variation
weaken' :: forall u v. u <= v => Finite u -> Finite v
weaken' (Finite (Proxy :: Proxy a)) = Finite (Proxy @a)

weakenR :: forall m n. Finite n -> Finite (m + n)
weakenR (Finite (Proxy :: Proxy b)) = Finite (Proxy @b)

bumpR :: forall m n. KnownNat m => Finite n -> Finite (m + n)
bumpR (Finite (Proxy :: Proxy b)) = Finite (Proxy @(m + b))

type KnownNat2 m n = (KnownNat m, KnownNat n)

sumToFin :: KnownNat m => Finite m :+ Finite n -> Finite (m + n)
sumToFin = weakenL ||| bumpR

finToSum :: KnownNat2 m n => Finite (m + n) -> Finite m :+ Finite n
finToSum = undefined

-- Safe subtraction
data Diff u v = (u >= v) => Diff (Proxy (u - v))

sub :: forall u v. KnownNat2 u v => Diff u v :+ Diff v u
sub = undefined
