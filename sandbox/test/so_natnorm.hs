-- SO test case, re: my use of ghc-typelits-natnormalise package.
--
-- David Banas <capn.freako@gmail.com>
-- February 9, 2018

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Bogus.NewFin where

import GHC.TypeLits
import Data.Proxy
import Data.Finite
import Data.Finite.Internal (Finite(..))
import Data.Reflection

-- A safer form of `finite`.
finite' :: (KnownNat n, KnownNat m, n `CmpNat` m ~ 'GT) => Proxy m -> Finite n
finite' p = Finite $ natVal p

-- A safer form of `getFinite`.
getFinite' :: KnownNat n => Finite n -> (forall m. (KnownNat m, n `CmpNat` m ~ 'GT) => Proxy m -> r) -> r
getFinite' x f = reifyNat (getFinite x) f

