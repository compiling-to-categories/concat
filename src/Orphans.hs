{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

-- | Orphan instances to be moved into other libraries
--
-- <https://github.com/ekmett/pointed/issues/18>

module Orphans where

import Prelude hiding (zipWith)
import Control.Applicative (liftA2)
import GHC.Generics (Par1(..),(:+:)(..),(:*:)(..),(:.:)(..))

import Data.Key (Zip(..))
import Data.Pointed
import Data.Copointed
import Data.Stream (Stream(..))
import Control.Newtype

import Misc ((:*),(:+))

{--------------------------------------------------------------------
    GHC.Generics
--------------------------------------------------------------------}

instance Pointed Par1 where
  point = Par1

instance (Pointed f, Pointed g) => Pointed (f :*: g) where
  point a = point a :*: point a

instance (Pointed f, Pointed g) => Pointed (g :.: f) where
  point = Comp1 . point . point

instance Copointed Par1 where
  copoint = unPar1

instance (Copointed f, Copointed g) => Copointed (g :.: f) where
  copoint = copoint . copoint . unComp1

-- TODO: many Pointed and Copointed instances for GHC.Generics types.
-- Offer as a pointed patch, as I did with keys.

instance Newtype ((a :*: b) t) where
  type O ((a :*: b) t) = a t :* b t
  pack (a,b) = a :*: b
  unpack (a :*: b) = (a,b)

instance Newtype ((a :+: b) t) where
  type O ((a :+: b) t) = a t :+ b t
  pack = either L1 R1
  unpack = eitherF Left Right

instance Newtype ((a :.: b) t) where
  type O ((a :.: b) t) = a (b t)
  pack = Comp1
  unpack = unComp1

eitherF :: (a t -> c) -> (b t -> c) -> ((a :+: b) t -> c)
eitherF f _ (L1 a) = f a
eitherF _ g (R1 b) = g b

{--------------------------------------------------------------------
    Data.Stream
--------------------------------------------------------------------}

instance Pointed Stream where point   = pure
instance Zip     Stream where zipWith = liftA2
-- etc

instance Foldable Stream where
  foldMap f ~(Cons a as) = f a `mappend` foldMap f as
