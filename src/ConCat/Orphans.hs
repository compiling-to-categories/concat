{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}

{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

-- | Orphan instances to be moved into other libraries
--
-- <https://github.com/ekmett/pointed/issues/18>

module Orphans where

import Prelude hiding (zipWith)
import Control.Applicative (liftA2)
import GHC.Generics (U1(..),Par1(..),(:+:)(..),(:*:)(..),(:.:)(..))

import Data.Void
import Data.Key
import Data.Pointed
import Data.Copointed
import Data.Stream (Stream(..))
import Control.Newtype

import Misc ((:*),(:+),inNew,inNew2)

{--------------------------------------------------------------------
    GHC.Generics and keys
--------------------------------------------------------------------}

-- Submitted to keys. Merge in progress.
#if 1

-- Key

type instance Key U1 = Void
type instance Key Par1 = ()
type instance Key (g :.: f) = (Key g , Key f)
type instance Key (f :*: g) = Either (Key f) (Key g)

-- Keyed

instance Keyed U1 where mapWithKey _ U1 = U1

instance Keyed Par1 where mapWithKey q = fmap (q ())

instance (Keyed g, Keyed f) => Keyed (f :*: g) where
  mapWithKey q (fa :*: ga) = mapWithKey (q . Left) fa :*: mapWithKey (q . Right) ga

instance (Keyed g, Keyed f) => Keyed (g :.: f) where
  mapWithKey q = inNew (mapWithKey (mapWithKey . fmap q . (,)))

#if 0
mapWithKey :: (Key (g :.: f) -> a -> b) -> (g :.: f) a -> (g :.: f) b
           :: ((Key g, Key f) -> a -> b) -> (g :.: f) a -> (g :.: f) b

mapWithKey q
  = \ (Comp1 gfa) -> Comp1 (mapWithKey (\ gk -> mapWithKey (\ fk a -> q (gk, fk) a)) gfa)
  = inNew $ mapWithKey (\ gk -> mapWithKey (\ fk a -> q (gk, fk) a))
  = inNew $ mapWithKey (\ gk -> mapWithKey (\ fk -> q (gk, fk)))
  = inNew $ mapWithKey (\ gk -> mapWithKey (q . (gk,)))
  = inNew $ mapWithKey (\ gk -> mapWithKey . (q .) $ (gk,))
  = inNew $ mapWithKey (\ gk -> mapWithKey . (q .) $ (,) gk)
  = inNew (mapWithKey (mapWithKey . fmap q . (,)))

q   :: ((Key g, Key f) -> a -> b)
gfa :: g (f a)
gk  :: Key g
fk  :: Key f
#endif

-- Zip

instance Zip U1 where zipWith = liftA2

instance Zip Par1 where zipWith = liftA2

instance (Zip f, Zip g) => Zip (f :*: g) where
  zipWith h (fa :*: ga) (fa' :*: ga') =
    zipWith h fa fa' :*: zipWith h ga ga'

instance (Zip f, Zip g) => Zip (g :.: f) where
  zipWith = inNew2 . zipWith . zipWith


-- ZipWithKey

instance ZipWithKey U1

instance ZipWithKey Par1

instance (Keyed g, Zip g, Keyed f, Zip f) => ZipWithKey (f :*: g)

instance (Keyed g, Zip g, Keyed f, Zip f) => ZipWithKey (g :.: f)


-- Indexable

instance Indexable U1 where index U1 = \ case

instance Indexable Par1 where index (Par1 a) () = a

instance (Indexable g, Indexable f) =>
         Indexable (f :*: g) where
  index (fa :*: _) (Left  fk) = fa ! fk
  index (_ :*: ga) (Right gk) = ga ! gk

instance (Indexable g, Indexable f) =>
         Indexable (g :.: f) where
  index (Comp1 gfa) (gk,fk) = gfa ! gk ! fk


-- Lookup

instance Lookup U1 where lookup = lookupDefault

instance Lookup Par1 where lookup = lookupDefault

instance (Indexable g, Indexable f) => Lookup (f :*: g) where
  lookup = lookupDefault

instance (Indexable g, Indexable f) => Lookup (g :.: f) where
  lookup = lookupDefault


-- Adjustable

instance Adjustable U1 where adjust = const (const id)

instance Adjustable Par1 where adjust h () = fmap h

instance (Adjustable g, Adjustable f) => Adjustable (f :*: g) where
  adjust h (Left  fk) (fa :*: ga) = adjust h fk fa :*: ga
  adjust h (Right gk) (fa :*: ga) = fa :*: adjust h gk ga

instance (Adjustable g, Adjustable f) => Adjustable (g :.: f) where
  adjust h (gk,fk) = inNew (adjust (adjust h fk) gk)

#endif

{--------------------------------------------------------------------
    GHC.Generics and pointed
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


{--------------------------------------------------------------------
    Control.Newtype and keys
--------------------------------------------------------------------}

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
