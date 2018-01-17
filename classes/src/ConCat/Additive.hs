{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}

-- | Commutative monoid intended to be used with a multiplicative monoid

module ConCat.Additive where

import Prelude hiding (zipWith)
import Data.Monoid
import Data.Complex hiding (magnitude)
import Data.Ratio
import Foreign.C.Types (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)
import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:.:)(..))
import GHC.TypeLits (KnownNat)

import Control.Newtype (Newtype(..))
import Data.Key(Zip(..))
import Data.Pointed(Pointed(..))
import Data.Functor.Rep (Representable(..))
import Data.Vector.Sized (Vector)

import ConCat.Misc
import ConCat.Orphans ()

-- | Commutative monoid intended to be used with a multiplicative monoid
class Additive a where
  zero  :: a
  infixl 6 ^+^
  (^+^) :: a -> a -> a
  default zero :: (Pointed h, Additive b) => h b
  zero = point zero
  default (^+^) :: (Zip h, Additive b) => Binop (h b)
  (^+^) = zipWith (^+^)
  {-# INLINE (^+^) #-}

-- zipWith' :: Representable h
--          => (a -> b -> c) -> (h a -> h b -> h c)
-- zipWith' f as bs = fmap (uncurry f) (zip (as,bs))
-- {-# INLINER zipWith' #-}

instance Additive () where
  zero = ()
  () ^+^ () = ()

#define ScalarType(t) \
  instance Additive (t) where { zero = 0 ; (^+^) = (+) }

ScalarType(Int)
ScalarType(Integer)
ScalarType(Float)
ScalarType(Double)
ScalarType(CSChar)
ScalarType(CInt)
ScalarType(CShort)
ScalarType(CLong)
ScalarType(CLLong)
ScalarType(CIntMax)
ScalarType(CDouble)
ScalarType(CFloat)

instance Integral a => Additive (Ratio a) where
  zero  = 0
  (^+^) = (+)

instance (RealFloat v, Additive v) => Additive (Complex v) where
  zero  = zero :+ zero
  (^+^) = (+)

-- The 'RealFloat' constraint is unfortunate here. It's due to a
-- questionable decision to place 'RealFloat' into the definition of the
-- 'Complex' /type/, rather than in functions and instances as needed.

instance (Additive u,Additive v) => Additive (u,v) where
  zero             = (zero,zero)
  (u,v) ^+^ (u',v') = (u^+^u',v^+^v')

instance (Additive u,Additive v,Additive w)
    => Additive (u,v,w) where
  zero                   = (zero,zero,zero)
  (u,v,w) ^+^ (u',v',w') = (u^+^u',v^+^v',w^+^w')

instance (Additive u,Additive v,Additive w,Additive x)
    => Additive (u,v,w,x) where
  zero                        = (zero,zero,zero,zero)
  (u,v,w,x) ^+^ (u',v',w',x') = (u^+^u',v^+^v',w^+^w',x^+^x')

instance Additive v => Additive (a -> v)
instance Additive v => Additive (Sum     v)
instance Additive v => Additive (Product v)

type AddF f = (Pointed f, Zip f)

instance Additive v => Additive (U1 v)
instance Additive v => Additive (Par1 v)
instance (Additive v, AddF f, AddF g) => Additive ((f :*: g) v)
instance (Additive v, AddF f, AddF g) => Additive ((g :.: f) v)

-- instance (Eq i, Additive v) => Additive (Arr i v) where
--   zero = point zero
--   as ^+^ bs = fmap (uncurry (^+^)) (zipC (as,bs))

-- TODO: Define and use zipWithC (^+^) as bs.

instance (Additive v, KnownNat n) => Additive (Vector n v)

-- Maybe is handled like the Maybe-of-Sum monoid
instance Additive a => Additive (Maybe a) where
  zero                = Nothing
  Nothing ^+^ b'      = b'
  a' ^+^ Nothing      = a'
  Just a' ^+^ Just b' = Just (a' ^+^ b')

-- -- Memo tries
-- instance (HasTrie u, Additive v) => Additive (u :->: v) where
--   zero  = pure   zero
--   (^+^) = liftA2 (^+^)

{--------------------------------------------------------------------
    Monoid wrapper
--------------------------------------------------------------------}

-- | Monoid under group addition.  Alternative to the @Sum@ in
-- "Data.Monoid", which uses 'Num' instead of 'Additive'.
newtype Add a = Add { getAdd :: a }
  deriving (Eq, Ord, Read, Show, Bounded)

instance Newtype (Add a) where
  type O (Add a) = a
  pack   = Add
  unpack = getAdd

instance Functor Add where fmap = inNew

instance Applicative Add where
  pure  = pack
  (<*>) = inNew2 ($)

instance Additive a => Monoid (Add a) where
  mempty  = pack zero
  mappend = inNew2 (^+^)

instance Additive a => Additive (Add a) where
  zero  = mempty
  (^+^) = mappend

sumA' :: (Foldable h, Additive a) => h a -> a
sumA' = getAdd . foldMap Add

-- Enables translation of sumA to jamPF in AltCat.
type Summable h = (Representable h, Eq (Rep h), Zip h, Pointed h, Foldable h)

sumA :: (Summable h, Additive a) => h a -> a
sumA = getAdd . foldMap Add
