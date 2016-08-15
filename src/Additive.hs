{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

-- | Commutative monoid intended to be used with a multiplicative monoid

module Additive where

import Control.Applicative (liftA2)
import Data.Foldable (fold)
import Data.Complex hiding (magnitude)
import Data.Ratio
import Foreign.C.Types (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)

import Data.MemoTrie

import Misc ((<~))

-- | Commutative monoid intended to be used with a multiplicative monoid
class Additive a where
  zero  :: a
  infixl 6 ^+^
  (^+^) :: a -> a -> a

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


-- Standard instance for an applicative functor applied to a vector space.
instance Additive v => Additive (a -> v) where
  zero  = pure   zero
  (^+^) = liftA2 (^+^)


-- Maybe is handled like the Maybe-of-Sum monoid
instance Additive a => Additive (Maybe a) where
  zero                = Nothing
  Nothing ^+^ b'      = b'
  a' ^+^ Nothing      = a'
  Just a' ^+^ Just b' = Just (a' ^+^ b')

-- Memo tries
instance (HasTrie u, Additive v) => Additive (u :->: v) where
  zero  = pure   zero
  (^+^) = liftA2 (^+^)

{--------------------------------------------------------------------
    Monoid wrapper
--------------------------------------------------------------------}

-- | Monoid under group addition.  Alternative to the @Sum@ in
-- "Data.Monoid", which uses 'Num' instead of 'Additive'.
newtype Add a = Add { getAdd :: a }
  deriving (Eq, Ord, Read, Show, Bounded)

instance Functor Add where
  fmap f (Add a) = Add (f a)

-- instance Applicative Add where
--   pure a = Add a
--   Add f <*> Add x = Add (f x)

instance Applicative Add where
  pure  = Add
  (<*>) = inAdd2 ($)

instance Additive a => Monoid (Add a) where
  mempty  = Add zero
  mappend = liftA2 (^+^)

-- | Application a unary function inside a 'Add'
inAdd :: (a -> b) -> (Add a -> Add b)
inAdd = Add <~ getAdd

-- | Application a binary function inside a 'Add'
inAdd2 :: (a -> b -> c) -> (Add a -> Add b -> Add c)
inAdd2 = inAdd <~ getAdd

instance Additive a => Additive (Add a) where
  zero  = mempty
  (^+^) = mappend

add :: (Foldable f, Functor f, Additive a) => f a -> a
add = getAdd . fold . fmap Add
