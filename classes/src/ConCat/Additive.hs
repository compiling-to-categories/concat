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
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

#include "ConCat/Ops.inc"

-- | Commutative monoid intended to be used with a multiplicative monoid

module ConCat.Additive where

import Prelude hiding (zipWith)
import Data.Monoid (Monoid(..), Sum(..), Product(..))
import Data.Semigroup (Semigroup(..))
import Data.Complex hiding (magnitude)
import Data.Ratio
import Foreign.C.Types (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)
import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:.:)(..))
import GHC.TypeLits (KnownNat)

import Data.Key(Zip(..))
import Data.Pointed
import Data.Functor.Rep (Representable(..))
import Data.Vector.Sized (Vector)
import Data.Finite.Internal

import ConCat.Misc
import ConCat.Rep (HasRep(abst),inAbst,inAbst2)
import qualified ConCat.Rep
import ConCat.Orphans ()

-- | Commutative monoid intended to be used with a multiplicative monoid
class Additive a where
  zero  :: a
  infixl 6 ^+^
  (^+^) :: a -> a -> a
  default zero :: (Pointed h, Additive b, a ~ h b) => a
  zero = pointNI zero
  default (^+^) :: (Zip h, Additive b, a ~ h b) => Binop a
  (^+^) = zipWithNI (^+^)
  {-# INLINE zero #-}
  {-# INLINE (^+^) #-}

-- These definitions and the corresponding Catify rewrites in AltCat prevent the point and zipWith methods from getting inlined too soon.
-- See 2018-04-09 notes.
pointNI :: Pointed h => a -> h a
pointNI = point
{-# INLINE [0] pointNI #-}

zipWithNI :: Zip h => (a -> b -> c) -> h a -> h b -> h c
zipWithNI = zipWith
{-# INLINE [0] zipWithNI #-}

instance Additive () where
  zero = ()
  () ^+^ () = ()

#define ScalarType(t) \
  instance Additive (t) where { zero = 0 ; (^+^) = (+);\
  {-# INLINE zero #-}; \
  {-# INLINE (^+^) #-} }

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
  zero              = (zero,zero)
  (u,v) ^+^ (u',v') = (u^+^u',v^+^v')

instance (Additive u,Additive v,Additive w)
    => Additive (u,v,w) where
  zero                   = (zero,zero,zero)
  (u,v,w) ^+^ (u',v',w') = (u^+^u',v^+^v',w^+^w')

instance (Additive u,Additive v,Additive w,Additive x)
    => Additive (u,v,w,x) where
  zero                        = (zero,zero,zero,zero)
  (u,v,w,x) ^+^ (u',v',w',x') = (u^+^u',v^+^v',w^+^w',x^+^x')

type AddF f = (Pointed f, Zip f)

instance KnownNat n => Additive (Finite n) where
  zero = 0
  (^+^) = (+)

#if 1

#define AdditiveFunctor(f) instance (AddF (f), Additive v) => Additive ((f) v)

AdditiveFunctor((->) a)
AdditiveFunctor(Sum)
AdditiveFunctor(Product)
AdditiveFunctor(U1)
AdditiveFunctor(Par1)
AdditiveFunctor(f :*: g)
AdditiveFunctor(g :.: f)

#else

instance Additive v => Additive (a -> v)
instance Additive v => Additive (Sum     v)
instance Additive v => Additive (Product v)

instance Additive v => Additive (U1 v)
instance Additive v => Additive (Par1 v)
instance (Additive v, AddF f, AddF g) => Additive ((f :*: g) v)
instance (Additive v, AddF f, AddF g) => Additive ((g :.: f) v)

#endif


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

-- Experiment
instance Additive Bool where
  -- zero = undefined
  -- _ ^+^ _ = undefined
  zero = False
  (^+^) = (||)
  {-# INLINE zero #-}
  {-# INLINE (^+^) #-}

{--------------------------------------------------------------------
    Monoid wrapper
--------------------------------------------------------------------}

-- | Monoid under group addition.  Alternative to the @Sum@ in
-- "Data.Monoid", which uses 'Num' instead of 'Additive'.
newtype Add a = Add { getAdd :: a }
  deriving (Eq, Ord, Read, Show, Bounded)

instance HasRep (Add a) where
  type Rep (Add a) = a
  abst = Add
  repr = getAdd

instance Functor Add where fmap = inAbst

instance Applicative Add where
  pure  = abst
  (<*>) = inAbst2 ($)

instance Additive a => Semigroup (Add a) where
  (<>) = inAbst2 (^+^)

instance Additive a => Monoid (Add a) where
  mempty  = abst zero
  mappend = (<>)

instance Additive a => Additive (Add a) where
  zero  = mempty
  (^+^) = mappend

-- sumA' :: (Foldable h, Additive a) => h a -> a
-- sumA' = getAdd . foldMap Add

-- Enables translation of sumA to jamPF in AltCat.
type SummableF h = (Representable h, Eq (Rep h), Zip h, Pointed h, Foldable h)

class    SummableF h => Summable h
instance SummableF h => Summable h

-- The constraint ‘Representable h’
--   is no smaller than the instance head
-- (Use UndecidableInstances to permit this)

sumA :: (
  -- Summable h, Additive a
  Foldable h, Additive a
  ) => h a -> a
sumA = getAdd . foldMap Add
{-# OPINLINE sumA #-}
