{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

-- | Vector spaces as zippable functors

module ConCat.Free.VectorSpace where

import Prelude hiding (zipWith,Float,Double)

import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:.:)(..))

import Data.Foldable (fold)
import Data.Pointed
import Data.Key (Zip(..))
import Data.Map (Map)

import Control.Newtype

import ConCat.Orphans ()
import ConCat.Misc (inNew2,(:*),(<~))
import ConCat.Float
-- import ConCat.Category (UT(..),Constrained(..),FunctorC(..))

{--------------------------------------------------------------------
    Vector spaces
--------------------------------------------------------------------}

infixl 7 *^, <.>, >.<
infixl 6 ^+^

#if 0
type Zeroable = Pointed

-- Zero vector
zeroV :: (Pointed f, Num a) => f a
zeroV = point 0

#else

-- Experimental alternative to Pointed
class Functor f => Zeroable f where
  zeroV :: Num a => f a
  default zeroV :: (Pointed f, Num a) => f a
  zeroV = point 0

-- The Functor superclass is just for convenience.
-- Remove if needed (and fix other signatures).

instance Zeroable U1

instance Zeroable Par1

instance Zeroable ((->) k)

instance Ord k => Zeroable (Map k) where zeroV = mempty

instance (Zeroable f, Zeroable g) => Zeroable (f :*: g) where
  zeroV = zeroV :*: zeroV

instance (Zeroable f, Zeroable g) => Zeroable (g :.: f) where
  zeroV = Comp1 (const zeroV <$> (zeroV :: g Int))

#endif

-- TODO: Replace Num constraints with Ring or SemiRing

-- Scale a vector
(*^) :: (Functor f, Num s) => s -> f s -> f s
s *^ v = (s *) <$> v

-- Add vectors
(^+^) :: (Zip f, Num s) => f s -> f s -> f s
(^+^) = zipWith (+)

-- Inner product
(<.>) :: (Zip f, Foldable f, Num s) => f s -> f s -> s
x <.> y = sum (zipWith (*) x y)

-- Outer product
(>.<) :: (Num s, Functor f, Functor g) => g s -> f s -> g (f s)
x >.< y = (*^ y) <$> x

-- Would I rather prefer swapping the arguments (equivalently, transposing the
-- result)?

-- After transposing (:-), do I still need sumV?
newtype SumV f a = SumV (f a)

instance Newtype (SumV f a) where
  type O (SumV f a) = f a
  pack as = SumV as
  unpack (SumV as) = as

instance (Zeroable f, Zip f, Num a) => Monoid (SumV f a) where
  mempty = pack zeroV
  mappend = inNew2 (^+^)

sumV :: (Functor m, Foldable m, Zeroable n, Zip n, Num a) => m (n a) -> n a
sumV = unpack . fold . fmap SumV

{--------------------------------------------------------------------
    Conversion
--------------------------------------------------------------------}

type NewHasV s t = (Newtype t, HasV s (O t), V s t ~ V s (O t))

class HasV s t where
  type V s t :: * -> *
  toV :: t -> V s t s
  unV :: V s t s -> t
  -- Default via Newtype.
  type V s t = V s (O t)
  default toV :: NewHasV s t => t -> V s t s
  default unV :: NewHasV s t => V s t s -> t
  toV = toV . unpack
  unV = pack . unV

inV :: (HasV s a, HasV s b) => (a -> b) -> (V s a s -> V s b s)
inV = toV <~ unV

-- Can I replace my HasRep class with Newtype?

-- -- Replace by special cases as needed
-- instance HasV s s where
--   type V s s = Par1
--   toV = Par1
--   unV = unPar1

instance HasV s () where
  type V s () = U1
  toV () = U1
  unV U1 = ()

instance HasV Float Float where
  type V Float Float = Par1
  toV = Par1
  unV = unPar1

instance HasV Double Double where
  type V Double Double = Par1
  toV = Par1
  unV = unPar1

-- etc

instance (HasV s a, HasV s b) => HasV s (a :* b) where
  type V s (a :* b) = V s a :*: V s b
  toV (a,b) = toV a :*: toV b
  unV (f :*: g) = (unV f,unV g)

-- instance HasV s a => HasV s (Pair a) where
--   type V s (Pair a) = Pair :.: V s a
--   toV = Comp1 . fmap toV
--   unV = fmap unV . unComp1

-- Similarly for other functors

#if 1
instance HasV s b => HasV s (a -> b) where
  type V s (a -> b) = (->) a :.: V s b
  toV = Comp1 . fmap toV
  unV = fmap unV . unComp1
#else
instance HasV s b => HasV s (a -> b) where
  type V s (a -> b) = Map a :.: V s b
  toV = Comp1 . ??
  unV = ?? . unComp1
#endif

#if 0
-- Example default instance

data Pickle a = Pickle a a a

instance Newtype (Pickle a) where
  type O (Pickle a) = (a :* a) :* a
  unpack (Pickle a b c) = ((a,b),c)
  pack ((a,b),c) = Pickle a b c

instance HasV s a => HasV s (Pickle a)
#endif

#if 0
-- -- | The 'unV' form of 'zeroV'
-- zeroX :: forall s a. (HasV s a, Zeroable (V s a)) => a
-- zeroX = unV (zeroV :: V s a s)

vfun :: (HasV s a, HasV s b) => (a -> b) -> UT s (V s a) (V s b)
vfun = UT . inV

-- vfun f = UT (toV . f . unV)

-- | Free vector over scalar s
data VFun s

instance FunctorC (VFun s) (Constrained (HasV s) (->)) (UT s) where
  -- type OkF (VFun s) = HasV s
  -- type OkF (VFun s) a = HasV s a
  -- type OkF (VFun s) b a = (HasV s a, HasV s b)
  type VFun s % a = V s a
  fmapC (Constrained f) = UT (inV f)
                          -- vfun f

#endif
