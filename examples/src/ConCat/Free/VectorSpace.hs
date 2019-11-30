{-# LANGUAGE TypeApplications #-}
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
{-# OPTIONS_GHC -Wno-unused-imports #-}  -- TEMP

-- | Vector spaces as zippable functors

module ConCat.Free.VectorSpace where

import Prelude hiding (zipWith)
import Data.Monoid (Sum(..),Product(..))
import Data.Semigroup (Semigroup(..))
-- import GHC.Exts (Coercible,coerce)
import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:+:)(..),(:.:)(..))
#ifdef VectorSized
import GHC.TypeLits (KnownNat)
#endif

import Data.Foldable (fold)
import Data.Pointed
import Data.Key (Zip(..))
-- import Data.Vector.Sized (Vector)
-- import Data.Map (Map)
import Data.Constraint ((:-)(..),Dict(..))
import Data.Vector.Sized (Vector)

-- import Control.Newtype.Generics

import ConCat.Orphans ()
import ConCat.Misc ((:*),(:+),(<~),sqr)
import ConCat.Rep
-- import ConCat.Category (UT(..),Constrained(..),FunctorC(..))
import ConCat.AltCat (OpCon(..),Sat,type (|-)(..),fmapC)

{--------------------------------------------------------------------
    Vector spaces
--------------------------------------------------------------------}

infixl 7 *^, <.>, >.<
infixl 6 ^+^, ^-^

#if 1
type Zeroable = Pointed

-- Zero vector
zeroV :: (Pointed f, Num a) => f a
zeroV = point 0

-- TODO: Maybe use tabulate . const instead of point

#else

-- Experimental alternative to Pointed
class Functor f => Zeroable f where
  zeroV :: Num a => f a
  default zeroV :: (Pointed f, Num a) => f a
  zeroV = point 0

-- The Functor superclass is just for convenience.
-- Remove if needed (and fix other signatures).

instance Zeroable U1 where
  -- zeroV = U1
  -- {-# INLINE zeroV #-}

-- The following instance could be defaulted. I'm tracking down what might be an
-- inlining failure.

instance Zeroable Par1 where
  zeroV = Par1 0
  {-# INLINE zeroV #-}

instance Zeroable ((->) k)

instance Ord k => Zeroable (Map k) where
  zeroV = mempty
  {-# INLINE zeroV #-}

instance (Zeroable f, Zeroable g) => Zeroable (f :*: g) where
  zeroV = zeroV :*: zeroV
  {-# INLINE zeroV #-}

instance (Zeroable f, Zeroable g) => Zeroable (g :.: f) where
  zeroV = Comp1 (const zeroV <$> (zeroV :: g Int))
  {-# INLINE zeroV #-}

#endif

-- TODO: Replace Num constraints with Ring or SemiRing

-- | Scale a vector
scaleV, (*^) :: (Functor f, Num s) => s -> f s -> f s
s *^ v = (s *) <$> v
scaleV = (*^)
{-# INLINE (*^) #-}
{-# INLINE scaleV #-}

-- | Negate a vector
negateV :: (Functor f, Num s) => f s -> f s
negateV = ((-1) *^)
{-# INLINE negateV #-}

-- | Add vectors
addV, (^+^) :: (Zip f, Num s) => f s -> f s -> f s
(^+^) = zipWith (+)
addV = (^+^)
{-# INLINE (^+^) #-}
{-# INLINE addV #-}

-- | Subtract vectors
subV, (^-^) :: (Zip f, Num s) => f s -> f s -> f s
(^-^) = zipWith (-)
subV = (^-^)
{-# INLINE (^-^) #-}
{-# INLINE subV #-}

-- | Inner product
dotV, (<.>) :: forall s f. (Zip f, Foldable f, Num s) => f s -> f s -> s
x <.> y = sum (zipWith (*) x y)
dotV = (<.>)
{-# INLINE (<.>) #-}
{-# INLINE dotV #-}

-- | Norm squared
#if 1
normSqr :: forall s f. (Functor f, Foldable f, Num s) => f s -> s
normSqr = sum . fmap sqr
#else
normSqr :: forall s f. (Zip f, Foldable f, Num s) => f s -> s
normSqr u = u <.> u
#endif
{-# INLINE normSqr #-}

-- | Distance squared
distSqr :: forall s f. (Zip f, Foldable f, Num s) => f s -> f s -> s
distSqr u v = normSqr (u ^-^ v)
{-# INLINE distSqr #-}

-- | Outer product
outerV, (>.<) :: (Num s, Functor f, Functor g) => g s -> f s -> g (f s)
x >.< y = (*^ y) <$> x
outerV = (>.<)
{-# INLINE (>.<) #-}
{-# INLINE outerV #-}

-- | Normalize a vector (scale to unit magnitude)
normalizeV :: (Functor f, Foldable f, Floating a) => f a -> f a
normalizeV xs = (/ sum xs) <$> xs
{-# INLINE normalizeV #-}

-- Would I rather prefer swapping the arguments (equivalently, transposing the
-- result)?

-- newtype SumV f a = SumV (f a)
data SumV f a = SumV (f a)

instance HasRep (SumV f a) where
  type Rep (SumV f a) = f a
  abst as = SumV as
  repr (SumV as) = as
  {-# INLINE abst #-}
  {-# INLINE repr #-}

instance (Zeroable f, Zip f, Num a) => Semigroup (SumV f a) where
  (<>) = inAbst2 (^+^)

instance (Zeroable f, Zip f, Num a) => Monoid (SumV f a) where
  mempty = abst zeroV
  mappend = (<>)

sumV :: (Functor m, Foldable m, Zeroable n, Zip n, Num a) => m (n a) -> n a
sumV = repr . fold . fmap SumV
{-# INLINE sumV #-}

{--------------------------------------------------------------------
    Conversion
--------------------------------------------------------------------}

type RepHasV s a = (HasRep a, HasV s (Rep a), V s a ~ V s (Rep a))

class HasV s a where
  type V s a :: * -> *
  toV :: a -> V s a s
  unV :: V s a s -> a
  -- Default via Rep.
  type V s a = V s (Rep a)
  default toV :: RepHasV s a => a -> V s a s
  default unV :: RepHasV s a => V s a s -> a
  toV = toV . repr
  unV = abst . unV
  {-# INLINE toV #-} ; {-# INLINE unV #-}

inV :: forall s a b. (HasV s a, HasV s b) => (a -> b) -> (V s a s -> V s b s)
inV = toV <~ unV

onV :: forall s a b. (HasV s a, HasV s b) => (V s a s -> V s b s) -> (a -> b)
onV = unV <~ toV

onV2 :: forall s a b c. (HasV s a, HasV s b, HasV s c) => (V s a s -> V s b s -> V s c s) -> (a -> b -> c)
onV2 = onV <~ toV

-- Can I replace my HasRep class with Newtype?

-- -- Replace by special cases as needed
-- instance HasV s s where
--   type V s s = Par1
--   toV = Par1
--   unV = unPar1

type IsScalar s = (HasV s s, V s s ~ Par1)

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
  {-# INLINE toV #-} ; {-# INLINE unV #-}

instance OpCon (:*) (Sat (HasV s)) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

instance (HasV s a, HasV s b) => HasV s (a :+ b) where
  type V s (a :+ b) = V s a :+: V s b
  toV (Left  a) = L1 (toV a)
  toV (Right b) = R1 (toV b)
  unV (L1 fs) = Left  (unV fs)
  unV (R1 gs) = Right (unV gs)
  {-# INLINE toV #-} ; {-# INLINE unV #-}

-- instance (HasV s a, HasV s b, Zeroable (V s a), Zeroable (V s b), Num s)
--       => HasV s (a :+ b) where
--   type V s (a :+ b) = V s a :*: V s b
--   toV (Left  a) = toV a :*: zeroV
--   toV (Right b) = zeroV :*: toV b
--   unV (f :*: g) = error "unV on a :+ b undefined" f g

instance (HasV s a, HasV s b, HasV s c) => HasV s (a,b,c)
instance (HasV s a, HasV s b, HasV s c, HasV s d) => HasV s (a,b,c,d)

-- Sometimes it's better not to use the default. I think the following gives more reuse:

-- instance HasV s a => HasV s (Pair a) where
--   type V s (Pair a) = Pair :.: V s a
--   toV = Comp1 . fmap toV
--   unV = fmap unV . unComp1

-- Similarly for other functors

instance HasV s (U1 a)
instance HasV s a => HasV s (Par1 a)
instance (HasV s (f a), HasV s (g a)) => HasV s ((f :*: g) a)
instance (HasV s (g (f a))) => HasV s ((g :.: f) a)

instance HasV s (f a) => HasV s (SumV f a)

instance HasV s a => HasV s (Sum a)
instance HasV s a => HasV s (Product a)
-- TODO: More newtypes

-- Sometimes it's better not to use the default. I think the following gives more reuse:

-- instance HasV s a => HasV s (Pair a) where
--   type V s (Pair a) = Pair :.: V s a
--   toV = Comp1 . fmap toV
--   unV = fmap unV . unComp1

-- Similarly for other functors

class VComp h where
  vcomp :: forall s c. HasV s c :- (HasV s (h c), V s (h c) ~ (h :.: V s c))

#if 1
instance HasV s b => HasV s (a -> b) where
  type V s (a -> b) = (->) a :.: V s b
  toV = Comp1 . fmap toV
  unV = fmap unV . unComp1
  {-# INLINE toV #-} ; {-# INLINE unV #-}
#else
instance HasV s b => HasV s (a -> b) where
  type V s (a -> b) = Map a :.: V s b
  toV = Comp1 . ??
  unV = ?? . unComp1
#endif

instance VComp ((->) a) where vcomp = Sub Dict

#ifdef VectorSized

#if 0
-- Until I work out HasL (g :.: f) or stop using it, restrict elements to s.
instance KnownNat n => HasV s (Vector n s) where
  type V s (Vector n s) = Vector n
  toV = id
  unV = id
  {-# INLINE toV #-}
  {-# INLINE unV #-}
#else
instance (HasV s b, KnownNat n) => HasV s (Vector n b) where
  type V s (Vector n b) = Vector n :.: V s b
  toV = Comp1 . fmapC toV
  unV = fmapC unV . unComp1
  {-# INLINE toV #-}
  {-# INLINE unV #-}
#endif

#else
instance (HasV s b) => HasV s (Vector n b) where
  type V s (Vector n b) = Vector n :.: V s b
  toV = Comp1 . fmapC toV
  unV = fmapC unV . unComp1
  {-# INLINE toV #-}
  {-# INLINE unV #-}
#endif

-- TODO: find a better alternative to using fmapC explicitly here. I'd like to
-- use fmap instead, but it gets inlined immediately, as do all class
-- operations.

-- instance 
-- #ifdef VectorSized
--          KnownNat n =>
-- #endif
--          VComp (Vector n) where vcomp = Sub Dict

#ifndef VectorSized
instance VComp (Vector n) where vcomp = Sub Dict
#endif

#if 0
-- Example default instance

data Pickle a = Pickle a a a

instance HasRep (Pickle a) where
  type Rep (Pickle a) = (a :* a) :* a
  repr (Pickle a b c) = ((a,b),c)
  abst ((a,b),c) = Pickle a b c

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

#if 0

{--------------------------------------------------------------------
    Coercible
--------------------------------------------------------------------}

-- I don't think I need this stuff.

-- As a second default, we can use coercible types.
coerceToV :: forall s a b. (Coercible a b, HasV s b) => a -> V s b s
coerceToV = toV . (coerce :: a -> b)

coerceUnV :: forall s a b. (Coercible a b, HasV s b) => V s b s -> a
coerceUnV = (coerce :: b -> a) . unV

#if 0

#define CoerceHasV(s,ty,rep) \
instance HasV s (rep) => HasV s (ty) where \
  { type V s (ty) = V s (rep) \
  ; toV = coerceToV @ s @ (ty) @ (rep) \
  ; unV = coerceUnV @ s @ (ty) @ (rep) }

newtype Two s = Two (s :* s)

-- instance HasV s s => HasV s (Two s) where
--   type V s (Two s) = V s (s :* s)
--   toV = coerceToV @ s @ (Two s) @ (s :* s)
--   unV = coerceUnV @ s @ (Two s) @ (s :* s)

CoerceHasV(s,Two s,s :* s)

#endif

#endif

{--------------------------------------------------------------------
    Utilities
--------------------------------------------------------------------}
