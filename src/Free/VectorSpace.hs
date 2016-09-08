{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wall #-}

-- | Vector spaces as zippable functors

module Free.VectorSpace where

import Prelude hiding (zipWith)
import Data.Foldable (fold)
import Data.Pointed
import Data.Key (Zip(..))
import GHC.Generics (Par1(..),(:*:)(..))

{--------------------------------------------------------------------
    Vector space basics
--------------------------------------------------------------------}

infixl 7 *^
infixl 6 ^+^

-- Zero vector
zeroV :: (Pointed f, Num a) => f a
zeroV = point 0

-- TODO: Replace Num constraints with Ring or SemiRing

-- Scale a vector
(*^) :: (Functor f, Num a) => a -> f a -> f a
s *^ v = (s *) <$> v

-- Add vectors
(^+^) :: (Zip f, Num a) => f a -> f a -> f a
(^+^) = zipWith (+)

newtype SumV f a = SumV { getSumV :: f a }

instance (Pointed f, Zip f, Num a) => Monoid (SumV f a) where
  mempty = SumV zeroV
  SumV u `mappend ` SumV v = SumV (u ^+^ v)

sumV :: (Functor m, Foldable m, Pointed n, Zip n, Num a) => m (n a) -> n a
sumV = getSumV . fold . fmap SumV

{--------------------------------------------------------------------
    Linear maps
--------------------------------------------------------------------}

-- Linear map from m r to n r
infixr 1 :-*
type (m :-* n) r = m (n r)

-- TODO: consider instead
-- 
--   type Linear = (:.:)
-- 
-- so that Linear itself forms a vector space.

-- Apply a linear map
linear :: (Zip m, Foldable m, Zip n, Pointed n, Num r)
       => (m :-* n) r -> m r -> n r
linear ns m = sumV (zipWith (*^) m ns)

zeroL :: (Pointed m, Pointed n, Num r) => (m :-* n) r
zeroL = point zeroV


{--------------------------------------------------------------------
    Affine maps
--------------------------------------------------------------------}

-- Affine map from m r to n r
type Affine m n r = (m :*: Par1 :-* n) r

-- Apply an affine map
affine :: (Zip m, Foldable m, Zip n, Pointed n, Num r)
       => Affine m n r -> m r -> n r
affine ns' m = linear ns' (m :*: Par1 1)

-- Compose affine transformations
(@..) :: (Zip n, Zip o, Pointed o, Foldable n, Num r, Functor m)
      => Affine n o r -> Affine m n r -> Affine m o r
no @.. mn = affine no <$> mn
