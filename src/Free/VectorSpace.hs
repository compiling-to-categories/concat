{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wall #-}

-- | Vector spaces as zippable functors

module Free.VectorSpace where

import Prelude hiding (zipWith)

import GHC.Generics (Par1(..),(:*:)(..))

import Data.Foldable (fold)
import Data.Pointed
import Data.Key (Zip(..))

import Control.Newtype

import Misc (inNew2)

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

newtype SumV f a = SumV (f a)

instance Newtype (SumV f a) where
  type O (SumV f a) = f a
  pack as = SumV as
  unpack (SumV as) = as

instance (Pointed f, Zip f, Num a) => Monoid (SumV f a) where
  mempty = pack zeroV
  mappend = inNew2 (^+^)

sumV :: (Functor m, Foldable m, Pointed n, Zip n, Num a) => m (n a) -> n a
sumV = unpack . fold . fmap SumV

{--------------------------------------------------------------------
    Linear maps
--------------------------------------------------------------------}

-- Linear map from a s to b s
infixr 1 :-*
type (a :-* b) s = a (b s)

-- TODO: consider instead
-- 
--   type Linear = (:.:)
-- 
-- so that Linear itself forms a vector space.

-- Apply a linear map
applyL :: (Zip a, Foldable a, Zip b, Pointed b, Num s)
       => (a :-* b) s -> a s -> b s
applyL bs a = sumV (zipWith (*^) a bs)

zeroL :: (Pointed a, Pointed b, Num s) => (a :-* b) s
zeroL = point zeroV


{--------------------------------------------------------------------
    Affine maps
--------------------------------------------------------------------}

-- Affine map from a s to b s
type Affine a b s = (a :*: Par1 :-* b) s

-- Apply an affine map
affine :: (Zip a, Foldable a, Zip b, Pointed b, Num s)
       => Affine a b s -> a s -> b s
affine bs' a = applyL bs' (a :*: Par1 1)

-- Compose affine transformations
(@..) :: (Zip b, Zip c, Pointed c, Foldable b, Num s, Functor a)
      => Affine b c s -> Affine a b s -> Affine a c s
bc @.. ab = affine bc <$> ab
