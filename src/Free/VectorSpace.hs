{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wall #-}

-- | Vector spaces as zippable functors

module Free.VectorSpace where

import Prelude hiding (zipWith)

-- import GHC.Generics (Par1(..),(:*:)(..))

import Data.Foldable (fold)
import Data.Pointed
import Data.Key (Zip(..))

import Control.Newtype

import Misc (inNew2)

{--------------------------------------------------------------------
    Vector spaces
--------------------------------------------------------------------}

infixl 7 *^, <.>, >.<
infixl 6 ^+^

-- Zero vector
zeroV :: (Pointed f, Num a) => f a
zeroV = point 0

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

instance (Pointed f, Zip f, Num a) => Monoid (SumV f a) where
  mempty = pack zeroV
  mappend = inNew2 (^+^)

sumV :: (Functor m, Foldable m, Pointed n, Zip n, Num a) => m (n a) -> n a
sumV = unpack . fold . fmap SumV
