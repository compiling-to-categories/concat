{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

-- | Typeclass for mimimum and maximum on functors
-- use with
-- import Prelude hiding (minimum, maximum)

module ConCat.MinMax(MinMax(..), MinMaxRep(..)) where

import Prelude hiding (minimum, maximum)
import GHC.TypeLits
import qualified Data.Vector as DataVector
import Data.Vector.Generic.Sized as Vector
import qualified Data.Vector.Generic as VectorGeneric
import Data.Functor.Rep (Representable(..))

class Ord a => MinMax f a where
  minimum :: f a -> a
  maximum :: f a -> a

instance (VectorGeneric.Vector v a, Ord a, n ~ (m + 1)) => MinMax (Vector v n) a where
  minimum = Vector.minimum
  maximum = Vector.maximum

class (Ord a, Representable f) => MinMaxRep f a where
  minimumRep :: f a -> (Rep f, a)
  maximumRep :: f a -> (Rep f, a)
  
instance (Ord a, KnownNat n, n ~ (m + 1)) => MinMaxRep (Vector DataVector.Vector n) a where
  minimumRep v =
    let i = Vector.minIndex v
    in (i, Vector.index v i)
  maximumRep v =
    let i = Vector.maxIndex v
    in (i, Vector.index v i)

