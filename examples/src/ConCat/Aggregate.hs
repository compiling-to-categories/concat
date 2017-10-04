{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Some aggregate operations

module ConCat.Aggregate where

import Prelude hiding (id,(.),curry,uncurry,const,zip)

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed
import Data.Key (Zip(..))

import ConCat.Misc ((:*))
import ConCat.Category
import ConCat.Free.Diagonal (Diagonal,diag)

-- TODO: generalize back from Arr i to functors

class OkArr k i where okArr :: Ok' k a |- Ok' k (Arr i a)

instance OkArr (->) i where okArr = Entail (Sub Dict)

class OkArr k i => LinearCat k i where
  -- zeroC :: (Num a, Ok k a) => () `k` Arr i a
  -- diagC :: a -> (a `k` Arr i (Arr i a))
  fmapC :: Ok2 k a b => (a -> b) `k` (Arr i a -> Arr i b)
  zipC  :: Ok2 k a b => (Arr i a :* Arr i b) `k` Arr i (a :* b)
  sumC  :: (Ok k a, Num a) => Arr i a `k` a

instance LinearCat (->) i where
  -- zeroC = const zeroArr
  -- diagC = diag
  fmapC = fmap
  zipC  = uncurry zip
  sumC  = sum

-- {-# RULES ccc diag = diagC #-}

-- TODO: orphan instance for Zip (Vector n) in ConCat.Orphans, where Vector n
-- comes from Data.Vector.Sized in the vector-sized package.

instance (OkArr k i, OkArr k' i) => OkArr (k :**: k') i where
  okArr = inForkCon (okArr @k *** okArr @k')

instance (LinearCat k i, LinearCat k' i) => LinearCat (k :**: k') i where
  -- zeroC = zeroC :**: zeroC
  fmapC = fmapC :**: fmapC
  zipC  = zipC  :**: zipC
  sumC  = sumC  :**: sumC

class PointedCat k h where
  pointC :: Ok k a => a `k` h a

instance Pointed h => PointedCat (->) h where
  pointC = point

instance (PointedCat k h, PointedCat k' h) => PointedCat (k :**: k') h where
  pointC = pointC :**: pointC

-- TODO: generalize LinearCat from Arr i back to h.
-- I can limit to Arr i in Circuit.
