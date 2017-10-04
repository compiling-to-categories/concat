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
-- I can limit to Arr i in Circuit if necessary.

class OkArr k i where okArr :: Ok' k a |- Ok' k (Arr i a)

instance OkArr (->) i where okArr = Entail (Sub Dict)

class OkArr k i => LinearCat k i where
  -- diagC :: a -> (a `k` Arr i (Arr i a))
  fmapC  :: Ok2 k a b => (a -> b) `k` (Arr i a -> Arr i b)
  zipC   :: Ok2 k a b => (Arr i a :* Arr i b) `k` Arr i (a :* b)
  sumC   :: (Ok k a, Num a) => Arr i a `k` a
  pointC :: Ok k a => a `k` Arr i a

instance LinearCat (->) i where
  -- diagC = diag
  fmapC  = fmap
  zipC   = uncurry zip
  sumC   = sum
  pointC = point

instance (OkArr k i, OkArr k' i) => OkArr (k :**: k') i where
  okArr = inForkCon (okArr @k *** okArr @k')

instance (LinearCat k i, LinearCat k' i) => LinearCat (k :**: k') i where
  fmapC  = fmapC  :**: fmapC
  zipC   = zipC   :**: zipC
  sumC   = sumC   :**: sumC
  pointC = pointC :**: pointC
