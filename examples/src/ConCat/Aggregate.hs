{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
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
-- import qualified Prelude as P

import qualified Control.Arrow as A
import GHC.Generics ((:.:)(..))

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed
import Data.Key (Zip(..))

import Data.Functor.Rep

import ConCat.Misc ((:*))
import ConCat.Category
import ConCat.Free.Diagonal (Diagonal,diag)

-- class OkFunctor k h where okFunctor :: Ok' k a |- Ok' k (h a)

-- instance OkFunctor (->) h where okFunctor = Entail (Sub Dict)

class OkFunctor k h => LinearCat k h where
  fmapC  :: Ok2 k a b => (a -> b) `k` (h a -> h b)
  zipC   :: Ok2 k a b => (h a :* h b) `k` h (a :* b)
  pointC :: Ok  k a => a `k` h a

-- TODO: Maybe move fmapC out to a FunctorCat, since it doesn't need
-- Representable.

-- TODO: Try removing Representable h and maybe OkFunctor k h from the
-- superclasses.

class DiagCat k h where
  diagC  :: Ok k a => (a :* a) `k` h (h a)

class SumCat k h where
  sumC :: (Ok k a, Num a) => h a `k` a

instance Representable h => LinearCat (->) h where
  fmapC = fmap
  zipC (as,bs) = tabulate (index as &&& index bs)
  pointC a = tabulate (const a)

-- Overlapping instances for ConCat.Misc.Yes1 (Rep h)
--   arising from a use of ‘&&&’
-- Matching instances:
--   instance [safe] forall k (a :: k). ConCat.Misc.Yes1 a
--     -- Defined at /Users/conal/Haskell/concat/classes/src/ConCat/Misc.hs:123:10
-- There exists a (perhaps superclass) match:
--   from the context: Representable h
--     bound by the instance declaration
--     at /Users/conal/Haskell/concat/examples/src/ConCat/Aggregate.hs:55:10-44
--   or from: Ok2 (->) a b
--     bound by the type signature for:
--                zipC :: Ok2 (->) a b => h a :* h b -> h (a :* b)

instance (Representable h, Eq (Rep h)) => DiagCat (->) h where
  diagC (z,o) = unComp1 (tabulate (\ (h,j) -> if h == j then o else z))

-- TODO: maybe move diagC to a new class, since it's the only method that needs
-- Eq (Rep h).

instance Foldable h => SumCat (->) h where
  sumC = sum

-- instance (OkFunctor k h, OkFunctor k' h) => OkFunctor (k :**: k') h where
--   okFunctor = inForkCon (okFunctor @k *** okFunctor @k')

instance (LinearCat k h, LinearCat k' h) => LinearCat (k :**: k') h where
  fmapC  = fmapC  :**: fmapC
  zipC   = zipC   :**: zipC
  pointC = pointC :**: pointC
  {-# INLINE fmapC #-}
  {-# INLINE zipC #-}
  {-# INLINE pointC #-}

instance (DiagCat k h, DiagCat k' h) => DiagCat (k :**: k') h where
  diagC  = diagC  :**: diagC
  {-# INLINE diagC #-}

instance (SumCat k h, SumCat k' h) => SumCat (k :**: k') h where
  sumC   = sumC   :**: sumC
  {-# INLINE sumC #-}


class DistributiveCat k g f where
  distributeC :: f (g a) `k` g (f a)

class RepresentableCat k f a where
  tabulateC :: (Rep f -> a) `k` f a
  indexC    :: f a `k` (Rep f -> a)
