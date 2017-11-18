{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}
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

-- For ConCat.Inline.ClassOp
{-# OPTIONS_GHC -fplugin=ConCat.Inline.Plugin #-}

-- | Some aggregate operations

module ConCat.Aggregate where

import Prelude hiding (id,(.),curry,uncurry,const,zipWith)
-- import qualified Prelude as P

import qualified Control.Arrow as A
import GHC.Generics ((:.:)(..))

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed (Pointed(..))
import Data.Key (Zip(..))
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(..))

import ConCat.Misc ((:*))
-- import ConCat.Category
import ConCat.Inline.ClassOp (inline)
import ConCat.AltCat
-- import ConCat.Free.Diagonal (Diagonal,diag)

class OkFunctor k h where
  okFunctor :: Ok' k a |- Ok' k (h a)

instance OkFunctor (->) h where okFunctor = Entail (Sub Dict)

instance (OkFunctor k h, OkFunctor k' h)
      => OkFunctor (k :**: k') h where
  okFunctor = inForkCon (okFunctor @k *** okFunctor @k')


class (Functor h, OkFunctor k h) => FunctorCat k h where
  fmapC :: Ok2 k a b => (a -> b) `k` (h a -> h b)

-- TODO: Maybe rename FunctorCat to avoid confusion.

class (Zip h, OkFunctor k h) => ZipCat k h where
  -- zipC :: Ok2 k a b => (h a :* h b) `k` h (a :* b)
  zipWithC :: Ok3 k a b c => (a :* b -> c) `k` (h a :* h b -> h c)

class (Pointed h, OkFunctor k h) => PointedCat k h where
  pointC :: Ok  k a => a `k` h a

-- TODO: eliminate pointC in favor of using tabulate

-- TODO: Try removing Representable h and maybe OkFunctor k h from the
-- superclasses.

-- class DiagCat k h where
--   diagC  :: Ok k a => (a :* a) `k` h (h a)

class SumCat k h where
  sumC :: (Ok k a, Num a) => h a `k` a

instance Functor h => FunctorCat (->) h where
  fmapC = inline fmap

#if 0
instance (Zip h, Representable h) => ZipCat (->) h where
  zipC (as,bs) = tabulate (index as &&& index bs)
instance (Pointed h, Representable h) => PointedCat (->) h where
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

-- TODO: inline for tabulate and index?

#else

instance Zip h => ZipCat (->) h where
  -- zipC = uncurry (inline zip)
  zipWithC :: (a :* b -> c) -> (h a :* h b -> h c)
  zipWithC f = uncurry (inline zipWith (curry f))
instance Pointed h => PointedCat (->) h where
  pointC = inline point

#endif

instance Foldable h => SumCat (->) h where
  sumC = inline sum

-- instance (OkFunctor k h, OkFunctor k' h) => OkFunctor (k :**: k') h where
--   okFunctor = inForkCon (okFunctor @k *** okFunctor @k')

instance (FunctorCat k h, FunctorCat k' h) => FunctorCat (k :**: k') h where
  fmapC = fmapC :**: fmapC
  {-# INLINE fmapC #-}

instance (ZipCat k h, ZipCat k' h) => ZipCat (k :**: k') h where
  -- zipC = zipC :**: zipC
  zipWithC = zipWithC :**: zipWithC
  {-# INLINE zipWithC #-}
instance (PointedCat k h, PointedCat k' h) => PointedCat (k :**: k') h where
  pointC = pointC :**: pointC
  {-# INLINE pointC #-}

-- instance (DiagCat k h, DiagCat k' h) => DiagCat (k :**: k') h where
--   diagC  = diagC :**: diagC
--   {-# INLINE diagC #-}

instance (SumCat k h, SumCat k' h) => SumCat (k :**: k') h where
  sumC   = sumC :**: sumC
  {-# INLINE sumC #-}

class DistributiveCat k g f where
  distributeC :: Ok k a => f (g a) `k` g (f a)

-- TODO: perhaps remove the f parameter:
-- 
-- class DistributiveCat k g where
--   distributeC :: (OkFunctor k f, Ok k a) => f (g a) `k` g (f a)

instance (Distributive g, Functor f) => DistributiveCat (->) g f where
  distributeC = inline distribute

instance (DistributiveCat k g f, DistributiveCat k' g f)
      => DistributiveCat (k :**: k') g f where
  distributeC = distributeC :**: distributeC
  {-# INLINE distributeC #-}

class RepresentableCat k f where
  tabulateC :: Ok k a => (Rep f -> a) `k` f a
  indexC    :: Ok k a => f a `k` (Rep f -> a)

instance Representable f => RepresentableCat (->) f where
  tabulateC = inline tabulate
  indexC    = indexC index

instance (RepresentableCat k h, RepresentableCat k' h)
      => RepresentableCat (k :**: k') h where
  tabulateC = tabulateC :**: tabulateC
  indexC    = indexC    :**: indexC
  {-# INLINE tabulateC #-}
  {-# INLINE indexC #-}

-- Experiment

-- fmap' and liftA2' are class-op-inlining synonyms for fmap and liftA2. Look
-- for a better alternative. See 2017-10-20 notes.

fmap' :: Functor f => (a -> b) -> f a -> f b
fmap' = inline fmap

liftA2' :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2' f as bs = fmap' f as <*> bs
