{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Late-inlining counterparts to ConCat.Aggregate

module ConCat.AltAggregate (module ConCat.AltAggregate, module C) where

import Prelude hiding (id,(.),curry,uncurry,const,zip)

import GHC.TypeLits (KnownNat)

import Data.Functor.Rep (Representable(..))
import Data.Finite (Finite)
import Data.Vector.Sized (Vector)

import ConCat.Misc ((:*))
import ConCat.Aggregate
  (FunctorCat,LinearCat,SumCat,DistributiveCat,RepresentableCat)
import qualified ConCat.Aggregate as C
import ConCat.AltCat

#include "ConCat/Ops.inc"

Op0(fmapC , (FunctorCat k h, Ok2 k a b) => (a -> b) `k` (h a -> h b))
Op0(zipC  , (LinearCat k h, Ok2 k a b)  => (h a :* h b) `k` h (a :* b))
Op0(pointC, (LinearCat k h, Ok k a)     => a `k` h a)
Op0(sumC  , (SumCat k h, Ok k a, Num a) => h a `k` a)

Op0(distributeC, (DistributiveCat k g f, Ok k a) => f (g a) `k` g (f a))
Op0(tabulateC  , (RepresentableCat k f , Ok k a) => (Rep f -> a) `k` f a)
Op0(indexC     , (RepresentableCat k f , Ok k a) => f a `k` (Rep f -> a))

fmapC' :: forall k h a b. (FunctorCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
        => (a `k` b) -> (h a `k` h b)
fmapC' f = funConst (fmapC . constFun f)
             <+ okExp     @k @(h a) @(h b)
             <+ okFunctor @k @h @a
             <+ okFunctor @k @h @b
             <+ okExp     @k @a @b

--                            f  :: a `k` b
--                   constFun f  :: () `k` (a -> b)
--           fmapC . constFun f  :: () `k` (h a -> h b)
-- funConst (fmapC . constFun f) :: h a `k` h b

unzipC :: forall k h a b. (FunctorCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
       => h (a :* b) `k` (h a :* h b)
unzipC = fmapC' exl &&& fmapC' exr
           <+ okFunctor @k @h @(a :* b)
           <+ okFunctor @k @h @a
           <+ okFunctor @k @h @b
           <+ okProd    @k @a @b
{-# INLINE unzipC #-}

zapC :: forall k h a b.
        (FunctorCat k h, LinearCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
     => (h (a -> b) :* h a) `k` h b
zapC = fmapC' apply . zipC
         <+ okFunctor @k @h @((a -> b) :* a)
         <+ okProd    @k    @(h (a -> b)) @(h a)
         <+ okFunctor @k @h @(a -> b)
         <+ okFunctor @k @h @a
         <+ okFunctor @k @h @b
         <+ okProd    @k    @(a -> b) @a
         <+ okExp     @k    @a @b
{-# INLINE zapC #-}

-- TODO: Is there any value to defining utility functions like unzipC and zapC
-- in categorical generality? Maybe df only for functions, but still using the
-- categorical building blocks. Later extend to other categories by translation,
-- at which point the Ok constraints will be checked anyway.

collectC :: (Representable g, Functor f) => (a -> g b) -> f a -> g (f b)
collectC f = distributeC . fmapC f
{-# INLINE collectC #-}

{-# RULES

"fmap id" uncurry fmapC . (curry exr &&& id) = id

 #-}

-- -- Names are in transition

-- tabulateC :: ArrayCat k n b => Exp k (Finite n) b `k` Arr n b
-- tabulateC = array

-- indexC :: ArrayCat k n b => Arr n b `k` Exp k (Finite n) b
-- indexC = curry arrAt


-- Variant of 'distributeRep' from Data.Functor.Rep
-- TODO: Generalize from Vector.

-- distributeRepC :: ( -- Representable f, Functor w,
--                     f ~ Vector n, KnownNat n, Representable w
--                   )
--                => w (f a) -> f (w a)

-- distributeRepC :: ( -- Representable f, Functor w,
--                     w ~ Vector n, KnownNat n -- , Representable w
--                   )
--                => w (f a) -> f (w a)

-- distributeRepC wf = tabulateC (\k -> fmapC (`indexC` k) wf)

type Diagonal h = (Representable h, Eq (Rep h))

diag :: Diagonal h => a -> a -> h (h a)
diag z o = tabulateC (\ i -> tabulateC (\ j -> if i == j then o else z))
{-# INLINE diag #-}
