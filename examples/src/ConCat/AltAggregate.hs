{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Late-inlining counterparts to ConCat.Aggregate

module ConCat.AltAggregate (module ConCat.AltAggregate, module C) where

import Prelude hiding (id,(.),curry,uncurry,const,zip)

import Data.Functor.Rep (Representable(..))

import ConCat.Misc ((:*))
import ConCat.Aggregate (LinearCat,SumCat,DiagCat)
import qualified ConCat.Aggregate as C
import ConCat.AltCat

#include "ConCat/Ops.inc"

Op0(fmapC , (LinearCat k h, Ok2 k a b)  => (a -> b) `k` (h a -> h b))
Op0(zipC  , (LinearCat k h, Ok2 k a b)  => (h a :* h b) `k` h (a :* b))
Op0(pointC, (LinearCat k h, Ok k a)     => a `k` h a)
Op0(sumC  , (SumCat k h, Ok k a, Num a) => h a `k` a)
Op0(diagC , (DiagCat k h, Ok k a)       => (a :* a) `k` h (h a))

fmapC' :: forall k h a b. (LinearCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
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

unzipC :: forall k h a b. (LinearCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
       => h (a :* b) `k` (h a :* h b)
unzipC = fmapC' exl &&& fmapC' exr
           <+ okFunctor @k @h @(a :* b)
           <+ okFunctor @k @h @a
           <+ okFunctor @k @h @b
           <+ okProd    @k @a @b
{-# INLINE unzipC #-}

zapC :: forall k h a b. (LinearCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
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

diag :: forall h a. (Representable h, Eq (Rep h)) => a -> a -> h (h a)
diag = curry diagC
{-# INLINE diag #-}

-- okArr :: forall k i a. Ok' k a |- Ok' k (Arr i a)
-- okArr = okFunctor @k @(Arr i) @a

{-# RULES

"fmap id" uncurry fmapC . (curry exr &&& id) = id

 #-}
