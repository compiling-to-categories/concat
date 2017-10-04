{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Late-inlining counterparts to ConCat.Aggregate

module ConCat.AltAggregate (module ConCat.AltAggregate, module C) where

import Prelude hiding (id,(.),curry,uncurry,const,zip)

import ConCat.Misc ((:*))
import ConCat.Aggregate (LinearCat,PointedCat,OkArr(..))
import qualified ConCat.Aggregate as C
import ConCat.AltCat

#include "ConCat/Ops.inc"

-- Op0(zeroC, (LinearCat k i, Ok k a, Num a) => () `k` Arr i a)
Op0(fmapC, (LinearCat k i, Ok2 k a b) => (a -> b) `k` (Arr i a -> Arr i b))
Op0(zipC , (LinearCat k i, Ok2 k a b) => (Arr i a :* Arr i b) `k` Arr i (a :* b))
Op0(sumC , (LinearCat k i, Ok k a, Num a) => Arr i a `k` a)

-- {-# RULES "ccc/fmapC" toCcc' fmapC = fmapC #-}

fmapC' :: forall k i a b. (LinearCat k i, TerminalCat k, ClosedCat k, Ok2 k a b)
        => (a `k` b) -> (Arr i a `k` Arr i b)
fmapC' f = funConst (fmapC . constFun f)
             <+ okExp @k @(Arr i a) @(Arr i b)
             <+ okArr @k @i @a
             <+ okArr @k @i @b
             <+ okExp @k @a @b

--                            f  :: a `k` b
--                   constFun f  :: () `k` (a -> b)
--           fmapC . constFun f  :: () `k` (Arr i a -> Arr i b)
-- funConst (fmapC . constFun f) :: Arr i a `k` Arr i b

unzipC :: forall k i a b. (LinearCat k i, TerminalCat k, ClosedCat k, Ok2 k a b)
       => Arr i (a :* b) `k` (Arr i a :* Arr i b)
unzipC = fmapC' exl &&& fmapC' exr
           <+ okArr  @k @i @(a :* b)
           <+ okArr  @k @i @a
           <+ okArr  @k @i @b
           <+ okProd @k @a @b
{-# INLINE unzipC #-}

zapC :: forall k i a b. (LinearCat k i, TerminalCat k, ClosedCat k, Ok2 k a b)
     => (Arr i (a -> b) :* Arr i a) `k` Arr i b
zapC = fmapC' apply . zipC
         <+ okArr  @k @i @((a -> b) :* a)
         <+ okProd @k    @(Arr i (a -> b)) @(Arr i a)
         <+ okArr  @k @i @(a -> b)
         <+ okArr  @k @i @a
         <+ okArr  @k @i @b
         <+ okProd @k    @(a -> b) @a
         <+ okExp  @k    @a @b
{-# INLINE zapC #-}

Op0(pointC, (PointedCat k h, Ok k a) => a `k` h a)
