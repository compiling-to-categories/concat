{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

#include "ConCat/Ops.inc"

-- | Simple feed-forward deep learning

module ConCat.Deep where

import Prelude hiding (zipWith)

import GHC.TypeLits ()
import GHC.Generics ((:*:)(..),(:.:)(..))

import Data.Key
import Data.Vector.Sized (Vector)
import Data.NumInstances.Function ()

import ConCat.Misc
-- import ConCat.Additive
import ConCat.AltCat (forkF,joinPF,scale,jamPF)
import ConCat.Orphans ()
import ConCat.RAD (gradR)

{--------------------------------------------------------------------
    Simple linear algebra
--------------------------------------------------------------------}

-- | "Matrix"
infixr 1 --*
type m --* n = (R :^ m) :^ n

infixr 1 -->
type m --> n = R :^ m -> R :^ n

lapply' :: ((R -> R) :^ m) :^ n -> (m --> n)
lapply' = forkF . fmap joinPF

lapply :: (m --* n) -> (m --> n)
lapply = lapply' . (fmap.fmap) scale

-- NOTE: lapply' and lapply' depend on the bogus IxCoproductPCat (->) instance
-- in ConCat.Category. Okay if we translate to another category. I'll find a
-- more principled way.

-- TODO: maybe constrain m and n.

normSqr :: Num s => s :^ n -> s
normSqr = jamPF . sqr
{-# INLINE normSqr #-}

-- | Distance squared
distSqr :: Num s => s :^ n -> s :^ n -> s
distSqr u v = normSqr (u - v)
{-# INLINE distSqr #-}

-- The normSqr and distSqr definitions rely on Num instances on functions.

{--------------------------------------------------------------------
    Learning
--------------------------------------------------------------------}

-- | Linear followed by RELUs.
linRelu :: (m --* n) -> (m --> n)
linRelu = (result.result.fmap) (max 0) lapply
{-# INLINE linRelu #-}

-- linRelu l = fmap (max 0) . lapply l

errSqr :: R :^ m :* R :^ n -> (m --> n) -> R
errSqr (a, b) h = distSqr b (h a)
{-# INLINE errSqr #-}

errGrad :: (p -> m --> n) -> R :^ m :* R :^ n -> Unop p
errGrad h sample = gradR (errSqr sample . h)
{-# INLINE errGrad #-}

infixr 9 @.
(@.) :: (p -> b -> c) -> (q -> a -> b) -> (p :* q -> a -> c)
(f @. g) (p,q) = f p . g q
{-# INLINE (@.) #-}

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

lr1 :: (m --* n) -> (m --> n)
lr1 = linRelu
{-# INLINE lr1 #-}

lr2 :: (n --* o) :* (m --* n) -> (m --> o)
lr2 = linRelu @. linRelu
{-# INLINE lr2 #-}

lr3 :: (o --* p) :* (n --* o) :* (m --* n) -> (m --> p)
lr3 = linRelu @. linRelu @. linRelu
{-# INLINE lr3 #-}

-- TODO: replace n, m, o, p, with a, b, c, d.
