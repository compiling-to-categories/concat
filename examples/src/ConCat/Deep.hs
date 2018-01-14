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
type (m --* n) s = (s :^ m) :^ n

infixr 1 -->
type (m --> n) s = s :^ m -> s :^ n

lapply' :: Num s
        => (m --* n) (s -> s) -> (m --> n) s
lapply' = forkF . fmap joinPF

lapply :: Num s
       => (m --* n) s -> (m --> n) s
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
linRelu :: (Num s, Ord s) => (m --* n) s -> (m --> n) s
linRelu = (result.result.fmap) (max 0) lapply
{-# INLINE linRelu #-}

-- linRelu l = fmap (max 0) . lapply l

errSqr :: (Num s) => s :^ m :* s :^ n -> (m --> n) s -> s
errSqr (a, b) h = distSqr b (h a)
{-# INLINE errSqr #-}

errGrad :: (Num s) => (p -> (m --> n) s) -> (s :^ m :* s :^ n) -> Unop p
errGrad h sample = gradR (errSqr sample . h)
{-# INLINE errGrad #-}

infixr 9 @.
(@.) :: (p -> b -> c) -> (q -> a -> b) -> (p :* q -> a -> c)
(f @. g) (p,q) = f p . g q
{-# INLINE (@.) #-}

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

lr1 :: (m --* n) R -> (m --> n) R
lr1 = linRelu
{-# INLINE lr1 #-}

lr2 :: (n --* o) R :* (m --* n) R -> (m --> o) R
lr2 = linRelu @. linRelu
{-# INLINE lr2 #-}

lr3 :: (o --* p) R :* (n --* o) R :* (m --* n) R -> (m --> p) R
lr3 = linRelu @. linRelu @. linRelu
{-# INLINE lr3 #-}

-- TODO: Wire in R for easy reading. I can generalize later.
-- TODO: replace n, m, o, p, with a, b, c, d.
