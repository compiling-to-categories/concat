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
type a --* b = (R :^ a) :^ b

infixr 1 -->
type a --> b = R :^ a -> R :^ b

-- dot' :: ((s -> s) :^ a) -> (s :^ a -> s)
-- dot' = joinPF

dot :: Num s => s :^ a -> (s :^ a -> s)
dot = joinPF . fmap scale

lap' :: ((R -> R) :^ a) :^ b -> (a --> b)
lap' = forkF . fmap joinPF

-- | Apply a linear map
lap :: (a --* b) -> (a --> b)
lap = lap' . (fmap.fmap) scale

-- NOTE: lap' and lap' depend on the bogus IxCoproductPCat (->) instance
-- in ConCat.Category. Okay if we translate to another category. I'll find a
-- more principled way.

-- TODO: maybe constrain a and b.

normSqr :: Num s => s :^ b -> s
normSqr' u  = u `dot` u
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
linRelu :: (a --* b) -> (a --> b)
linRelu = (result.result.fmap) (max 0) lap
{-# INLINE linRelu #-}

-- linRelu l = fmap (max 0) . lap l

errSqr :: R :^ a :* R :^ b -> (a --> b) -> R
errSqr (a, b) h = distSqr b (h a)
{-# INLINE errSqr #-}

errGrad :: (p -> a --> b) -> R :^ a :* R :^ b -> Unop p
errGrad h sample = gradR (errSqr sample . h)
{-# INLINE errGrad #-}

infixr 9 @.
(@.) :: (p -> b -> c) -> (q -> a -> b) -> (p :* q -> a -> c)
(f @. g) (p,q) = f p . g q
{-# INLINE (@.) #-}

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

lr1 :: (a --* b)  ->  (a --> b)
lr1 = linRelu
{-# INLINE lr1 #-}

lr2 :: (b --* c) :* (a --* b)  ->  (a --> c)
lr2 = linRelu @. linRelu
{-# INLINE lr2 #-}

lr3 :: (c --* d) :* (b --* c) :* (a --* b)  ->  (a --> d)
lr3 = linRelu @. linRelu @. linRelu
{-# INLINE lr3 #-}


