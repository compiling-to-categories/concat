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
import ConCat.Additive
import ConCat.AltCat (forkF,joinPF,scale,jamPF)
import ConCat.Orphans ()
import ConCat.RAD (gradR)

{--------------------------------------------------------------------
    Simple linear algebra
--------------------------------------------------------------------}

infixl 7 *^, <.>, >.<

-- | Scale a vector
scaleV, (*^) :: Num s => s -> s :^ n -> s :^ n
s *^ v = scale s <$> v
scaleV = (*^)
{-# INLINE (*^) #-}

-- | "Matrix"
infixr 1 --*
type a --* b = (R :^ a) :^ b

infixr 1 -->
type a --> b = R :^ a -> R :^ b

-- dot' :: ((s -> s) :^ a) -> (s :^ a -> s)
-- dot' = joinPF

-- | Inner product
dotV,(<.>) :: (IxSummable a, Additive s, Num s) => s :^ a -> s :^ a -> s
(<.>) = joinPF . fmap scale
dotV = (<.>)
{-# INLINE (<.>) #-}
{-# INLINE dotV #-}

-- | Outer product
outerV, (>.<) :: Num s => s :^ m -> s :^ n -> (s :^ n) :^ m
(u >.< v) m n = u m `scale` v n
outerV = (>.<)
{-# INLINE (>.<) #-}
{-# INLINE outerV #-}

lap' :: (IxSummable a, Additive z)
     => ((z -> z) :^ a) :^ b -> (z :^ a -> z :^ b)
lap' = forkF . fmap joinPF

-- | Apply a linear map
lap :: (IxSummable a, Additive s, Num s)
    => (s :^ a) :^ b -> (s :^ a -> s :^ b)
lap = lap' . (fmap.fmap) scale

-- lap :: (a --* b) -> (a --> b)

-- NOTE: lap' and lap' depend on the bogus IxCoproductPCat (->) instance
-- in ConCat.Category. Okay if we translate to another category. I'll find a
-- more principled way.

-- TODO: maybe constrain a and b.

normSqr :: (IxSummable n, Additive s, Num s) => s :^ n -> s
normSqr u  = u <.> u
{-# INLINE normSqr #-}

-- | Distance squared
distSqr :: (IxSummable n, Additive s, Num s) => s :^ n -> s :^ n -> s
distSqr u v = normSqr (u - v)
{-# INLINE distSqr #-}

-- The normSqr and distSqr definitions rely on Num instances on functions.

{--------------------------------------------------------------------
    Learning
--------------------------------------------------------------------}

-- | Linear followed by RELUs.
linRelu :: IxSummable a
        => (a --* b) -> (a --> b)
linRelu = (result.result.fmap) (max 0) lap
{-# INLINE linRelu #-}

-- linRelu l = fmap (max 0) . lap l

-- TODO: add a constant ("bias") term. Use "--+*" or "--+" to notate.

errSqr :: IxSummable b => R :^ a :* R :^ b -> (a --> b) -> R
errSqr (a, b) h = distSqr b (h a)
{-# INLINE errSqr #-}

errGrad :: IxSummable b => (p -> a --> b) -> R :^ a :* R :^ b -> Unop p
errGrad h sample = gradR (errSqr sample . h)
{-# INLINE errGrad #-}

infixr 9 @.
(@.) :: (p -> b -> c) -> (q -> a -> b) -> (p :* q -> a -> c)
(f @. g) (p,q) = f p . g q
{-# INLINE (@.) #-}

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

lr1 :: IxSummable a => (a --* b)  ->  (a --> b)
lr1 = linRelu
{-# INLINE lr1 #-}

lr2 :: (IxSummable a, IxSummable b)
    => (b --* c) :* (a --* b)  ->  (a --> c)
lr2 = linRelu @. linRelu
{-# INLINE lr2 #-}

lr3 :: (IxSummable a, IxSummable b, IxSummable c)
    => (c --* d) :* (b --* c) :* (a --* b)  ->  (a --> d)
lr3 = linRelu @. linRelu @. linRelu
{-# INLINE lr3 #-}
