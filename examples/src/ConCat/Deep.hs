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

-- | Simple feed-forward deep learning

module ConCat.Deep where

import Prelude hiding (zipWith)

import GHC.TypeLits
import GHC.Generics ((:*:)(..),(:.:)(..))

import Data.Key
import Data.Vector.Sized (Vector)

import ConCat.Misc
import ConCat.Orphans ()
import ConCat.RAD (gradR)

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

infixr 1 -->
type (f --> g) s = f s -> g s

type UnopS f s = Unop (f s)

{--------------------------------------------------------------------
    Simple linear algebra
--------------------------------------------------------------------}

type OkS s = (Num s, Ord s)

infixr 1 +->
type (f +-> g) = forall s. OkS s => f s -> g s

type OkL f = (Zip f, Foldable f)

infixr 1 :-*
-- | Linear map
type a :-* b = b :.: a

infixl 7 <.>
-- | Dot product
(<.>) :: (OkL f, OkS s) => f s -> f s -> s
x <.> y = sum (zipWith (*) x y)
{-# INLINE (<.>) #-}

lapply :: (OkL f, Functor g) => (f :-* g) +-> (f --> g)
lapply (Comp1 as) a = (<.> a) <$> as
{-# INLINE lapply #-}

-- | Norm squared
normSqr :: (OkL f, Num s) => f s -> s
normSqr = sum . fmap sqr
{-# INLINE normSqr #-}

-- | Distance squared
distSqr :: (OkL f, Num s) => f s -> f s -> s
distSqr u v = normSqr (zipWith (-) u v)
{-# INLINE distSqr #-}

{--------------------------------------------------------------------
    Learning
--------------------------------------------------------------------}

relus :: OkL f => f +-> f
relus = fmap (max 0)
{-# INLINE relus #-}

-- Linear followed by RELUs.
linRelu :: forall f g. (OkL f, OkL g) => (f :-* g) +-> (f --> g)
linRelu l = fmap (max 0) . lapply l
{-# INLINE linRelu #-}

errSqr :: (Zip g, Foldable g, Num s) => (f :*: g) s -> (f --> g) s -> s
errSqr (a :*: b) h = distSqr b (h a)
{-# INLINE errSqr #-}

errGrad :: (OkL g, Num s) => (p -> f s -> g s) -> (f :*: g) s -> Unop p
errGrad h sample = gradR (errSqr sample . h)
{-# INLINE errGrad #-}

infixr 9 @.
(@.) :: (p s -> b -> c) -> (q s -> a -> b) -> ((p :*: q) s -> a -> c)
(f @. g) (x :*: y) = f x . g y
{-# INLINE (@.) #-}

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type V1 = Vector 10
type V2 = Vector 20
type V3 = Vector 30

elr1 :: (OkL f, OkL g) => f :*: g +-> UnopS (f :-* g)
elr1 = errGrad linRelu
{-# INLINE elr1 #-}

elr2 :: (OkL f, OkL g, OkL h) => f :*: h +-> UnopS ((g :-* h) :*: (f :-* g))
elr2 = errGrad (linRelu @. linRelu)
{-# INLINE elr2 #-}

elr3 :: (OkL f, OkL g, OkL h, OkL k)
     => f :*: k +-> UnopS ((h :-* k) :*: (g :-* h) :*: (f :-* g))
elr3 = errGrad (linRelu @. linRelu @. linRelu)
{-# INLINE elr3 #-}

lr1 :: (OkL f, OkL g) => (f :-* g) +-> (f --> g)
lr1 = linRelu
{-# INLINE lr1 #-}

lr2 :: (OkL f, OkL g, OkL h) => f :*: h +-> UnopS ((g :-* h) :*: (f :-* g))
lr2 = errGrad (linRelu @. linRelu)
{-# INLINE lr2 #-}

lr3 :: (OkL f, OkL g, OkL h, OkL k)
    => f :*: k +-> UnopS ((h :-* k) :*: (g :-* h) :*: (f :-* g))
lr3 = errGrad (linRelu @. linRelu @. linRelu)
{-# INLINE lr3 #-}
