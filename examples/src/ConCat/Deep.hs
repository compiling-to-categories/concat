{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | 

module ConCat.Deep where

import Prelude hiding (zipWith)

import GHC.TypeLits

import Data.Key
import Data.Vector.Sized (Vector)

import ConCat.Misc
import ConCat.Orphans ()
import ConCat.RAD (gradR)

-- import ConCat.AltCat (Ok2)
-- import ConCat.Free.VectorSpace
-- import ConCat.Free.LinearRow

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type V1 = Vector 10
type V2 = Vector 20
type V3 = Vector 30

elr1 :: (OkL f, OkL g) => f :*: g -> Unop (f :-* g)
elr1 = errGrad linRelu
{-# INLINE elr1 #-}

elr2 :: (OkL f, OkL g, OkL h) => f :*: h -> Unop ((g :-* h) :* (f :-* g))
elr2 = errGrad (linRelu @. linRelu)
{-# INLINE elr2 #-}

elr3 :: (OkL f, OkL g, OkL h, OkL k)
     => f :*: k -> Unop ((h :-* k) :* (g :-* h) :* (f :-* g))
elr3 = errGrad (linRelu @. linRelu @. linRelu)
{-# INLINE elr3 #-}

lr1 :: (OkL f, OkL g) => (f :-* g) -> (f --> g)
lr1 = linRelu
{-# INLINE lr1 #-}

lr2 :: (OkL f, OkL g, OkL h) => f :*: h -> Unop ((g :-* h) :* (f :-* g))
lr2 = errGrad (linRelu @. linRelu)
{-# INLINE lr2 #-}

-- lr3 :: (OkL f, OkL g, OkL h, OkL k)
--     => f :*: k -> Unop ((h :-* k) :* (g :-* h) :* (f :-* g))
-- lr3 = errGrad (linRelu @. linRelu @. linRelu)
-- {-# INLINE lr3 #-}

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

infixr 1 -->
type f --> g = f R -> g R

infixr 7 :*:
type (f :*: g) = f R :* g R

type UnopR f = Unop (f R)

{--------------------------------------------------------------------
    Learning
--------------------------------------------------------------------}

relus :: OkL f => f --> f
relus = fmap (max 0)
{-# INLINE relus #-}

-- Linear followed by RELUs.
linRelu :: forall f g. (OkL f, OkL g) => (f :-* g) -> (f --> g)
-- linRelu l = relus . lapply l
linRelu l = fmap (max 0) . lapply l
{-# INLINE linRelu #-}

errSqr :: (Zip g, Foldable g) => f :*: g -> (f --> g) -> R
errSqr (a,b) h = distSqr b (h a)
{-# INLINE errSqr #-}

errGrad :: OkL g => (p -> f --> g) -> f :*: g -> Unop p
errGrad h sample = gradR (errSqr sample . h)
{-# INLINE errGrad #-}

infixr 9 @.
(@.) :: (p -> b -> c) -> (q -> a -> b) -> (p :* q -> a -> c)
(f @. g) (x,y) = f x . g y
{-# INLINE (@.) #-}

{--------------------------------------------------------------------
    Simple linear algebra
--------------------------------------------------------------------}

type OkL f = (Zip f, Foldable f)

infixr 1 :-*
-- | Linear map from a R to b R
type (f :-* g) = g (f R)

infixl 7 <.>
-- | Dot product
(<.>) :: OkL f => f R -> f R -> R
x <.> y = sum (zipWith (*) x y)
{-# INLINE (<.>) #-}

lapply :: (OkL f, Functor g) => (f :-* g) -> (f --> g)
lapply as a = (<.> a) <$> as
{-# INLINE lapply #-}

-- | Norm squared
normSqr :: forall f. OkL f => f R -> R
normSqr = sum . fmap sqr
{-# INLINE normSqr #-}

-- | Distance squared
distSqr :: forall f. OkL f => f R -> f R -> R
distSqr u v = normSqr (zipWith (-) u v)
{-# INLINE distSqr #-}
