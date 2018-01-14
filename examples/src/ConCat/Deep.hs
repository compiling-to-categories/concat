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
import ConCat.Additive
import ConCat.Orphans ()
import ConCat.RAD (gradR)

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

infixr 1 -->
type f --> g = f R -> g R

-- Missing in GHC.Generics
infixr 1 :->
newtype (f :-> g) s = Fun1 (f s -> g s)

type UnopR f = Unop (f R)

{--------------------------------------------------------------------
    Simple linear algebra
--------------------------------------------------------------------}

type OkL f = (Zip f, Foldable f)

infixr 1 :-*
-- | Linear map
type a :-* b = b :.: a

infixl 7 <.>
-- | Dot product
(<.>) :: (OkL f, Num s, Additive s) => f s -> f s -> s
x <.> y = sumA (zipWith (*) x y)
{-# INLINE (<.>) #-}

-- Apply a linear map
lap :: (OkL f, Functor g, Num s, Additive s) => (f :-* g) s -> (f s -> g s)
lap (Comp1 as) a = (<.> a) <$> as
{-# INLINE lap #-}

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

relus :: (OkL f, Num s, Ord s) => f s -> f s
relus = fmap (max 0)
{-# INLINE relus #-}

-- Linear followed by RELUs.
linRelu :: (OkL f, OkL g, Num s, Additive s, Ord s) => (f :-* g) s -> (f s -> g s)
linRelu l = fmap (max 0) . lap l
{-# INLINE linRelu #-}

errSqr :: (Zip g, Foldable g, Num s) => (f :*: g) s -> (f s -> g s) -> s
errSqr (a :*: b) h = distSqr b (h a)
{-# INLINE errSqr #-}

errGrad :: (OkL g, Num s) => (p -> f s -> g s) -> (f :*: g) s -> Unop p
errGrad h sample = gradR (errSqr sample . h)
{-# INLINE errGrad #-}

infixr 9 @.
(@.) :: (p s -> b -> c) -> (q s -> a -> b) -> ((p :*: q) s -> a -> c)
(f @. g) (x :*: y) = f x . g y
{-# INLINE (@.) #-}

-- TODO: Maybe simplify (:*:) to (*:) and (f :- g) s to g (f s)

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

type V1 = Vector 10
type V2 = Vector 20
type V3 = Vector 30

lr1 :: (OkL f, OkL g) => (f :-* g) R -> (f R -> g R)
lr1 = linRelu
{-# INLINE lr1 #-}

lr2 :: (OkL f, OkL g, OkL h) => ((g :-* h) :*: (f :-* g)) R -> (f R -> h R)
lr2 = linRelu @. linRelu
{-# INLINE lr2 #-}

lr3 :: (OkL f, OkL g, OkL h, OkL k)
    => ((h :-* k) :*: (g :-* h) :*: (f :-* g)) R -> (f R -> k R)
lr3 = linRelu @. linRelu @. linRelu
{-# INLINE lr3 #-}

#if 0
#endif
