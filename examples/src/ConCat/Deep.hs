{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MonadComprehensions #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

#include "ConCat/Ops.inc"

-- | Simple feed-forward deep learning

module ConCat.Deep where

import Prelude hiding (zipWith)

import GHC.TypeLits ()
import GHC.Generics (Par1(..),(:*:)(..),(:.:)(..))

import Data.Key
import Data.NumInstances.Function ()

import ConCat.Misc
import ConCat.Additive
import ConCat.Orphans ()
import ConCat.RAD (gradR)

{--------------------------------------------------------------------
    Simple linear algebra
--------------------------------------------------------------------}

-- | Generalized matrix
infixr 1 --*
type p --* q = q :.: p

infixl 7 *^, <.>, >.<

-- | Scale a vector
scaleV, (*^) :: (Functor a, Num s) => s -> a s -> a s
-- s *^ v = scale s <$> v
s *^ v = (s *) <$> v
scaleV = (*^)
{-# INLINE (*^) #-}

infixl 7 ^/
(^/) :: (Functor a, Fractional s) => a s -> s -> a s
v ^/ s = recip s *^ v
{-# INLINE (^/) #-}

normalize :: (Summable a, Fractional s, Additive s) => a s -> a s
normalize v = v ^/ sumA v
{-# INLINE normalize #-}

-- | Inner product
dotV,(<.>) :: (Summable a, Additive s, Num s) => a s -> a s -> s
xs <.> ys = sumA (zipWith (*) xs ys)
-- (<.>)  = joinPF . fmap scale
dotV      = (<.>)
{-# INLINE (<.>) #-}
{-# INLINE dotV #-}

-- | Outer product. (Do we want this order of functor composition?)
outerV, (>.<) :: (Functor a, Functor b, Num s) => a s -> b s -> a (b s)
a >.< b = (*^ b) <$> a
outerV  = (>.<)
{-# INLINE (>.<) #-}
{-# INLINE outerV #-}

-- (*^ b)       :: s   -> b s
-- (*^ b) <$> a :: a s -> a (b s)

-- linear' :: (Summable a, Summable b, Additive v)
--         => (a --* b) (u -> v) -> (a u -> b v)
-- linear' = linearApp'
-- linear' = forkF . fmap joinPF
-- {-# INLINE linear' #-}

-- | Apply a linear map
linear :: (Summable a, Summable b, Additive s, Num s)
       => (a --* b) s -> (a s -> b s)
linear (Comp1 ba) a = (<.> a) <$> ba
{-# INLINE linear #-}

-- linear = linearApp
-- linear = forkF . fmap joinPF . (fmap.fmap) scale
-- linear = linear' . (fmap.fmap) scale

type Bump h = h :*: Par1

bump :: Num s => a s -> Bump a s
bump a = a :*: Par1 1

-- | Affine map representation
infixr 1 --+
type a --+ b = Bump a --* b

-- | Affine application
affine :: (Summable a, Summable b, Additive s, Num s)
       => (a --+ b) s -> (a s -> b s)
affine m = linear m . bump
{-# INLINE affine #-}

--        m        :: b (Bump a s)
-- linear m        :: Bump a s -> b s
-- linear m . bump :: a s -> b s

-- TODO: Is there an affine counterpart to linear'?

normSqr :: (Summable n, Additive s, Num s) => n s -> s
normSqr u  = u <.> u
{-# INLINE normSqr #-}

-- | Distance squared
distSqr :: (Summable n, Additive s, Num s) => n s -> n s -> s
distSqr u v = normSqr (zipWith (-) u v)
{-# INLINE distSqr #-}

-- The normSqr and distSqr definitions rely on Num instances on functions.

{--------------------------------------------------------------------
    Learning
--------------------------------------------------------------------}

relus :: (Functor f, Ord a, Num a) => Unop (f a)
relus = fmap (max 0)
{-# INLINE relus #-}

-- | Affine followed by RELUs.
affRelu :: (C2 Summable a b, Ord s, Additive s, Num s)
        => (a --+ b) s -> (a s -> b s)
affRelu l = relus . affine l
{-# INLINE affRelu #-}

-- affRelu = (result.result) relus affine

errSqr :: (Summable b, Additive s, Num s)
       => a s :* b s -> (a s -> b s) -> s
errSqr (a,b) h = distSqr b (h a)
{-# INLINE errSqr #-}

errSqrSampled :: (Summable b, Additive s, Num s)
              => (p s -> a s -> b s) -> a s :* b s -> p s -> s
errSqrSampled h sample = errSqr sample . h
{-# INLINE errSqrSampled #-}

errGrad :: (Summable b, Additive s, Num s)
        => (p s -> a s -> b s) -> a s :* b s -> Unop (p s)
errGrad = (result.result) gradR errSqrSampled
{-# INLINE errGrad #-}

infixr 9 @.
(@.) :: (q s -> b -> c) -> (p s -> a -> b) -> ((q :*: p) s -> a -> c)
(g @. f) (q :*: p) = g q . f p
{-# INLINE (@.) #-}

-- Using q :*: p instead of p :*: q avoids the need for parens when combining
-- several, while giving (@.) the same fixity as (.).

{--------------------------------------------------------------------
    SGD interface
--------------------------------------------------------------------}

-- Single SGD step, from one parameter estimation to the next
step :: (C3 Summable p a b, Additive (p s), Additive s, Num s)
     => s -> (p s -> a s -> b s) -> a s :* b s -> Unop (p s)
step gamma m sample p = p ^+^ gamma *^ errGrad m sample p
{-# INLINE step #-}

-- Multiple SGD steps, from one parameter estimation to another
steps :: (C3 Summable p a b, Additive (p s), Functor f, Foldable f, Additive s, Num s)
      => s -> (p s -> a s -> b s) -> f (a s :* b s) -> Unop (p s)
steps gamma m samples = compose (step gamma m <$> samples)
{-# INLINE steps #-}

--          step gamma m              :: a s :* b s -> Unop (p s)
--          step gamma m <$> samples  :: f (Unop (p s))
-- compose (step gamma m <$> samples) :: Unop (p s)

{--------------------------------------------------------------------
    Temp
--------------------------------------------------------------------}

err1 :: (R -> R) -> R :* R -> R
err1 h (a,b) = sqr (b - h a)
{-# INLINE err1 #-}

err1Grad :: (p -> R -> R) -> R :* R -> Unop p
err1Grad h sample = gradR (\ a -> err1 (h a) sample)
{-# INLINE err1Grad #-}

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

infixr 1 -->
type (a --> b) s = a s -> b s

lr1 :: C2 Summable a b => (a --+ b) R  ->  (a --> b) R
lr1 = affRelu
{-# INLINE lr1 #-}

lr2 :: C3 Summable a b c => ((b --+ c) :*: (a --+ b)) R  ->  (a --> c) R
lr2 = affRelu @. affRelu
{-# INLINE lr2 #-}

lr3 :: C4 Summable a b c d => ((c --+ d) :*: (b --+ c) :*: (a --+ b)) R  ->  (a --> d) R
lr3 = affRelu @. affRelu @. affRelu
{-# INLINE lr3 #-}
