{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- -- Does this flag make any difference?
-- {-# OPTIONS_GHC -fexpose-all-unfoldings #-}

-- | Regression experiments
module ConCat.Regress where

import ConCat.Misc (R)

import ConCat.AltCat (ccc)

import ConCat.Sized
import ConCat.AD (gradient)
import ConCat.GradientDescent

-- Slope and intercept (m,b)
-- data Line = Line R R
type Line = (R,R)

-- pattern Line :: R -> R -> Line
-- pattern Line m b = (m,b)

-- Semantic function
evalL :: Line -> (R -> R)
evalL (m,b) x = m * x + b
{-# INLINE evalL #-}

type Sample = (R,R)

type FF f = (Functor f, Foldable f, Sized f)

-- Sum of squared errors compared with a given function
ss :: FF f => f Sample -> (R -> R) -> R
ss samples f = sum (sqerr <$> samples)  -- TODO: rewrite
 where
   sqerr (xi,yi) = sqr (yi - f xi)
   sqr x = x * x
{-# INLINE ss #-}

type Metric f = f Sample -> Line -> R

-- Residual sum of squares
rss :: FF f => Metric f
rss samples line = ss samples (evalL line)
{-# INLINE rss #-}

-- Total sum of squares
tss :: FF f => f Sample -> R
tss samples = ss samples (const (mean (snd <$> samples)))
{-# INLINE tss #-}

-- Mean squared error
mse :: FF f => Metric f
mse samples line = rss samples line / fromIntegral (length samples)
{-# INLINE mse #-}

-- R-squared
r2 :: FF f => Metric f
r2 samples line = 1 - rss samples line / tss samples
{-# INLINE r2 #-}

mean :: forall f a. (FF f, Fractional a) => f a -> a
mean as = sum as / fromIntegral (size @f)
-- mean as = sum as / fromIntegral (length as)
{-# INLINE mean #-}

-- I'd like to drop dependency on Sized, replacing size @f with length as. Then
-- we can use lists. The trick is to get all of the operations on samples to be
-- computed at compile time when the samples are known. Currently, mean appears
-- not to be getting unrolled/computed at compile time for lists.

-- | Linear (for now) regression
regress :: Line -> Metric f -> f Sample -> Line
-- regress metric samples = minimize 1 (ccc (metric samples)) (0,0)
regress line0 metric samples =
  chase 1 (gradient (negate . metric samples)) line0
{-# INLINE regress #-}

-- Maybe pass in (metric samples) (Line -> R) instead of metric and samples.

-- -- | Linear (for now) regression
-- -- regress' :: Line -> (Line -> R) -> Line
-- regress' :: a -> (a -> R) -> a
-- regress' line0 eval = chase 1 (gradient (negate . eval)) line0
-- {-# INLINE regress' #-}

-- Hm. Isn't regress' just flip minimize?
