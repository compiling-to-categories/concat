{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Experiment with learning from the notMNIST data set

module ConCat.RegressChoice where

import Data.Key

import ConCat.Misc (R,sqr,Unop,(:*),Yes1)
import ConCat.Free.VectorSpace
-- import ConCat.Free.LinearRow
-- import ConCat.Shaped

import ConCat.AD (gradient)

import ConCat.Choice (choose)

-- First do a simple linear regression

-- | Slope/intercept form of a line: y = m * x + b
type Line = (R,R)

type Fun = R -> R

-- -- | 1D linear function in slope/intercept for: y = m * x + b.
-- -- Defines a family of functions.
-- line :: Line -> Fun
-- line (m,b) x = m * x + b

-- Choose a 1D linear function. To be re-interpreted in a ChoiceCat.
chooseLine :: Fun
chooseLine = choose @(HasV R) (\ (m,b) x -> m * x + b)

-- chooseLine' :: forall con. Fun
-- chooseLine' = choose @con (\ (m,b) x -> m * x + b)

type Sample = (R,R)

-- | Squared error for a single sample
sqErr :: Sample -> Fun -> R
sqErr (a,b) f = sqr (f a - b)

-- lineErr :: Sample -> Line -> R
-- lineErr s = sqErr s . line

-- -- Given a data sample and candidate line, yield a delta moving the line toward the sample
-- step :: Sample -> Line -> Line
-- step s = negateV' @R . gradient (lineErr s)
-- -- step s l = negateV' @R (gradient (lineErr s) l)

-- bestChoice :: Choice (->) 

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

negateV' :: forall s a. (HasV s a, Functor (V s a), Num s) => Unop a
negateV' = onV @s negateV
