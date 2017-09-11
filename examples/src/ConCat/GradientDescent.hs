{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experimenting with formulations of gradient descent minimization

module ConCat.GradientDescent where

import Data.Function (on)
import Data.List (iterate,unfoldr)
import Control.Arrow (first)

import GHC.Generics (Par1(..))

import Control.Newtype (unpack)
import Data.Key (Zip)

import ConCat.Misc (Unop,Binop,R)
import ConCat.AD
import ConCat.Free.VectorSpace (HasV(..),onV,onV2)
import qualified ConCat.Free.VectorSpace as V
import ConCat.Free.LinearRow
import ConCat.Orphans ()
import ConCat.Category (dup)

{--------------------------------------------------------------------
    Minimization via gradient descent
--------------------------------------------------------------------}

maximize, minimize :: (HasV R a, Zip (V R a), Eq a) => R -> D R a R -> a -> a
maximize = (fmap.fmap.fmap) fst maximizeN
minimize = maximize . negate
-- {-# INLINE maximize #-}
-- {-# INLINE minimize #-}

-- | Optimize a function using gradient ascent, with step count.
maximizeN, minimizeN :: (HasV R a, Zip (V R a), Eq a) => R -> D R a R -> a -> (a,Int)
-- maximizeN gamma f = fixN (\ a -> a ^+^ gamma *^ gradient' f a)
-- maximizeN gamma f = chaseN gamma (gradientD f)
maximizeN gamma = chaseN gamma . gradientD
minimizeN = maximizeN . negate
-- {-# INLINE maximizeN #-}
-- {-# INLINE minimizeN #-}

-- TODO: adaptive step sizes

chaseN :: (HasV R a, Zip (V R a), Eq a) => R -> (a -> a) -> a -> (a,Int)
chaseN gamma next = fixN (\ a -> a ^+^ gamma *^ next a)

chase :: (HasV R a, Zip (V R a), Eq a) => R -> Unop (a -> a)
chase = (fmap.fmap.fmap) fst chaseN

-- Experiment: generate list of approximations

-- chaseL :: (HasV R a, Zip (V R a), Eq a) => R -> (a -> a) -> a -> [a]
chaseL :: (HasV R a, Zip (V R a)) => R -> (a -> a) -> a -> [a]
chaseL gamma next = iterate (\ a -> a ^+^ gamma *^ next a)

-- maximizeL, minimizeL :: (HasV R a, Zip (V R a), Eq a) => R -> D R a R -> a -> [a]
maximizeL, minimizeL :: (HasV R a, Zip (V R a)) => R -> D R a R -> a -> [a]
maximizeL gamma = chaseL gamma . gradientD
minimizeL = maximizeL . negate

{--------------------------------------------------------------------
    Fixed points
--------------------------------------------------------------------}

-- Fixed point with comparision
fixBy :: (a -> a -> Bool) -> Unop (Unop a)
fixBy eq next = go
 where
   go a | a' `eq` a = a'
        | otherwise = go a'
    where
      a' = next a

-- Fixed point with comparison and number of steps
fixByN :: (a -> a -> Bool) -> Unop a -> a -> (a,Int)
fixByN eq next a0 = fixBy (eq `on` fst) next' (a0,0)
 where
   next' (a,!n) = (next a, n+1)

-- Fixed point using (==) and number of steps
fixN :: Eq a => Unop a -> a -> (a,Int)
fixN = fixByN (==)

-- Fixed point
fixEq :: Eq a => Unop (Unop a)
fixEq = fixBy (==)

{--------------------------------------------------------------------
    Vector operations
--------------------------------------------------------------------}

-- The vector operations in VectorSpace are on free vector spaces (f s for
-- functor f and scalar field s), so define counterparts on regular values.

infixl 7 *^
infixl 6 ^-^, ^+^

(*^) :: (HasV R a, Functor (V R a)) => R -> Unop a
(*^) s = onV ((V.*^) s)

negateV :: (HasV R a, Functor (V R a)) => Unop a
negateV = ((*^) (-1))
-- negateV = onV V.negateV

(^+^) :: forall a. (HasV R a, Zip (V R a)) => Binop a
(^+^) = onV2 ((V.^+^) :: Binop (V R a R))

(^-^) :: forall a. (HasV R a, Zip (V R a)) => Binop a
(^-^) = onV2 ((V.^-^) :: Binop (V R a R))

-- The specialization to R helps with type checking. Generalize if needed.

