{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | 

module ConCat.GradientDescent where

import Data.List (iterate)

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

gradientDescent :: forall a. (HasV R a, Zip (V R a))
                => R -> (a -> R) -> a -> [a]
gradientDescent gamma f = iterate (\ a -> a ^-^ gamma *^ f' a)
 where
   f' = gradient f
{-# INLINE gradientDescent #-}

minimize :: forall a. (HasV R a, Zip (V R a), Eq a)
         => R -> (a -> R) -> a -> a
minimize gamma f a = firstEq (gradientDescent gamma f a)
{-# INLINE minimize #-}

firstEq :: Eq a => [a] -> a
firstEq (a:a':as) | a == a'   = a
                  | otherwise = firstEq (a':as)
firstEq _                     = error "firstEq: finite"

-- Experiment: track number of steps
minimize' :: forall a. (HasV R a, Zip (V R a), Eq a)
          => R -> (a -> R) -> a -> (a,Int)
minimize' gamma f a = firstEq' (gradientDescent gamma f a)
{-# INLINE minimize' #-}

firstEq' :: Eq a => [a] -> (a,Int)
firstEq' = go 1
 where
   go !n (a:a':as) | a == a'   = (a,n)
                   | otherwise = go (n+1) (a':as)
   go  _ _                     = error "firstEq': finite"

-- gd1 :: [R]
-- gd1 = gradientDescent 0.1 (\ x -> x*x) 0.5
-- {-# INLINE gd1 #-}

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- The vector operations in VectorSpace are on free vector spaces, so define
-- counterparts on regular values.

infixl 7 *^
infixl 6 ^-^

(*^) :: (HasV R a, Functor (V R a)) => R -> Unop a
(*^) s = onV ((V.*^) s)

(^-^) :: forall a. (HasV R a, Zip (V R a)) => Binop a
(^-^) = onV2 ((V.^-^) :: Binop (V R a R))

-- The specialization to R helps with type checking. Generalize if needed.

