{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | 

module ConCat.GradientDescent where

import Data.Function (on)
import Data.List (iterate,unfoldr)

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

follow :: (HasV R a, Zip (V R a)) => R -> (a -> a) -> a -> [a]
follow gamma f' = iterate (\ a -> a ^+^ gamma *^ f' a)
-- {-# INLINE follow #-}

gradientDescent :: (HasV R a, Zip (V R a)) => R -> (a -> R) -> a -> [a]
gradientDescent gamma f = follow gamma (negateV . gradient f)
{-# INLINE gradientDescent #-}

minimize :: forall a. (HasV R a, Zip (V R a), Eq a) => R -> (a -> R) -> a -> a
minimize = (fmap.fmap.fmap) fst minimize'
-- minimize gamma f a = fst (minimize' gamma f a)
{-# INLINE minimize #-}

-- Track number of steps
minimize' :: forall a. (HasV R a, Zip (V R a), Eq a)
          => R -> (a -> R) -> a -> (a,Int)
minimize' gamma f a = limit (gradientDescent gamma f a)
{-# INLINE minimize' #-}

limit :: Eq a => [a] -> (a,Int)
limit = go 1
 where
   go !n (a:a':as) | a == a'   = (a,n)
                   | otherwise = go (n+1) (a':as)
   go  _ _                     = error "limit: finite"

-- gd1 :: [R]
-- gd1 = gradientDescent 0.1 (\ x -> x*x) 0.5
-- {-# INLINE gd1 #-}

fixEq :: Eq a => Unop (Unop a)
fixEq = fixBy (==)

fixBy :: (a -> a -> Bool) -> Unop (Unop a)
fixBy eq next = go
 where
   go a | a' `eq` a = a'
        | otherwise = go a'
    where
      a' = next a

fixN :: Eq a => Unop a -> a -> (a,Int)
fixN = fixByN (==)

-- Add step number
fixByN :: (a -> a -> Bool) -> Unop a -> a -> (a,Int)
fixByN eq next a0 = fixBy (eq `on` fst) next' (a0,0)
 where
   next' (a,!n) = (next a, n+1)

-- Track gradient values
follow' :: (HasV R a, Zip (V R a)) => R -> (a -> a) -> a -> [(a,a)]
follow' gamma f' = unfoldr (Just . g)
 where
   g a = ((a ^+^ gamma *^ a',a'), a') where a' = f' a

-- -- With gradient and steps
-- minimize'' :: (HasV R a, Zip (V R a), Eq a) => R -> (a -> R) -> a -> ((a,a),Int)
-- minimize'' gamma f a0 = fixByN ((==) `on` fst) next (a0, f' a0)
--  where
--    f' = gradient f
--    next a = ((a ^+^ gamma *^ a',a'), a') where a' = f' a
-- {-# INLINE minimize'' #-}

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- The vector operations in VectorSpace are on free vector spaces, so define
-- counterparts on regular values.

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

