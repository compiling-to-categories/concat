{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}

------------------------------------------------------------------------------
-- | This module requires all of its exports to be INLINEd so that we can
-- preserve referential transparency in any tests which attempt to use their
-- definitions for 'toCCC'.
module Miscellany where

import Prelude

import GHC.TypeLits ()

import ConCat.Misc ((:*))
import ConCat.AltCat ((:**:)(..),Ok2,U2,toCcc)
import ConCat.Orphans ()
import ConCat.Rebox ()
import ConCat.ADFun (andDerF)
import ConCat.RAD (andDerR, andGradR)
import ConCat.Circuit (GenBuses,(:>))
import ConCat.Syntactic (Syn,render)
import ConCat.RunCircuit (run)
-- import ConCat.Chain (Chain)
-- import ConCat.StackMachine (Stack(..))
import ConCat.StackVM (StackProg(..))

type EC = Syn :**: (:>)

runU2 :: U2 a b -> IO ()
runU2 = print
{-# INLINE runU2 #-}

type GO a b = (GenBuses a, Ok2 (:>) a b)

runSyn :: Syn a b -> IO ()
runSyn syn = putStrLn ('\n' : render syn)
{-# INLINE runSyn #-}

runSynCirc :: GO a b => String -> EC a b -> IO ()
runSynCirc nm (syn :**: circ) = runSyn syn >> runCirc nm circ
{-# INLINE runSynCirc #-}

runCirc :: GO a b => String -> (a :> b) -> IO ()
runCirc nm circ = run nm [] circ
{-# INLINE runCirc #-}

runSynCircDers :: (GO a b, Num b) => String -> (a -> b) -> IO ()
runSynCircDers nm f =
  do runSynCirc nm               $ toCcc $ id       $ f
     runSynCirc (nm ++ "-adf")   $ toCcc $ andDerF  $ f
     runSynCirc (nm ++ "-adr")   $ toCcc $ andDerR  $ f
     runSynCirc (nm ++ "-gradr") $ toCcc $ andGradR $ f
{-# INLINE runSynCircDers #-}

runPrint :: Show b => a -> (a -> b) -> IO ()
runPrint a f = print (f a)
{-# INLINE runPrint #-}

-- Ambiguous type variable ‘z0’ arising from a use of ‘print’
-- prevents the constraint ‘(Show (k (a :* z0) (b :* z0)))’ from being solved.
--
-- runStack :: Stack k a b -> IO ()
-- runStack = print . unStack'

-- runSynStack :: Stack Syn a b -> IO ()
-- runSynStack = print . unStack

-- runChainStack :: Stack (Chain Syn) a b -> IO ()
-- runChainStack = print . unStack

runStack :: StackProg a b -> IO ()
runStack = print

runSynStack :: (Syn :**: StackProg) a b -> IO ()
runSynStack (syn :**: prog) = runSyn syn >> runStack prog

twice :: Num a => a -> a
twice x = x + x
{-# INLINE twice #-}

cosSin :: Floating a => a -> a :* a
cosSin a = (cos a, sin a)
{-# INLINE cosSin #-}

cosSinProd :: Floating a => a :* a -> a :* a
cosSinProd (x,y) = cosSin (x * y)
{-# INLINE cosSinProd #-}

horner :: Num a => [a] -> a -> a
horner []     _ = 0
horner (c:cs) a = c + a * horner cs a
{-# INLINE horner #-}

-- Non-inlining versions:

-- horner coeffs a = foldr (\ w z -> w + a * z) 0 coeffs

-- horner coeffs0 a = go coeffs0
--  where
--    go [] = a
--    go (c:cs) = c + a * go cs

-- foo1 :: R -> L R R R
-- foo1 = coerce
