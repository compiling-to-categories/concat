{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE TypeOperators   #-}

{-# OPTIONS_GHC -Wall #-}

------------------------------------------------------------------------------
-- | This module requires all of its exports to be INLINEd so that we can
-- preserve referential transparency in any tests which attempt to use their
-- definitions for 'toCCC'.
module Utils where

import           ConCat.AltCat ((:**:)(..),Ok2,U2)
import           ConCat.Circuit (GenBuses,(:>))
import           ConCat.Misc ((:*),R,Unop)
import           ConCat.Orphans ()
import           ConCat.Rebox ()
import           ConCat.Rep (HasRep(..))
import qualified ConCat.RunCircuit as RC
import           ConCat.Syntactic (Syn,render)
import           GHC.TypeLits ()
import           Prelude hiding (unzip,zip,zipWith)


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
runCirc nm circ = RC.run nm [] circ
{-# INLINE runCirc #-}

runPrint :: Show b => a -> (a -> b) -> IO ()
runPrint a f = print (f a)
{-# INLINE runPrint #-}

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


data Foo = Foo Double

negateFoo :: Unop Foo
negateFoo (Foo x) = Foo (negate x)
{-# INLINE negateFoo #-}

instance HasRep Foo where
  type Rep Foo = R
  abst x = Foo x
  repr (Foo x) = x

  {-# INLINE abst #-}
  {-# INLINE repr #-}


