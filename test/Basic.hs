-- -*- flycheck-disabled-checkers: '(haskell-ghc haskell-stack-ghc); -*-

-- stack build :basic

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- -- TEMP for Pair
-- {-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds   #-}

----------------------------------------------------------------------
-- |
-- Module      :  Basic
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Suite of automated tests
----------------------------------------------------------------------

{-# OPTIONS_GHC -fplugin=ConCat.Plugin -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}

-- {-# OPTIONS_GHC -dsuppress-all #-}
-- {-# OPTIONS_GHC -dsuppress-type-applications -dsuppress-coercions #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}

-- {-# OPTIONS_GHC -dverbose-core2core #-}

{-# OPTIONS_GHC -fsimpl-tick-factor=300 #-} -- default 100

-- When I list the plugin in the test suite's .cabal target instead of here, I get
--
--   <command line>: Could not find module ‘ConCat.Plugin’
--   It is a member of the hidden package ‘concat-0.0.0’.
--   Perhaps you need to add ‘concat’ to the build-depends in your .cabal file.

module Basic (tests) where

import Prelude hiding (Float,Double)   -- ,id,(.),const

import Data.Tuple (swap)
import Distribution.TestSuite

import ConCat.Misc (Unop,Binop,(:*))
import ConCat.Float
import ConCat.Syntactic (Sexp,render)
import ConCat.Circuit (GenBuses)
import qualified ConCat.RunCircuit as RC
import ConCat.RunCircuit (go,Okay,(:>))
import ConCat.ADFun (D,unD)

import ConCat.AltCat (ccc,Uncurriable(..),(:**:)(..))

-- -- Experiment: try to force loading of Num Float etc
-- class Num a => Quuz a
-- instance Quuz Float
-- instance Quuz Double

-- For FP & parallelism talk
tests :: IO [Test]
tests = return
  [ nopTest

--   , tst (id :: Unop Bool)

--   , tst ((\ x -> x) :: Unop Bool)

--   , tst (fst @Bool @Int)

--   , tst (C.exl :: Int :* Bool -> Int)

--   , tst not

--   , tst ((+) :: Binop Int)

--   , tst ((+) 3 :: Unop Int)

--   , tst ((+) 3 :: Unop Float)

--   , tst (||)

--   , tst ((||) True)

--   , tst (const True :: Unop Bool)

--   , tst ((||) False)

--   , tst (negate :: Unop Int)

--   , tst (negate  :: Unop Float)
--   , tst (negateC :: Unop Float)

--   , tst (\ (_ :: ()) -> 1 :: Double)

--   , tst (\ (x,y) -> x + y :: Int)

--   , tst (uncurry ((+) :: Binop Int))

--   , tst ((+) :: Binop Int)

--   , tst ((+) :: Binop Float)

--   , tst (recip :: Unop Float)

--   , tst ((==) :: Int -> Int -> Bool)
--   , tst ((==) :: Float -> Float -> Bool)
--   , tst ((==) :: Double -> Double -> Bool)
--   , tst ((/=) :: Int -> Int -> Bool)
--   , tst ((/=) :: Float -> Float -> Bool)
--   , tst ((/=) :: Double -> Double -> Bool)

--   , tst ((<) :: Int -> Int -> Bool)
--   , tst ((<) :: Float -> Float -> Bool)
--   , tst ((<) :: Double -> Double -> Bool)
--   , tst ((<=) :: Int -> Int -> Bool)
--   , tst ((<=) :: Float -> Float -> Bool)
--   , tst ((<=) :: Double -> Double -> Bool)
--   , tst ((>) :: Int -> Int -> Bool)
--   , tst ((>) :: Float -> Float -> Bool)
--   , tst ((>) :: Double -> Double -> Bool)
--   , tst ((>=) :: Int -> Int -> Bool)
--   , tst ((>=) :: Float -> Float -> Bool)
--   , tst ((>=) :: Double -> Double -> Bool)

--   , tst ((+) :: Binop Int)
--   , tst ((+) :: Binop Float)
--   , tst ((+) :: Binop Double)
--   , tst ((-) :: Binop Int)
--   , tst ((-) :: Binop Float)
--   , tst ((-) :: Binop Double)
  
--   , tst (recip :: Unop Float)
--   , tst (recip :: Unop Double)
--   , tst ((/) :: Binop Float)
--   , tst ((/) :: Binop Double)

--   , tst (exp :: Unop Float)
--   , tst (exp :: Unop Double)
--   , tst (cos :: Unop Float)
--   , tst (cos :: Unop Double)
--   , tst (sin :: Unop Float)
--   , tst (sin :: Unop Double)

--   , tst (\ (_ :: ()) -> 1 :: Int)

--   , test "fmap Pair" (fmap not :: Unop (Pair Bool))

--   , test "negate" (\ x -> negate x :: Int)
--   , test "succ" (\ x -> succ x :: Int)
--   , test "pred" (pred :: Unop Int)

--   , tst (id :: Unop Bool)

--   , tst (\ (x :: Int) -> succ (succ x))

--   , tst ((.) :: Binop (Unop Bool))

--     , tst (succ . succ :: Unop Int)

--     , tst (\ (x :: Int) -> succ (succ x))

--   , tst ((\ (x,y) -> (y,x)) :: Unop (Bool :* Bool))
--   , tst ((,) :: Bool -> Int -> Bool :* Int)

  , test "q0"  (\ x -> x :: Int)
--   , test "q1"  (\ (_x :: Int) -> True)
--   , test "q2"  (\ (x :: Int) -> negate (x + 1))
--   , test "q3"  (\ (x :: Int) -> x > 0)
--   , test "q4"  (\ x -> x + 4 :: Int)
--   , test "q5"  (\ x -> x + x :: Int)
--   , test "q6"  (\ x -> 4 + x :: Int)
--   , test "q7"  (\ (a :: Int) (_b :: Int) -> a)
--   , test "q8"  (\ (_ :: Int) (b :: Int) -> b)
--   , test "q9"  (\ (a :: Float) (b :: Float) -> a + b)
--   , test "q10" (\ (a :: Float) (b :: Float) -> b + a)

--   , test "q7u"  ((\ (a,_) -> a) :: Int :* Int -> Int)
--   , test "q8u"  ((\ (_,b) -> b) :: Int :* Int -> Int)
--   , test "q9u"  ((\ (a,b) -> a + b) :: Float :* Float -> Float)
--   , test "q10u" ((\ (a,b) -> b + a) :: Float :* Float -> Float)

--   , tst (\ (_x :: Int) -> not)
--   , tst (\ (_ :: Bool) -> negate :: Unop Int)
--   , tst (\ f -> f True :: Bool)

  ]

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

type EC = Sexp :**: (:>)

runEC :: GenBuses a => String -> EC a b -> IO ()
runEC s (ex :**: circ) = putStrLn ('\n':render ex) >> RC.run s [] circ

#if 0
-- Circuit interpretation
test :: Okay a b => String -> (a -> b) -> Test
tst  :: Okay a b => (a -> b) -> Test
{-# RULES "circuit" forall s f. test s f = mkTest s (go s f) #-}
#elif 0
-- Syntactic interpretation
test :: String -> (a -> b) -> Test
tst :: (a -> b) -> Test
{-# RULES "syntactic" forall s f.
  test s f = mkTest s (putStrLn ('\n':render (ccc f))) #-}
#elif 0
-- (->), then syntactic
-- With INLINE [3]: "Simplifier ticks exhausted"
test :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "(->); Sexp" forall s f.
   test s f = mkTest s (putStrLn ('\n':render (ccc (ccc f))))
 #-}
#elif 0
-- Syntactic, then uncurries
test :: Uncurriable Sexp a b => String -> (a -> b) -> Test
tst :: Uncurriable Sexp a b => (a -> b) -> Test
{-# RULES "syntactic; uncurries" forall s f.
  test s f = mkTest s (putStrLn ('\n':render (uncurries (ccc f)))) #-}
#elif 0
-- uncurries, then syntactic
-- Fine with INLINE and NOINLINE
test :: Uncurriable (->) a b => String -> (a -> b) -> Test
tst  :: Uncurriable (->) a b => (a -> b) -> Test
{-# RULES "uncurries; Sexp" forall s f.
   test s f = mkTest s (putStrLn ('\n':render (ccc (uncurries f))))
 #-}
#elif 0
-- (->), then uncurries, then syntactic
-- Some trouble with INLINE [3]
test :: Uncurriable (->) a b => String -> (a -> b) -> Test
tst  :: Uncurriable (->) a b => (a -> b) -> Test
{-# RULES "(->); uncurries; Sexp" forall s f.
   test s f = mkTest s (putStrLn ('\n':render (ccc (uncurries (ccc f)))))
 #-}
#elif 0
-- syntactic *and* circuit
test :: GenBuses a => String -> (a -> b) -> Test
tst  :: GenBuses a => (a -> b) -> Test
{-# RULES "Sexp :**: (:>)" forall s f.
   test s f = mkTest s (runEC s (ccc f))
 #-}
#elif 1
-- uncurries, then syntactic *and* circuit
-- OOPS: Core Lint error
test :: (GenBuses (UncDom a b), Uncurriable (->) a b) => String -> (a -> b) -> Test
tst  :: (GenBuses (UncDom a b), Uncurriable (->) a b) => (a -> b) -> Test
{-# RULES "uncurries ; Sexp :**: (:>)" forall s f.
   test s f = mkTest s (runEC s (ccc (uncurries f)))
 #-}
#elif 1
-- (->), then circuit
-- OOPS: "Simplifier ticks exhausted"
test :: Okay a b => String -> (a -> b) -> Test
tst  :: Okay a b => (a -> b) -> Test
{-# RULES "(->); (:>)" forall s f.
   test s f = mkTest s (go s (ccc f))
 #-}
#elif 0
-- Derivative, then syntactic
test :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "test AD" forall s (f :: a -> b).
   -- test s f = mkTest s (putStrLn (render (ccc (unD (ccc f)))))
   test s f = mkTest s (doodleD (ccc f))
 #-}
#else
NOTHING
#endif
test _ = error "test called"
tst  _ = error "tst called"

{-# NOINLINE test #-}
{-# NOINLINE tst #-}

-- {-# RULES "tst" forall f. tst f = test "test" f #-}
{-# RULES "tst" tst = test "test" #-}

mkTest :: String -> IO () -> Test
mkTest nm doit = Test inst
 where
   inst = TestInstance
            { run       = Finished Pass <$ doit
            , name      = nm
            , tags      = []
            , options   = []
            , setOption = \_ _ -> Right inst
            }
-- {-# NOINLINE mkTest #-}

nopTest :: Test
nopTest = Group "nop" False []

{--------------------------------------------------------------------
    Support for fancier tests
--------------------------------------------------------------------}

-- data Pair a = a :# a deriving Functor

-- instance Uncurriable k a (Pair b)
