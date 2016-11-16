-- -*- flycheck-disabled-checkers: '(haskell-ghc haskell-stack-ghc); -*-

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE ScopedTypeVariables #-}

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

{-# OPTIONS_GHC -fplugin=ConCat.Plugin -dcore-lint -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-module-prefixes -dsuppress-uniques #-}

{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}

-- When I list the plugin in the test suite's .cabal target instead of here, I get
--
--   <command line>: Could not find module ‘ConCat.Plugin’
--   It is a member of the hidden package ‘concat-0.0.0’.
--   Perhaps you need to add ‘concat’ to the build-depends in your .cabal file.

module Basic (tests) where

import Data.Tuple (swap)
import Distribution.TestSuite

import GHC.Float ()  -- experiment

import ConCat.Misc (ccc,Unop,Binop)
import ConCat.Circuit ((:>))
import ConCat.RunCircuit (go,Okay)

-- Whether to render to a PDF (vs print reified expression)
render :: Bool
render = True -- False

-- -- Experiment: try to force loading of Num Float etc
-- class Num a => Quuz a
-- instance Quuz Float
-- instance Quuz Double

-- For FP & parallelism talk
tests :: IO [Test]
tests = return
  [ nopTest
--   , test not
--   , test (negate :: Unop Int)
--   , test ((+) :: Binop Int)
--   , test ((+) :: Binop Float)
--   , test (recip :: Unop Float)

--   , test ((==) :: Int -> Int -> Bool)
--   , test ((==) :: Float -> Float -> Bool)
--   , test ((==) :: Double -> Double -> Bool)
--   , test ((/=) :: Int -> Int -> Bool)
--   , test ((/=) :: Float -> Float -> Bool)
--   , test ((/=) :: Double -> Double -> Bool)

--   , test ((<) :: Int -> Int -> Bool)
--   , test ((<) :: Float -> Float -> Bool)
--   , test ((<) :: Double -> Double -> Bool)
--   , test ((<=) :: Int -> Int -> Bool)
--   , test ((<=) :: Float -> Float -> Bool)
--   , test ((<=) :: Double -> Double -> Bool)
--   , test ((>) :: Int -> Int -> Bool)
--   , test ((>) :: Float -> Float -> Bool)
--   , test ((>) :: Double -> Double -> Bool)
--   , test ((>=) :: Int -> Int -> Bool)
--   , test ((>=) :: Float -> Float -> Bool)
--   , test ((>=) :: Double -> Double -> Bool)

--   , test ((+) :: Binop Int)
--   , test ((+) :: Binop Float)
--   , test ((+) :: Binop Double)
--   , test ((-) :: Binop Int)
--   , test ((-) :: Binop Float)
--   , test ((-) :: Binop Double)
  
--   , test (recip :: Unop Float)
--   , test (recip :: Unop Double)
--   , test ((/) :: Binop Float)
--   , test ((/) :: Binop Double)

--   , test (exp :: Unop Float)
--   , test (exp :: Unop Double)
--   , test (cos :: Unop Float)
--   , test (cos :: Unop Double)
--   , test (sin :: Unop Float)
--   , test (sin :: Unop Double)

  , test (\ x -> x :: Int)
--   , test (\ (_x :: Int) -> True)
--   , test (\ (_x :: Int) -> not)
--   , test (\ (_ :: Bool) -> negate :: Unop Int)
--   , test (\ (x :: Int) -> negate (x + 1))
--   , test (\ f -> f True :: Bool)
--   , test (\ x -> succ x :: Int)
--   , test (\ x -> x + 4 :: Int)
--   , test (\ x -> x + x :: Int)
--   , test (\ x -> 4 + x :: Int)
--   , test (\ a _b -> a :: Int)
--   , test (\ _a b -> b :: Int)
--   , test (\ a b -> a + b :: Int)
--   , test (\ a b -> b + a :: Int)
  ]

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

-- type Cat = (->)
-- type Cat = (:>)

-- test :: forall a b. (a -> b) -> Test
-- test f = mkTest (ccc @(:>) f)
-- {-# INLINE test #-}
-- -- test _ = error "test called"
-- -- {-# NOINLINE test #-}

-- {-# RULES "test" forall f. test f = mkTest (ccc f) #-}

test :: Okay a => a -> Test
test _ = error "test called"
{-# NOINLINE test #-}

{-# RULES "test" forall a. test a = mkTest (go "test" a) #-}

-- test a = mkTest (go "test" a)
-- {-# INLINE test #-}

mkTest :: IO () -> Test
mkTest doit = Test inst
 where
   inst = TestInstance
            { run       = Finished Pass <$ doit
            , name      = "whatevs"
            , tags      = []
            , options   = []
            , setOption = \_ _ -> Right inst
            }
{-# NOINLINE mkTest #-}

nopTest :: Test
nopTest = Group "nop" False []
