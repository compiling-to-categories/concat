-- -*- flycheck-disabled-checkers: '(haskell-ghc haskell-stack-ghc); -*-

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}
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
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-uniques #-}

-- {-# OPTIONS_GHC -dsuppress-module-prefixes #-}

-- {-# OPTIONS_GHC -dcore-lint #-}

-- {-# OPTIONS_GHC -dsuppress-all #-}
-- {-# OPTIONS_GHC -dsuppress-type-applications -dsuppress-coercions #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}

{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}

-- When I list the plugin in the test suite's .cabal target instead of here, I get
--
--   <command line>: Could not find module ‘ConCat.Plugin’
--   It is a member of the hidden package ‘concat-0.0.0’.
--   Perhaps you need to add ‘concat’ to the build-depends in your .cabal file.

module Basic (tests) where

import Prelude hiding (Float,Double)

import Data.Tuple (swap)
import Distribution.TestSuite

import ConCat.Misc (Unop,Binop)
import ConCat.Category (ccc,Uncurriable(..))
import ConCat.Circuit ((:>))
import ConCat.RunCircuit (go,Okay)
import ConCat.Float

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

--   , tst (fst @Bool @Int)

--   , tst not

--   , tst (negate :: Unop Int)

--   , tst (negate :: Unop Float)

--   , tst (negate :: Unop Float)

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

  , tst (sin :: Unop Double)

--   , tst (\ (_ :: ()) -> 1 :: Int)

--   , test "fmap Pair" (fmap not :: Unop (Pair Bool))

--   , test "negate" (\ x -> negate x :: Int)
--   , test "succ" (\ x -> succ x :: Int)
--   , test "pred" (pred :: Unop Int)

--   , test "q0"  (\ x -> x :: Int)
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

--   , tst (\ (_x :: Int) -> not)
--   , tst (\ (_ :: Bool) -> negate :: Unop Int)
--   , tst (\ f -> f True :: Bool)

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

tst :: Okay a b => (a -> b) -> Test
tst _ = error "test called"
{-# NOINLINE tst #-}

test :: Okay a b => String -> (a -> b) -> Test
test _ _ = error "test called"
{-# NOINLINE test #-}

{-# RULES "tst" forall f. tst f = test "test" f #-}
{-# RULES "test" forall s f. test s f = mkTest (go s f) #-}

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

{--------------------------------------------------------------------
    Support for fancier tests
--------------------------------------------------------------------}

-- data Pair a = a :# a deriving Functor

-- instance Uncurriable k a (Pair b)
