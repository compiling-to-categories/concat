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
{-# OPTIONS_GHC -ddump-rule-rewrites #-}

-- When I list the plugin in the test suite's .cabal target instead of here, I get
--
--   <command line>: Could not find module ‘ConCat.Plugin’
--   It is a member of the hidden package ‘concat-0.0.0’.
--   Perhaps you need to add ‘concat’ to the build-depends in your .cabal file.

module Basic (tests) where

import Data.Tuple (swap)
import Distribution.TestSuite

import ConCat.Misc (ccc)

-- Whether to render to a PDF (vs print reified expression)
render :: Bool
render = True -- False

-- For FP & parallelism talk
tests :: IO [Test]
tests = return
  [ nopTest
  , test (\ x -> x :: Int)
  , test (\ _x -> 3 :: Int)
  , test (\ x -> succ x :: Int)
  , test (\ x -> x + 4 :: Int)
  , test (\ a b -> a + b :: Int)
  , test (\ a b -> b + a :: Int)
  ]

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

test :: forall a b. (a -> b) -> Test
test f = mkTest (ccc @(->) f)
{-# INLINE test #-}
-- test _ = error "test called"
-- {-# NOINLINE test #-}

-- {-# RULES "test" forall f. test f = mkTest (ccc f) #-}

mkTest :: a -> Test
mkTest _a = Test inst
 where
   inst = TestInstance
            { run       = return (Finished Pass)
            , name      = "whatevs"
            , tags      = []
            , options   = []
            , setOption = \_ _ -> Right inst
            }
{-# NOINLINE mkTest #-}

nopTest :: Test
nopTest = Group "nop" False []
