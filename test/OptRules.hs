-- -*- flycheck-disabled-checkers: '(haskell-ghc haskell-stack-ghc); -*-

-- stack build :opt-rules

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
-- Module      :  OptRules
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Test optimization rewrite rules
----------------------------------------------------------------------

{-# OPTIONS_GHC -fplugin=ConCat.Plugin -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -dsuppress-idinfo -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

{-# OPTIONS_GHC -dcore-lint #-}

{-# OPTIONS_GHC -dsuppress-all #-}
{-# OPTIONS_GHC -dsuppress-type-applications -dsuppress-coercions #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}

-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}

-- -- ./.stack-work/dist/x86_64-osx/Cabal-1.24.0.0/build/concat-0.1.0.0-3D1T28buysUFAzpaRyQqCE-opt-rules.test/test/OptRules.dump-rule-rewrites
-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}

{-# OPTIONS_GHC -fsimpl-tick-factor=300 #-} -- default 100

{-# OPTIONS_GHC -dverbose-core2core #-}

-- When I list the plugin in the test suite's .cabal target instead of here, I get
--
--   <command line>: Could not find module ‘ConCat.Plugin’
--   It is a member of the hidden package ‘concat-0.0.0’.
--   Perhaps you need to add ‘concat’ to the build-depends in your .cabal file.

module OptRules (tests) where

import Prelude hiding (Float,Double,id,(.),const,curry,uncurry)

import Data.Tuple (swap)
import Distribution.TestSuite

import ConCat.Misc (Unop,Binop,(:*))
import ConCat.AltCat
import ConCat.Float
import ConCat.Syntactic (Syn,render)

-- For FP & parallelism talk
tests :: IO [Test]
tests = return
  [ nopTest
  , tst (fst :: Int :* Bool -> Int)
  -- , tst (apply . (curry (exl . exr) &&& id) :: Int :* Bool -> Int)  -- fst
  ]

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

#if 1
-- Syntactic interpretation
test :: String -> (a -> b) -> Test
tst :: (a -> b) -> Test
{-# RULES "test syntactic" forall s f.
  test s f = mkTest s (putStrLn ('\n':render (ccc f))) #-}
#elif 1
-- (->), then syntactic
test :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "test (->) then Syn" forall s f.
   test s f = mkTest s (putStrLn ('\n':render (ccc (ccc f))))
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
