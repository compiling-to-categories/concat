-- To run:
--
--   stack build :hardware-examples
--
--   stack build :hardware-trace >& ~/Haskell/concat/hardware/out/o1
--
-- You might also want to use stack's --file-watch flag for automatic recompilation.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=250 #-}  -- default 100

-- {-# OPTIONS -fplugin-opt=ConCat.Plugin:trace #-}

{-# OPTIONS_GHC -fno-do-lambda-eta-expansion #-}

module Main where

import Control.Applicative (liftA2,liftA3)
import Data.Complex
import Data.List           (mapAccumL)
import GHC.Float (int2Double)   -- TEMP
import GHC.Generics hiding (S)
-- import ShapedTypes.FFT

import ConCat.Pair
import ConCat.FFT
import ConCat.Misc ((:*),R,sqr,magSqr,Unop,Binop,inNew,inNew2,(:+))
import ConCat.Circuit (GenBuses(..),(:>),Ty(..),Buses(..))
import qualified ConCat.RunCircuit as RC
import ConCat.Syntactic (Syn,render)
import ConCat.AltCat (Ok2,ccc,(:**:)(..))
import qualified ConCat.AltCat as A

import ConCat.Rebox () -- necessary for reboxing rules to fire

import ConCat.Hardware.Verilog
import ConCat.Rep
import ConCat.Nat
import ConCat.Shaped

main :: IO ()
main = sequence_
  [ putChar '\n' -- return ()
    -- Unary
  , runVerilog' "neg" $ \ (x :: Int) -> - x  -- Yields bit inversion, not 2's complement!
  , runVerilog' "odd" $ \ (x :: Int) -> x `mod` 2

    -- Binary
  , runVerilog' "adder" $ \ (x :: Int, y :: Int) -> x + y

    -- Conditional
  , runVerilog' "cond" $ \ (p :: Bool, x :: Int, y :: Int) -> if p then x else y

    -- FFT, via functor composition
  -- , runVerilog' "fft_fc_pair" $ \ ( pr :: (UPair (Complex Double)) ) -> fft pr
  , runVerilog' "fft_fc_pair" $ \ ( (x0::(Complex Double)) :# x1 ) -> fft (x0 :# x1)
  -- , runVerilog' "fft_fc_quad" $ \ ( fc :: ( (Pair :.: Pair) (Complex Float) )) -> fft fc
  -- TODO: Understand why only the second alternative, below, works.
  --       (The other two cause a compilation time-out error.)
  -- , runVerilog' "fft_fc_octet" $ \ ( fc :: ( ((Pair :.: Pair) :.: (Pair :.: Pair)) (Complex Float) )) -> fft fc
  , runVerilog' "fft_fc_rb3" $ fft @(RBin N3) @Float
  -- , runVerilog' "fft_fc_rb3" $ fft @((Pair :.: Pair) :.: (Pair :.: Pair)) @Float
  -- , runCirc "fft-rb3" $ ccc $ fft @(RBin N3) @Double
  ]

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

runVerilog' :: (GenBuses a, GenBuses b) => String -> (a -> b) -> IO ()
runVerilog' _ _ = error "runVerilog' called directly"
{-# NOINLINE runVerilog' #-}
{-# RULES "runVerilog'"
  forall n f. runVerilog' n f = runVerilog n $ toCcc' f #-}

