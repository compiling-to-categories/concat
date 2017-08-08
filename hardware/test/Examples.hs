{-# LANGUAGE FlexibleContexts #-}
-- To run:
--
--   stack build :hardware-examples
--
--   stack build :hardware-trace >& ~/Haskell/concat/hardware/out/o1
--
-- You might also want to use stack's --file-watch flag for automatic recompilation.

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE TypeApplications    #-}

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
import GHC.Float (int2Double)   -- TEMP

import ConCat.Misc ((:*),R,sqr,magSqr,Unop,Binop,inNew,inNew2)
import ConCat.Circuit (GenBuses,(:>))
import qualified ConCat.RunCircuit as RC
import ConCat.Syntactic (Syn,render)
import ConCat.AltCat (Ok2,ccc,(:**:)(..))
import qualified ConCat.AltCat as A

import ConCat.Rebox () -- necessary for reboxing rules to fire

import ConCat.Hardware.Verilog

main :: IO ()
main = sequence_
  [ putChar '\n' -- return ()
  , runVerilog' "top" $ \ (x :: Int, y :: Int) -> x + y
  ]

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

runVerilog' :: (GenBuses a, GenBuses b) => String -> (a -> b) -> IO ()
runVerilog' _ _ = error "runVerilog' called directly"
{-# NOINLINE runVerilog' #-}
{-# RULES "runVerilog'"
  forall n f. runVerilog' n f = runVerilog n $ ccc f #-}

