{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, TypeFamilies, ExistentialQuantification, FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving, ViewPatterns #-}
{-# LANGUAGE DefaultSignatures, MultiParamTypeClasses #-}

-- Okay
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  Run
-- Copyright   :  (c) 2016 Conal Elliott
-- 
-- Maintainer  :  conal@tabula.com
-- Stability   :  experimental
-- 
-- Run a test: reify, CCC, circuit
----------------------------------------------------------------------

module ConCat.RunCircuit
  ( Okay, go,go',goSep,run,runSep,ranksep -- ,goM,goM',goMSep
  , (:>)) where

-- TODO: clean up interfaces.

import Prelude

import Control.Monad (when)

import ConCat.AltCat (toCcc,Uncurriable(..),Ok,Ok2) -- unitArrow
import ConCat.Circuit (Attr,mkGraph,writeDot,displayDot,(:>),GenBuses)

-- import ConCat.Netlist (saveAsVerilog)
-- import ConCat.Mealy (Mealy(..,asFun)

ranksep :: Double -> Attr
ranksep n = ("ranksep",show n)

-- type Okay = Uncurriable (:>) ()

-- type Okay = Yes2
-- type Okay a b = GenBuses a
type Okay a b = (Uncurriable (:>) a b, GenBuses (UncDom a b), Ok (:>) (UncRan a b))

go :: Okay a b => String -> (a -> b) -> IO ()
-- go name = go' name []
go _ _ = error "go: not implemented"
{-# NOINLINE go #-}

go' :: Okay a b => String -> [Attr] -> (a -> b) -> IO ()
-- go' name attrs f = run name attrs (toCcc (uncurries (unitArrow f)))
go' _ _ _ = error "go': not implemented"
{-# NOINLINE go' #-}

goSep :: Okay a b => String -> Double -> (a -> b) -> IO ()
-- goSep name s = go' name [ranksep s]
goSep _ _ _ = error "goSep: not implemented"
{-# NOINLINE goSep #-}

-- Use rules instead of INLINE so that GHC will "inline" these definitions
-- before inlining begins. Otherwise, we'd lose our "primitives" before they can
-- be reified.

-- It's crucial that these error definitions are not CAFs. Otherwise, case
-- alternatives disappear. See inquiry and explanation:
-- <http://haskell.1045720.n5.nabble.com/Disappearing-case-alternative-td5832042.html>

{-# RULES

"go'"   forall name attrs f . go' name attrs f = run name attrs (uncurries (toCcc f))
"go"    forall name         . go name          = go' name []
"goSep" forall name s       . goSep name s     = go' name [ranksep s]

 #-}

-- genVerilog :: Bool
-- genVerilog = False -- True

genPdf :: Bool
genPdf = True -- False

-- showPretty :: Bool
-- showPretty = False -- True

showGraph :: Bool
showGraph = False -- True

-- Run an example: reify, CCC, circuit.
run :: (GenBuses a, Ok (:>) b) => String -> [Attr] -> (a :> b) -> IO ()
run name attrs circ = do -- when showPretty $ putStrLn (name ++ " = " ++ show e)
                         outGV name attrs circ
{-# NOINLINE run #-}

runSep :: (Ok2 (:>) a b) => String -> Double -> (a :> b) -> IO ()
runSep name s = run name [ranksep s]

-- Diagram and Verilog
outGV :: Ok2 (:>) a b => String -> [Attr] -> (a :> b) -> IO ()
outGV name attrs circ =
  do when showGraph $ putStrLn $ "outGV: Graph \n" ++ show g
     writeDot name attrs g
     -- Cap the size so that LaTeX doesn't choke and PDF viewers allow more
     -- zooming out.
     when genPdf $ displayDot ("pdf","-Gsize=10,10") name
     -- displayDot ("svg","") 
     -- displayDot ("png","-Gdpi=200")
     -- when genVerilog $ saveAsVerilog g
 where
   g = mkGraph circ
{-# NOINLINE outGV #-}

-- TODO: Move file-saving code from outD and saveVerilog to here.

#if 0

{--------------------------------------------------------------------
    State machines
--------------------------------------------------------------------}

goM :: Okay (a -> b) => String -> Mealy a b -> IO ()
goM name = goM' name []
{-# INLINE goM #-}

goMSep :: Okay (a -> b) => String -> Double -> Mealy a b -> IO ()
goMSep name s = goM' name [ranksep s]
{-# INLINE goMSep #-}

goM' :: Okay (a -> b) => String -> [Attr] -> Mealy a b -> IO ()
{-# INLINE goM' #-}

goM' name attrs = go' name attrs . asFun

#endif
