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
  ) where

-- TODO: clean up interfaces.

import Prelude

import Control.Monad (when)

-- import ReificationRules.Exp (E)
-- import ReificationRules.Prim (Prim)
-- import ReificationRules.HOS (reify)
-- import ReificationRules.ToCCC (toCCC)

import ConCat.Misc ((:+),(:*),ccc)
import ConCat.Category (Ok,unitArrow)
import ConCat.Circuit (Attr,mkGraph,UU,writeDot,displayDot,unitize,(:>),GenBuses)

-- import ConCat.Netlist (saveAsVerilog)
-- import ConCat.Mealy (Mealy(..,asFun)

ranksep :: Double -> Attr
ranksep n = ("ranksep",show n)

-- type Okay = Uncurriable (:>) ()

type Okay a = (Ok (:>) a, Uncurriable () a, GenBuses (UncDom () a))

go :: Okay a => String -> a -> IO ()
-- go name = go' name []
go _ _ = error "go: not implemented"
{-# NOINLINE go #-}

go' :: Okay a => String -> [Attr] -> a -> IO ()
-- go' name attrs f = run name attrs (ccc (uncurries (unitArrow f)))
go' _ _ _ = error "go': not implemented"
{-# NOINLINE go' #-}

goSep :: Okay a => String -> Double -> a -> IO ()
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

"go'"   forall name attrs f . go' name attrs f = run name attrs (ccc (uncurries (unitArrow f)))
"go"    forall name         . go name          = go' name []
"goSep" forall name s       . goSep name s     = go' name [ranksep s]

 #-}

-- genVerilog :: Bool
-- genVerilog = False -- True

genPdf :: Bool
genPdf = True

-- showPretty :: Bool
-- showPretty = False -- True

showGraph :: Bool
showGraph = False -- True

-- Run an example: reify, CCC, circuit.
run :: GenBuses a => String -> [Attr] -> (a :> b) -> IO ()
run name attrs circ = do -- when showPretty $ putStrLn (name ++ " = " ++ show e)
                         outGV name attrs (unitize circ)
{-# NOINLINE run #-}

runSep :: GenBuses a => String -> Double -> (a :> b) -> IO ()
runSep name s = run name [ranksep s]

-- Diagram and Verilog
outGV :: String -> [Attr] -> UU -> IO ()
outGV name attrs circ =
  do when showGraph $ putStrLn $ "outGV: Graph \n" ++ show g
     writeDot attrs g
     -- Cap the size so that LaTeX doesn't choke and PDF viewers allow more
     -- zooming out.
     when genPdf $ displayDot ("pdf","-Gsize=10,10") name'
     -- displayDot ("svg","") 
     -- displayDot ("png","-Gdpi=200")
     -- when genVerilog $ saveAsVerilog g
 where
   g@(name',_,_) = mkGraph name circ
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

{--------------------------------------------------------------------
    Uncurrying --- maybe move elsewhere
--------------------------------------------------------------------}

-- Note: I'm not using yet. I think it needs to go before ccc.
-- Alternatively, generalize from (->) to ClosedCat.

-- | Repeatedly uncurried version of a -> b
class Uncurriable a b where
  type UncDom a b
  type UncRan a b
  type UncDom a b = a
  type UncRan a b = b
  uncurries :: (a -> b) -> (UncDom a b -> UncRan a b)
  default uncurries :: (a -> b) -> (a -> b)
  uncurries = id

instance Uncurriable (a :* b) c => Uncurriable a (b -> c) where
  type UncDom a (b -> c) = UncDom (a :* b) c
  type UncRan a (b -> c) = UncRan (a :* b) c
  uncurries = uncurries . uncurry

instance Uncurriable a ()
instance Uncurriable a Bool
instance Uncurriable a Int
instance Uncurriable a Float
instance Uncurriable a Double
instance Uncurriable a (c :* d)
instance Uncurriable a (c :+ d)
