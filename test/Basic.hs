-- -*- flycheck-disabled-checkers: '(haskell-ghc haskell-stack-ghc); -*-

-- stack test (or stack build :basic)

-- stack build && stack test >& ~/Haskell/concat/out/o1

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE LambdaCase          #-}

-- -- TEMP for Pair
-- {-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-binds   #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

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
-- {-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -funfolding-keeness-factor=5 #-} -- Try. Defaults to 1.5
{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
-- {-# OPTIONS_GHC -dverbose-core2core #-}

-- {-# OPTIONS_GHC -dsuppress-all #-}
-- {-# OPTIONS_GHC -dsuppress-type-applications #-}
-- {-# OPTIONS_GHC -dsuppress-coercions #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}

-- {-# OPTIONS_GHC -dshow-passes #-}

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}

-- Tweak simpl-tick-factor from default of 100
{-# OPTIONS_GHC -fsimpl-tick-factor=500 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=5  #-}

-- https://ghc.haskell.org/trac/ghc/wiki/RewriteRules
-- {-# OPTIONS -fno-method-sharing #-}  -- obsolete
-- {-# OPTIONS -fdicts-cheap #-}  -- no visible change

-- When I list the plugin in the test suite's .cabal target instead of here, I get
--
--   <command line>: Could not find module ‘ConCat.Plugin’
--   It is a member of the hidden package ‘concat-0.0.0’.
--   Perhaps you need to add ‘concat’ to the build-depends in your .cabal file.

module Basic {-(tests)-} where

import Prelude hiding (Float,Double)   -- ,id,(.),const

import Control.Arrow (second)
import Data.Tuple (swap)
import Data.Maybe
import Distribution.TestSuite
import GHC.Generics hiding (R,D)
import GHC.Exts (lazy,coerce)

import ConCat.Misc (Unop,Binop,(:*),PseudoFun(..),R,bottom)
import ConCat.Rep
import ConCat.Float
import ConCat.Free.VectorSpace (V)
import ConCat.Free.LinearRow
import ConCat.Incremental
import ConCat.GAD  -- AD
import qualified ConCat.ADFun as ADFun
import ConCat.Syntactic (Syn,render)
import ConCat.Circuit (GenBuses)
import qualified ConCat.RunCircuit as RC
import ConCat.RunCircuit (go,Okay,(:>))
import ConCat.AltCat (ccc,reveal,Uncurriable(..),U2(..),(:**:)(..),Ok2,reprC,abstC,mulC)
import qualified ConCat.AltCat as A
import ConCat.Rebox () -- experiment
import ConCat.Orphans ()

-- import GHC.Num () -- help the plugin find instances (doesn't)

-- import ShapedTypes.Fams

-- -- Experiment: try to force loading of Num Float etc
-- class Num a => Quuz a
-- instance Quuz Float
-- instance Quuz Double

tests :: IO [Test]
tests = return
  [ nopTest

--   , test "negate-ai" (andInc (negate :: Unop Int))

--   , test "xy" (\ (x,y) -> x * y :: R)

--   , test "xy-i" (inc (\ (x,y) -> x * y :: R))

--   , test "xy-ai" (andInc (\ (x,y) -> x * y :: R))

--   , test "cond" (\ x -> if x > 0 then x else negate x :: Int)

--   , test "cond-fun" (\ x -> (if x > 0 then id else negate) x :: Int)

--   , test "sop1" (\ (x,y,z) -> x * y + y * z + x * z :: R)
--   , test "sop1-ai" (andInc (\ (x,y,z) -> x * y + y * z + x * z :: R))

  , test "sum4" (\ (a,b,c,d) -> (a+b)+(c+d) :: R)
--   , test "sum4-ai" (andInc (\ (a,b,c,d) -> (a+b)+(c+d) :: Int))

--   , test "sum8" (\ ((a,b,c,d),(e,f,g,h)) -> ((a+b)+(c+d))+((e+f)+(g+h)) :: R)
--   , test "sum8-ai" (andInc (\ ((a,b,c,d),(e,f,g,h)) -> ((a+b)+(c+d))+((e+f)+(g+h)) :: R))

--   , test "magSqr"            (magSqr @R)
--   , test "magSqr-ai" (andInc (magSqr @R))
--   , test "magSqr-i"     (inc (magSqr @R))

--   , test "magSqr-ad1" (andDer (magSqr @R))

--   , test "magSqr-ad1-inc" (inc (andDer (magSqr @R)))

--   , test "p1-ai" (andInc (\ ((x,y) :: R2) -> (x + 1, y)))
--   , test "p2-ai" (andInc (second succ :: Unop R2))
--   , test "p3-ai" (andInc (\ ((x,y) :: R2) -> (x + 1, x * y)))
--   , test "p3-i" (inc (\ ((x,y) :: R2) -> (x + 1, x * y)))

--   , test "sop1-ai" (andInc (\ ((x,y),z) -> x * y + y * z + x * z :: R))

  -- , tst (deriv @R (sin :: Unop R)) -- okay
  -- , tst (snd . unD (scalarX sin cos :: D R R R)) -- okay

  -- , tst (coerce :: Bool -> Bool) -- okay
  -- , tst (coerce :: Bool -> Bolo) -- hole
  -- , tst (coerce :: Bool -> Par1 Bool) -- hole
  -- , tst (coerce :: Par1 Bool -> Bool) -- hole

  -- , tst (coerce :: R -> L R R R) -- hole
  -- , tst (A.coerceC :: R -> L R R R) -- hole
  -- , tst (scale :: R -> L R R R) -- hole

  -- , tst (andDeriv @R (scale :: R -> L R R R)) -- hole
  -- , tst (andDeriv @R (scale :: R -> L R R R)) -- hole
  -- , tst (deriv @R (scale :: R -> L R R R)) -- hole
  -- , tst (deriv @R (\ x -> scale x :: L R R R)) -- hole
  -- , tst (deriv @R (\ x -> scale (cos x) :: L R R R)) -- hole

  -- , tst (deriv @R (deriv @R (sin :: Unop R)))  -- hole

--   , tst ((,) @ (Par1 Float) @ (Par1 Float) (Par1 1.0))

--   , tst ((,) @Bool @Bool)

--   , tst (\ (a :: Bool) -> (a,a,a))

--   , tst ((,,) @Bool @Bool @Bool)

--   , tst ((:*:) :: Par1 Bool -> Par1 Bool -> (Par1 :*: Par1) Bool)

--   , tst (scale :: R -> L R R R)

--   , tst (\ x _y -> negate x :: Int)

--   , tst (\ x -> 3 * x + x :: Int)

--   , tst (\ (x,y) -> 3 * x + y + 7 :: Float)

--   , tst (negate :: Unop Int)

--   , tst (uncurry ((*) :: Binop Float))

--   , tst (uncurry (\ x y -> x + y :: Int))

--   , tst ((\ _ -> 0) :: Unop Int)

--   , tst (\ x -> x + 3 :: Int)

--   , tst (\ x -> x + 3 :: Float)

--   , tst (\ x -> x / 3 :: Float)  -- divideFloat# problem. See todo.md

--   , tst (\ () -> (3,4) :: Double :* Float)

--   , tst (\ (x,y) -> 3 * x + y + 7 :: Float)

--   , test "linear-compose-r-r-r" (uncurry ((A..) :: LComp R R R))
--   , test "linear-compose-r2-r-r" (uncurry ((A..) :: LComp R2 R R))
--   , test "linear-compose-r-r2-r" (uncurry ((A..) :: LComp R R2 R))
--   , test "linear-compose-r2-r2-r2" (uncurry ((A..) :: LComp R2 R2 R2))

--   , tst (Par1 @ Bool)
--   , tst (Par1 . Par1 @ Bool)
--   , tst (\ (x :: Bool) -> Par1 (Par1 x))
--   , tst (\ () -> Par1 True)

--   , tst (\ (Par1 b) -> b :: Bool)
--   , tst (\ (Par1 (Par1 b)) -> b :: Bool)

--   , tst ((\ (L w) -> w) :: LR R R -> (V R R :-* V R R) R)
--   , tst ((\ (L (Par1 (Par1 s))) -> s) :: LR R R -> R)

--   , tst (scale :: R -> L R R R)

--   , test "id-r"          (id :: Unop R)
--   , test "id-r2"         (id :: Unop R2)
--   , test "id-r3"         (id :: Unop R3)
--   , test "id-r4"         (id :: Unop R4)

--   , test "const-r-4"     (const 4 :: Unop R)
--   , test "const-r-34"    (const (3,4) :: R -> R2)
--   , test "const-r2-34"   (const (3,4) :: Unop R2)

--   , test "x-plus-four" (\ x -> x + 4 :: R)
--   , test "four-plus-x" (\ x -> 4 + x :: R)

--   , test "sin"         (sin @R)
--   , test "cos"         (cos @R)
--   , test "double"      (\ x -> x + x :: R) 

--   , test "sin-d1" (der (sin @R))
--   , test "sin-d2" (der (der (sin @R)))
--   , test "sin-d3" (der (der (der (sin @R))))
--   , test "sin-d4" (der (der (der (der (sin @R)))))

--   , tst (\ (p :: R2) -> (snd p, fst p))
--   , tst (\ ((x,y) :: R2) -> (y,x))
--   , tst (\ ((x,y) :: R2) -> (Par1 y,Par1 x))
--   , tst (\ ((x,y) :: R2) -> Par1 y :*: Par1 x) -- simple

--   , tst (\ (p :: Par1 R, q :: Par1 R) -> p :*: q)  -- complex

--   , tst (abstC :: Par1 R :* Par1 R -> (Par1 :*: Par1) R)

--   , test "mult"                     (uncurry ((*) @R))
--   , test "mult-d1"             (der (uncurry ((*) @R)))
--   , test "mult-d2"        (der (der (uncurry ((*) @R))))
--   , test "mult-d3"   (der (der (der (uncurry ((*) @R)))))

--   , test "square"      (\ x -> x * x :: R)

--   , test "cos-2x"      (\ x -> cos (2 * x) :: R)
--   , test "cos-2xx"     (\ x -> cos (2 * x * x) :: R)
--   , test "cos-xpy"     (\ (x,y) -> cos (x + y) :: R)

--   , test "cos-xy" (\ (x,y) -> cos (x * y) :: R)
--   , test "cos-xy-d1" (der (\ (x,y) -> cos (x * y) :: R))
--   , test "cos-xy-d2" (der (der (\ (x,y) -> cos (x * y) :: R)))

--   , test "cosSin-xy" (\ (x,y) -> cosSin (x * y) :: R2)
--   , test "cosSin-xy-d1" (der (\ (x,y) -> cosSin (x * y) :: R2))

--   , test "cosSin-xy-ad1" (andDer (\ (x,y) -> cosSin (x * y) :: R2))

--   , test "cosSin-xy-ad1-i" (inc (andDer (\ (x,y) -> cosSin (x * y) :: R2)))


--   , test "cosSin-xyz" (\ (x,y,z) -> cosSin (x * y + x * z + y * z) :: R2)
--   , test "cosSin-xyz-d1" (der (\ (x,y,z) -> cosSin (x * y + x * z + y * z) :: R2))

--   , test "foo" (\ (a::R,_b::R,_c::R) -> a)

--   , test "foo" (\ (a::R) -> a * a + a) -- fine

--   , test "foo" (\ (a,b) -> b * a :: R) -- non-IsoB

--   , test "foo" (\ ((a::R,b::R),c::R) -> a * b) -- non-IsoB

--   , test "foo" (\ (a::R,b::R,c::R) -> a * b) -- non-IsoB

--   , test "foo" (\ (a::R,b::R,c::R) -> b * c) -- non-IsoB

--   , test "foo" (\ (a::R,b::R,c::R) -> a + b * c) -- non-IsoB

--   , test "foo" (\ (a,b,c) -> a * b * c :: R)

--   , test "foo" (\ (a,b,c,d) -> a * b + c * d :: R)

--   , test "foo" (\ ((a,b),(c,d)) -> a * b + c * d :: R)

--   , test "mul" ((*) :: Binop R)

--   , test "cos-xy" (\ (x,y) -> cos (x * y) :: R)

--   , test "three" three
--   , test "threep" three'
--   , test "addThree" addThree

--   , tst (fst @Bool @Int)

--   , tst (A.exl :: Int :* Bool -> Int)

--   , tst ((<=) :: Int -> Int -> Bool)

--   , tst not

--   , tst (\ (x :: Int) -> x + x)

--   , tst (flip (+) :: Binop Int)

--   , tst ((+) :: Binop Int)

--   , tst ((+) 3 :: Unop Int)

--   , tst ((+) 3 :: Unop R)

--   , tst (||)

--   , tst ((||) True)

--   , tst (const True :: Unop Bool)

--   , tst ((||) False)

--   , tst (negate :: Unop Int)

--   , tst (negate  :: Unop R)
--   , tst (negateC :: Unop R)

--   , tst (\ (_ :: ()) -> 1 :: Double)

--   , tst (\ (x,y) -> x + y :: Int)

--   , tst (uncurry ((+) :: Binop Int))

--   , tst ((+) :: Binop Int)

--   , tst ((+) :: Binop R)

--   , tst (recip :: Unop R)

--   , tst ((==) :: Int -> Int -> Bool)
--   , tst ((==) :: R -> R -> Bool)
--   , tst ((==) :: Double -> Double -> Bool)
--   , tst ((/=) :: Int -> Int -> Bool)
--   , tst ((/=) :: R -> R -> Bool)
--   , tst ((/=) :: Double -> Double -> Bool)

--   , tst ((<) :: Int -> Int -> Bool)
--   , tst ((<) :: R -> R -> Bool)
--   , tst ((<) :: Double -> Double -> Bool)
--   , tst ((<=) :: Int -> Int -> Bool)
--   , tst ((<=) :: R -> R -> Bool)
--   , tst ((<=) :: Double -> Double -> Bool)
--   , tst ((>) :: Int -> Int -> Bool)
--   , tst ((>) :: R -> R -> Bool)
--   , tst ((>) :: Double -> Double -> Bool)
--   , tst ((>=) :: Int -> Int -> Bool)
--   , tst ((>=) :: R -> R -> Bool)
--   , tst ((>=) :: Double -> Double -> Bool)

--   , tst ((+) :: Binop Int)
--   , tst ((+) :: Binop R)
--   , tst ((+) :: Binop Double)
--   , tst ((-) :: Binop Int)
--   , tst ((-) :: Binop R)
--   , tst ((-) :: Binop Double)
  
--   , tst (recip :: Unop R)
--   , tst (recip :: Unop Double)
--   , tst ((/) :: Binop R)
--   , tst ((/) :: Binop Double)

--   , tst (exp :: Unop R)
--   , tst (exp :: Unop Double)
--   , tst (cos :: Unop R)
--   , tst (cos :: Unop Double)
--   , tst (sin :: Unop R)
--   , tst (sin :: Unop Double)

--   , tst (\ (_ :: ()) -> 1 :: Int)

--   , test "fmap Pair" (fmap not :: Unop (Pair Bool))

--   , test "negate" (\ x -> negate x :: Int)
--   , test "succ" (\ x -> succ x :: Int)
--   , test "pred" (pred :: Unop Int)

--   , tst (id :: Unop R)

--   , tst ((\ x -> x) :: Unop R)

--   , tst  ((\ _ -> 4) :: Unop R)

--   , tst (fst :: Bool :* Int -> Bool)

--   , tst (\ (x :: Int) -> succ (succ x))

--   , tst ((.) :: Binop (Unop Bool))

--   , tst (succ . succ :: Unop Int)

--   , tst (\ (x :: Int) -> succ (succ x))

--   , tst ((\ (x,y) -> (y,x)) :: Unop (Bool :* Bool))
--   , tst ((,) :: Bool -> Int -> Bool :* Int)

--   , tst (double :: Unop R)

--   , test "q0"  (\ x -> x :: Int)
--   , test "q1"  (\ (_x :: Int) -> True)
--   , test "q2"  (\ (x :: Int) -> negate (x + 1))
--   , test "q3"  (\ (x :: Int) -> x > 0)
--   , test "q4"  (\ x -> x + 4 :: Int)
--   , test "q5"  (\ x -> x + x :: Int)
--   , test "q6"  (\ x -> 4 + x :: Int)

--   , test "q7"  (\ (a :: Int) (_b :: Int) -> a)
--   , test "q8"  (\ (_ :: Int) (b :: Int) -> b)
--   , test "q9"  (\ (a :: R) (b :: R) -> a + b)
--   , test "q10" (\ (a :: R) (b :: R) -> b + a)

--   , test "q7u"  ((\ (a,_) -> a) :: Int :* Int -> Int)
--   , test "q8u"  ((\ (_,b) -> b) :: Int :* Int -> Int)
--   , test "q9u"  ((\ (a,b) -> a + b) :: R :* R -> R)
--   , test "q10u" ((\ (a,b) -> b + a) :: R :* R -> R)

--   , tst (\ (_x :: Int) -> not)
--   , tst (\ (_ :: Bool) -> negate :: Unop Int)
--   , tst (\ f -> f True :: Bool)

  ]

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

type EC = Syn :**: (:>)

runU2 :: U2 a b -> IO ()
runU2 = print

type GO a b = (GenBuses a, Ok2 (:>) a b)

runF :: (a -> b) -> IO ()
runF f = f `seq` return ()

runSyn :: Syn a b -> IO ()
runSyn syn = putStrLn ('\n' : render syn)

runEC :: GO a b => String -> EC a b -> IO ()
runEC nm (syn :**: circ) = runSyn syn >> RC.run nm [] circ

runCirc :: GO a b => String -> (a :> b) -> IO ()
runCirc nm circ = RC.run nm [] circ

runCirc' :: GO a b => String -> (U2 :**: (:>)) a b -> IO ()
runCirc' nm (triv :**: circ) = runU2 triv >> RC.run nm [] circ

-- When I use U2, I get an run-time error: "Impossible case alternative".

#if 0
-- (->) interpretation
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "ccc (->)" forall nm f. test nm f = mkTest nm (runF (ccc f)) #-}
#elif 0
-- U2 interpretation
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "trivial" forall nm f. test nm f = mkTest nm (runU2 (ccc f)) #-}
#elif 0
-- Syntactic interpretation
test, test' :: String -> (a -> b) -> Test
tst :: (a -> b) -> Test
{-# RULES "syntactic" forall nm f.
  test nm f = mkTest nm (runSyn (ccc f)) #-}
#elif 0
-- Circuit interpretation
test, test' :: GO a b => String -> (a -> b) -> Test
tst  :: GO a b => (a -> b) -> Test
{-# RULES "circuit" forall nm f. test nm f = mkTest nm (runCirc nm (ccc f)) #-}
#elif 0
-- (->), syntactic
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "(->); Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (ccc f)))
 #-}
#elif 0
-- Syntactic, uncurries
test, test' :: Uncurriable Syn a b => String -> (a -> b) -> Test
tst :: Uncurriable Syn a b => (a -> b) -> Test
{-# RULES "syntactic; uncurries" forall nm f.
  test nm f = mkTest nm (runSyn (uncurries (ccc f))) #-}
#elif 0
-- uncurries, syntactic
test, test' :: Uncurriable (->) a b => String -> (a -> b) -> Test
tst  :: Uncurriable (->) a b => (a -> b) -> Test
{-# RULES "uncurries; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (uncurries f)))
 #-}
#elif 0
-- (->), uncurries, syntactic
-- Some trouble with INLINE [3]
test, test' :: Uncurriable (->) a b => String -> (a -> b) -> Test
tst  :: Uncurriable (->) a b => (a -> b) -> Test
{-# RULES "(->); uncurries; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (uncurries (ccc f))))
 #-}
#elif 1
-- syntactic *and* circuit
test, test' :: GO a b => String -> (a -> b) -> Test
tst  :: GO a b => (a -> b) -> Test
{-# RULES "Syn :**: (:>)" forall nm f.
   test nm f = mkTest nm (runEC nm (ccc f))
 #-}
#elif 0
-- (->), syntactic *and* circuit
test, test' :: GO a b => String -> (a -> b) -> Test
tst  :: GO a b => (a -> b) -> Test
{-# RULES "(->); Syn :**: (:>)" forall nm f.
   test nm f = mkTest nm (runEC nm (ccc (ccc f)))
 #-}
#elif 0
-- syntactic *and* circuit, uncurries
-- OOPS: Core Lint error
test, test' :: (GenBuses (UncDom a b), Uncurriable (Syn :**: (:>)) a b) => String -> (a -> b) -> Test
tst  :: (GenBuses (UncDom a b), Uncurriable (Syn :**: (:>)) a b) => (a -> b) -> Test
{-# RULES "uncurries ; Syn :**: (:>)" forall nm f.
   test nm f = mkTest nm (runEC nm (uncurries (ccc f)))
 #-}
#elif 0
-- uncurries, syntactic *and* circuit
-- OOPS: Core Lint error
test, test' :: (GenBuses (UncDom a b), Uncurriable (->) a b) => String -> (a -> b) -> Test
tst  :: (GenBuses (UncDom a b), Uncurriable (->) a b) => (a -> b) -> Test
{-# RULES "uncurries ; Syn :**: (:>)" forall nm f.
   test nm f = mkTest nm (runEC nm (ccc (uncurries f)))
 #-}
#elif 0
-- (->), circuit
-- OOPS: "Simplifier ticks exhausted"
test, test' :: Okay a b => String -> (a -> b) -> Test
tst  :: Okay a b => (a -> b) -> Test
{-# RULES "(->); (:>)" forall nm f.
   test nm f = mkTest nm (go nm (ccc f))
 #-}
#elif 0
-- L, syntactic
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "L ; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (\ () -> lmap @R f)))
 #-}
#elif 0
-- (->), L, Syn
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "(->) ; L ; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (\ () -> lmap @R (ccc f))))
 #-}
#elif 0
type Q a b = (V R a :-* V R b) R
type GB a b = (GenBuses (UncDom () (Q a b)), Uncurriable (:>) () (Q a b))
-- L, syntax+circuit
test, test' :: GB a b => String -> (a -> b) -> Test
tst         :: GB a b =>           (a -> b) -> Test
{-# RULES "L ; Syn+circuit" forall nm f.
   test nm f = mkTest nm (runEC (nm++"-lmap") (ccc (\ () -> repr (lmap @R f))))
 #-}
#elif 0
-- Val+deriv, syntactic
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "test AD" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (andDer f)))
 #-}
#elif 0
-- (->), val+deriv, syntactic. The first (->) gives us a chance to
-- transform away the ClosedCat operations.
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "(->); D; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (andDer (ccc f))))
 #-}
#elif 0
-- (->), val+deriv via ADFun, syntactic
test, test' :: (Ok2 (L R) a b, HasL (V R a)) => String -> (a -> b) -> Test
tst         :: (Ok2 (L R) a b, HasL (V R a)) =>           (a -> b) -> Test
{-# RULES "(->); D'; EC" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (ADFun.andDer (ccc f))))
 #-}
#elif 0
-- (->), val+deriv, circuit.
test, test' :: GO a b => String -> (a -> b) -> Test
tst         :: GO a b =>           (a -> b) -> Test
{-# RULES "(->); D; (:>)" forall nm f.
   test nm f = mkTest nm (runCirc (nm++"-ad") (ccc (andDer (ccc f))))
 #-}
#elif 0
-- (->), val+deriv, syntactic+circuit.
test, test' :: GO a b => String -> (a -> b) -> Test
tst         :: GO a b =>           (a -> b) -> Test
{-# RULES "(->); D; EC" forall nm f.
   test nm f = mkTest nm (runEC (nm++"-ad") (ccc (andDer (ccc f))))
 #-}
#elif 0
-- (->), deriv, syntactic+circuit.
test, test' :: GO a b => String -> (a -> b) -> Test
tst         :: GO a b =>           (a -> b) -> Test
{-# RULES "(->); D; EC" forall nm f.
   test nm f = mkTest nm (runEC (nm++"-d") (ccc (der (ccc f))))
 #-}
#elif 1
-- (->), second deriv, syntactic+circuit.
test, test' :: GO a b => String -> (a -> b) -> Test
tst         :: GO a b =>           (a -> b) -> Test
{-# RULES "(->); D; EC" forall nm f.
   test nm f = mkTest nm (runEC (nm++"-d2") (ccc (der (der (ccc f)))))
 #-}
#elif 0
-- (->), val+deriv via ADFun, syntactic+circuit.
test, test' :: (Ok2 (L R) a b, HasL (V R a), GO a b) => String -> (a -> b) -> Test
tst         :: (Ok2 (L R) a b, HasL (V R a), GO a b) =>           (a -> b) -> Test
{-# RULES "(->); D'; EC" forall nm f.
   test nm f = mkTest nm (runEC (nm++"-adf") (ccc (ADFun.andDer (ccc f))))
 #-}
#elif 0
-- (->), deriv via ADFun, syntactic+circuit.
test, test' :: (Ok2 (L R) a b, HasL (V R a), GO a b) => String -> (a -> b) -> Test
tst         :: (Ok2 (L R) a b, HasL (V R a), GO a b) =>           (a -> b) -> Test
{-# RULES "(->); D; EC" forall nm f.
   test nm f = mkTest nm (runEC (nm++"-derf") (ccc (ADFun.der (ccc f))))
 #-}
#else
-- NOTHING
#endif

test' nm _f = mkTest nm (putStrLn ("test called on " ++ nm))

test nm = test' nm
tst    = test' "tst"
{-# NOINLINE test #-}
-- {-# ANN test PseudoFun #-}
{-# NOINLINE tst #-}
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

{--------------------------------------------------------------------
    Ad hoc tests
--------------------------------------------------------------------}

#if 0

foo1 :: D R R
foo1 = ccc id

foo2, foo3 :: R -> R :* (R -> R)
foo2 = unD foo1
foo3 = unD (ccc id)

sampleD :: D a b -> a -> b
sampleD (D f) = fst . f

foo4 :: R -> R
foo4 = sampleD (ccc id)

#endif

double :: Num a => a -> a
double a = a + a
{-# INLINE double #-}

cosSin :: Floating a => a -> a :* a
cosSin a = (cos a, sin a)
{-# INLINE cosSin #-}

type R2 = R :* R

type R3 = (R,R,R)

type R4 = (R2,R2)

type LComp a b c = LR b c -> LR a b -> LR a c

sqr :: Num a => a -> a
sqr a = a * a

magSqr :: Num a => a :* a -> a
magSqr (a,b) = sqr a + sqr b

{--------------------------------------------------------------------
    More examples
--------------------------------------------------------------------}

three :: R -> R3
three x = (x, x*x, x*x*x)

three' :: R -> (R3,R3)
three' x = (f 5, f 6)
 where
   f y = (x, x*x, x*y*x)

addThree :: R3 -> R
addThree (a,b,c) = a+b+c

par1 :: a -> Par1 a
par1 = Par1
{-# INLINE [0] par1 #-}

newtype Bolo = Bolo Bool



{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

-- bar :: Par1 R :* Par1 R -> (Par1 :*: Par1) R
-- bar = abstC

-- dbar :: Par1 R :* Par1 R -> L R (Par1 R :* Par1 R) ((Par1 :*: Par1) R)
-- dbar = deriv abstC

-- bar :: R -> (R -+> R)
-- bar = inc negate

-- bar :: R2 -> (Del R2 -> Del R)
-- bar = inc mulC

