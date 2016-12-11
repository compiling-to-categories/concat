-- -*- flycheck-disabled-checkers: '(haskell-ghc haskell-stack-ghc); -*-

-- stack build :basic

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds     #-}

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
{-# OPTIONS_GHC -dcore-lint #-}
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

{-# OPTIONS_GHC -ddump-rule-rewrites #-}

-- {-# OPTIONS_GHC -fsimpl-tick-factor=300 #-} -- default 100
-- {-# OPTIONS_GHC -fsimpl-tick-factor=5  #-} -- default 100

-- When I list the plugin in the test suite's .cabal target instead of here, I get
--
--   <command line>: Could not find module ‘ConCat.Plugin’
--   It is a member of the hidden package ‘concat-0.0.0’.
--   Perhaps you need to add ‘concat’ to the build-depends in your .cabal file.

module Basic {-(tests)-} where

import Prelude hiding (Float,Double)   -- ,id,(.),const

import Control.Arrow (second)
import Data.Tuple (swap)
import Distribution.TestSuite

import ConCat.Misc (Unop,Binop,(:*),PseudoFun(..))
import ConCat.Float
import ConCat.Syntactic (Syn,render)
import ConCat.Circuit (GenBuses)
import qualified ConCat.RunCircuit as RC
import ConCat.RunCircuit (go,Okay,(:>))
#if 1
import ConCat.AD
#else
import ConCat.ADFun
#endif
import ConCat.Free.VectorSpace (V)
import ConCat.Free.LinearRow
import ConCat.Rep (repr)

import ConCat.AltCat (ccc,reveal,Uncurriable(..),(:**:)(..))
import qualified ConCat.AltCat as A

-- -- Experiment: try to force loading of Num Float etc
-- class Num a => Quuz a
-- instance Quuz Float
-- instance Quuz Double

tests :: IO [Test]
tests = return
  [ nopTest

--   , test "id-r"          (id :: Unop R)

  , test "id-r2"          (id :: Unop R2)

--   , test "const-4"     (const 4 :: Unop R)
--   , test "four-plus-x" (\ x -> 4 + x :: R)
--   , test "cos"         (cos :: Unop R)
--   , test "square"      (\ x -> x * x :: R)
--   , test "cos-2x"      (\ x -> cos (2 * x) :: R)
--   , test "cos-xpx"      (\ x -> cos (x + x) :: R)
--   , test "cos-2xx"     (\ x -> cos (2 * x * x) :: R)

--   , test "cos-xpy"      (\ (x,y) -> cos (x + y) :: R)

--   , test "xy" (\ (x,y) -> x * y :: R)

--   , test "cos-x"         (\ x -> cos x :: R)

--   , test "cos-xy" (\ (x,y) -> cos (x * y) :: R)

--   , test "cosSin-xy" (\ (x,y) -> cosSin (x * y) :: R2)

--   , test "mul" ((*) :: Binop R)

--   , test "cos-xy" (\ (x,y) -> cos (x * y) :: R)

--   , test "addThree" addThree
--   , test "threep" three'
--   , test "three" three

--   , tst (fst @Bool @Int)

--   , tst (A.exl :: Int :* Bool -> Int)

--   , tst not

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

runSyn :: Syn a b -> IO ()
runSyn syn = putStrLn ('\n' : render syn)

runEC :: GenBuses a => String -> EC a b -> IO ()
runEC nm (syn :**: circ) = runSyn syn >> RC.run nm [] circ

#if 0
-- Circuit interpretation
test, test' :: Okay a b => String -> (a -> b) -> Test
tst  :: Okay a b => (a -> b) -> Test
{-# RULES "circuit" forall nm f. test nm f = mkTest nm (go nm f) #-}
#elif 0
-- Syntactic interpretation
test, test' :: String -> (a -> b) -> Test
tst :: (a -> b) -> Test
{-# RULES "syntactic" forall nm f.
  test nm f = mkTest nm (runSyn (ccc f)) #-}
#elif 0
-- (->), then syntactic
-- With INLINE [3]: "Simplifier ticks exhausted"
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "(->); Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (ccc f)))
 #-}
#elif 0
-- Syntactic, then uncurries
test, test' :: Uncurriable Syn a b => String -> (a -> b) -> Test
tst :: Uncurriable Syn a b => (a -> b) -> Test
{-# RULES "syntactic; uncurries" forall nm f.
  test nm f = mkTest nm (runSyn (uncurries (ccc f))) #-}
#elif 0
-- uncurries, then syntactic
test, test' :: Uncurriable (->) a b => String -> (a -> b) -> Test
tst  :: Uncurriable (->) a b => (a -> b) -> Test
{-# RULES "uncurries; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (uncurries f)))
 #-}
#elif 0
-- (->), then uncurries, then syntactic
-- Some trouble with INLINE [3]
test, test' :: Uncurriable (->) a b => String -> (a -> b) -> Test
tst  :: Uncurriable (->) a b => (a -> b) -> Test
{-# RULES "(->); uncurries; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (uncurries (ccc f))))
 #-}
#elif 0
-- syntactic *and* circuit
test, test' :: GenBuses a => String -> (a -> b) -> Test
tst  :: GenBuses a => (a -> b) -> Test
{-# RULES "Syn :**: (:>)" forall nm f.
   test nm f = mkTest nm (runEC nm (ccc f))
 #-}
#elif 0
-- syntactic *and* circuit, then uncurries
-- OOPS: Core Lint error
test, test' :: (GenBuses (UncDom a b), Uncurriable (Syn :**: (:>)) a b) => String -> (a -> b) -> Test
tst  :: (GenBuses (UncDom a b), Uncurriable (Syn :**: (:>)) a b) => (a -> b) -> Test
{-# RULES "uncurries ; Syn :**: (:>)" forall nm f.
   test nm f = mkTest nm (runEC nm (uncurries (ccc f)))
 #-}
#elif 0
-- uncurries, then syntactic *and* circuit
-- OOPS: Core Lint error
test, test' :: (GenBuses (UncDom a b), Uncurriable (->) a b) => String -> (a -> b) -> Test
tst  :: (GenBuses (UncDom a b), Uncurriable (->) a b) => (a -> b) -> Test
{-# RULES "uncurries ; Syn :**: (:>)" forall nm f.
   test nm f = mkTest nm (runEC nm (ccc (uncurries f)))
 #-}
#elif 0
-- (->), then circuit
-- OOPS: "Simplifier ticks exhausted"
test, test' :: Okay a b => String -> (a -> b) -> Test
tst  :: Okay a b => (a -> b) -> Test
{-# RULES "(->); (:>)" forall nm f.
   test nm f = mkTest nm (go nm (ccc f))
 #-}
#elif 0
-- L, then syntactic
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "L ; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (\ () -> lmap @R f)))
 #-}
#elif 1
type Q a b = (V R a :-* V R b) R
type GB a b = (GenBuses (UncDom () (Q a b)), Uncurriable (:>) () (Q a b))
-- L, then circuit
test, test' :: GB a b => String -> (a -> b) -> Test
tst         :: GB a b =>           (a -> b) -> Test
{-# RULES "L ; Syn" forall nm f.
   test nm f = mkTest nm (go nm (ccc (\ () -> repr (lmap @R f))))
 #-}
#elif 1
-- L, then syntactic and circuit
test, test' :: GenBuses a => String -> (a -> b) -> Test
tst         :: GenBuses a => (a -> b) -> Test
{-# RULES "L ; Syn" forall nm f.
   test nm f = mkTest nm (runEC nm (ccc (\ () -> lmap @R f)))
 #-}
#elif 0
-- Derivative, then syntactic
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "test AD" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (dfun f)))
 #-}
#elif 0
-- (->), then derivative, then syntactic. The first (->) gives us a chance to
-- transform away the ClosedCat operations.
test, test' :: String -> (a -> b) -> Test
tst  :: (a -> b) -> Test
{-# RULES "(->); D; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (dfun (ccc f))))
 #-}
#elif 0
-- (->), then derivative, then syntactic and circuit.
test, test' :: GenBuses a => String -> (a -> b) -> Test
tst         :: GenBuses a =>           (a -> b) -> Test
{-# RULES "(->); D; EC" forall nm f.
   test nm f = mkTest nm (runEC (nm++"-ad") (ccc (dfun @R (ccc f))))
 #-}
#elif 0
-- (->), then *scalar* derivative, then syntactic.
test, test' :: Num a => String -> (a -> b) -> Test
tst  :: Num a => (a -> b) -> Test
{-# RULES "(->); D; Syn" forall nm f.
   test nm f = mkTest nm (runSyn (ccc (dsc (dfun (ccc f)))))
 #-}
#elif 0
-- (->), scalar D, syntax+circuit.
test, test' :: (Num a, GenBuses a) => String -> (a -> b) -> Test
tst         :: (Num a, GenBuses a) =>           (a -> b) -> Test
{-# RULES "(->); D; Syn" forall nm f.
   test nm f = mkTest nm (runEC nm (ccc (dsc (dfun (ccc f)))))
 #-}
#elif 0
-- scalar D, syntax+circuit.
test, test' :: (Num a, GenBuses a) => String -> (a -> b) -> Test
tst         :: (Num a, GenBuses a) =>           (a -> b) -> Test
{-# RULES "(->); D; Syn" forall nm f.
   test nm f = mkTest nm (runEC nm (ccc (dsc (dfun f))))
 #-}
#elif 0
-- (->), non-scalar D, syntax+circuit.
test, test' :: GenBuses a => String -> (a -> b) -> Test
tst         :: GenBuses a =>           (a -> b) -> Test
{-# RULES "(->); D; Syn" forall nm f.
   test nm f = mkTest nm (runEC (nm++"-da2b2") (ccc (da2b2 (dfun (ccc f)))))
 #-}
#elif 0
-- (->), basis D, syntax+circuit.
test, test' :: (HasBasis a b, GenBuses a) => String -> (a -> b) -> Test
tst         :: (HasBasis a b, GenBuses a) =>           (a -> b) -> Test
{-# RULES "(->); D; Syn" forall nm f.
   test nm f = mkTest nm (runEC (nm++"-dbas") (ccc (dbas (dfun (ccc f)))))
 #-}
#elif 0
-- (->), uncurries, non-scalar D, syntax+circuit.
test, test' :: (GenBuses (UncDom a b), Uncurriable (->) a b)
            => String -> (a -> b) -> Test
tst         :: (GenBuses (UncDom a b), Uncurriable (->) a b)
            => GenBuses a =>           (a -> b) -> Test
{-# RULES "uncurries; (->); D; Syn" forall nm f.
   test nm f = mkTest nm (runEC nm (ccc (da2b2 (dfun (ccc (uncurries f))))))
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

#if 1

-- unD :: D a b -> a -> b :* (a -> b)
-- unD (D f) = f
-- {-# INLINE unD #-}

-- bar :: IO ()
-- bar = runSyn (ccc (unD' (ccc (id :: Bool -> Bool))))

-- -- Okay
-- foo1 :: R -> R :* (R -> R)
-- foo1 = unD' A.id

-- -- Okay
-- foo2 :: Syn R (R :* (R -> R))
-- foo2 = ccc (unD' A.id)

-- -- Okay (now with NOINLINE render)
-- foo3 :: String
-- foo3 = render (ccc (unD' (A.id :: D R R)))

-- -- Okay
-- foo4 :: Test
-- foo4 = mkTest "foo4" (runSyn (ccc (unD' (A.id :: D R R))))

-- -- Okay
-- bar1 :: D R R
-- bar1 = ccc (A.id :: R -> R)

-- -- residual with unD, but okay with unD'
-- bar2 :: R -> (R :* (R -> R))
-- bar2 = unD' (ccc (A.id :: R -> R))

-- bar :: D R R
-- bar = ccc id

-- bar :: D R R
-- bar = reveal (ccc id)

-- bar :: R -> (R :* (R -> R))
-- bar = unD' (reveal (ccc id))

-- bar :: R -> (R :* (R -> R))
-- bar = dfun (const 4)

-- bar :: R -> (R :* (R -> R))
-- bar = -- dfun ((\ _x -> 4))
--       dfun id

-- bar :: Syn R (R :* (R -> R))
-- bar = ccc (dfun id)

-- bar :: Syn R (R :* (R -> R))
-- bar = ccc (dfun id)

-- bar :: D R R
-- bar = ccc cos

-- bar :: D R R
-- bar = reveal (ccc cos)

-- bar :: D R R
-- bar = reveal (reveal (ccc cos))

-- bar :: R -> R :* (R -> R)
-- bar = dfun (ccc cos)

-- bar :: Syn R (R :* (R -> R))
-- bar = ccc (dfun (ccc cos))

-- bar :: R -> R :* (R -> R)
-- bar = unD' (ccc cos)

-- bar :: Syn R (R :* (R -> R))
-- bar = ccc (unD' (ccc cos))

-- bar :: R -> R :* (R -> R)
-- bar = unD' (reveal (ccc cos))

-- bar :: Syn R (R :* (R -> R))
-- bar = ccc (unD' (reveal (ccc cos)))

-- bar :: Syn R (R :* (R -> R))
-- bar = reveal (ccc (unD' (reveal (ccc cos))))

-- bar :: Syn Bool Bool
-- bar = reveal (ccc not)

-- bar :: Syn R (R :* (R -> R))
-- bar = reveal (ccc (unD' (reveal (ccc (ccc cos)))))

-- bar :: R -> R :* R
-- bar = dsc (unD' (reveal (ccc cos)))

-- bar :: R -> R :* R
-- bar = dsc (dfun id)

-- bar :: R -> R :* R
-- bar = ccc (dsc (dfun id))

-- bar :: Syn R (R :* R)
-- bar = ccc (dsc (dfun id))

-- bar :: Syn R (R :* R)
-- bar = ccc (dsc (dfun id))

-- bar :: EC R (R :* R)
-- bar = ccc (dsc (dfun id))


-- bar :: Syn R (R :* R)
-- bar = ccc (dsc (unD' (reveal (ccc cos))))

-- bar :: Syn R (R :* R)
-- bar = reveal (ccc (dsc (unD' (reveal (ccc cos)))))


-- bar :: String
-- bar = render (ccc (dfun (ccc (cos :: Unop R))))

-- bar :: String
-- bar = render (ccc (dfun (ccc (cos :: Unop R))))

-- test nm f = mkTest nm (runSyn (ccc (dfun (ccc f))))

-- bar :: Syn R (R :* (R -> R))
-- bar = ccc (dfun (ccc (\ x -> 4 + x)))

-- -- dfun h = unD' (reveal (ccc h))

-- bar :: Syn R (R :* (R -> R))
-- bar = reveal (ccc (dfun id))

-- bar :: String
-- bar = render (reveal (ccc (dfun (id :: Unop R))))

-- bar :: String
-- bar = render (ccc (dfun ((\ x_ -> 4) :: Unop R)))

-- bar :: IO ()
-- bar = runSyn (reveal (ccc (dfun (id :: Unop R))))

-- boozle :: String -> (a -> b) -> Test
-- boozle _ _ = undefined
-- {-# NOINLINE boozle #-}
-- {-# RULES
-- "boozle" forall nm f. boozle nm f = mkTest nm (runSyn (ccc (dfun f)))
--  #-}

-- bar :: Test
-- bar = boozle "bar" (id :: Unop R)

-- -- Derivative, then syntactic
-- test' :: String -> (a -> b) -> Test
-- {-# RULES "test AD" forall nm f.
--    test' nm f = mkTest nm (runSyn (ccc (dfun f)))
--  #-}
-- test' nm _f = undefined -- mkTest nm (putStrLn ("test called on " ++ nm))
-- {-# NOINLINE test' #-}

-- bar :: Test
-- bar = boozle "bar" (id :: Unop R)

-- bar :: IO ()
-- bar = runSyn (ccc (dfun (id :: Unop R)))

-- bar :: IO ()
-- bar = runSyn (ccc (dfun ((\ _x -> 4) :: Unop R)))

-- bar :: Test
-- bar = mkTest "bar" (runSyn (ccc (unD' (ccc (A.id :: R -> R)))))

-- bar :: String
-- bar = render (ccc (unD' (ccc (ccc (double :: R -> R)))))

-- bar :: EC R (R :* (R -> R))
-- bar = ccc (dfun id)

-- bar :: EC R (R :* (R -> R))
-- bar = reveal (ccc (dfun id))

-- bar :: IO ()
-- bar = runEC "bar" (ccc (dfun (id :: Unop R)))

#endif

render' :: Syn a b -> String
render' = render
{-# NOINLINE render' #-}

double :: Num a => a -> a
double a = a + a
{-# INLINE double #-}

cosSin :: Floating a => a -> a :* a
cosSin a = (cos a, sin a)
{-# INLINE cosSin #-}

type R = Float
type R2 = R :* R

{--------------------------------------------------------------------
    More examples
--------------------------------------------------------------------}

type R3 = (R,R,R)

three :: R -> R3
three x = (x, x*x, x*x*x)

three' :: R -> (R3,R3)
three' x = (f 5, f 6)
 where
   f y = (x, x*x, x*y*x)

-- bar :: Syn R R3
-- bar = ccc three

addThree :: R3 -> R
addThree (a,b,c) = a+b+c

-- bar :: L R R R
-- bar = ccc id
