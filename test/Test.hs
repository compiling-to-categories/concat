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

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
-- {-# OPTIONS_GHC -Wno-unused-binds   #-}
-- {-# OPTIONS_GHC -Wno-redundant-constraints #-}

-- To keep ghci happy, it appears that the plugin flag must be in the test module.
{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}

-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
-- {-# OPTIONS_GHC -dverbose-core2core #-}

----------------------------------------------------------------------
-- |
-- Module      :  Test
-- Copyright   :  (c) 2017 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Suite of automated tests
----------------------------------------------------------------------

module Main where

import Prelude hiding (Float,Double)   -- ,id,(.),const

import Control.Arrow (second)
import Data.Tuple (swap)
import Data.Maybe
import Distribution.TestSuite
import GHC.Generics hiding (R,D)
import GHC.Exts (lazy,coerce)

import ConCat.Misc (Unop,Binop,(:*),PseudoFun(..),R,bottom,oops,Yes2)
import ConCat.Rep
import ConCat.Float
import ConCat.Free.VectorSpace (V)
import ConCat.Free.LinearRow
import ConCat.Incremental
import ConCat.GAD
import ConCat.AD
import ConCat.Syntactic (Syn,render)
import ConCat.Circuit (GenBuses)
import qualified ConCat.RunCircuit as RC
import ConCat.RunCircuit (go,Okay,(:>))
import ConCat.AltCat (ccc,reveal,Uncurriable(..),U2(..),(:**:)(..),Ok2,reprC,abstC,mulC)
import qualified ConCat.AltCat as A
import ConCat.Rebox () -- experiment
import ConCat.Orphans ()

main :: IO ()
main = sequence_
  [ return ()

--   , test "magSqr-ad1" (andDer (magSqr @R))
--   , test "magSqr-ad1-inc" (inc (andDer (magSqr @R)))

--   , test "negate-ai" (andInc (negate :: Unop Int))

--   , test "xy" (\ (x,y) -> x * y :: R)

--   , test "xy-ad" (andDer (\ (x,y) -> x * y :: R))

--   , test "xy-i" (inc (\ (x,y) -> x * y :: R))

  , test "xy-ai" (andInc (\ (x,y) -> x * y :: R))

--   , test "cond" (\ x -> if x > 0 then x else negate x :: Int)

--   , test "cond-fun" (\ x -> (if x > 0 then id else negate) x :: Int)

--   , test "sop1" (\ (x,y,z) -> x * y + y * z + x * z :: R)
--   , test "sop1-ai" (andInc (\ (x,y,z) -> x * y + y * z + x * z :: R))

--   , test "sum4" (\ (a,b,c,d) -> (a+b)+(c+d) :: R)

--   , test "sum4-ai" (andInc (\ (a,b,c,d) -> (a+b)+(c+d) :: Int))

--   , test "sum8" (\ ((a,b,c,d),(e,f,g,h)) -> ((a+b)+(c+d))+((e+f)+(g+h)) :: R)
--   , test "sum8-ai" (andInc (\ ((a,b,c,d),(e,f,g,h)) -> ((a+b)+(c+d))+((e+f)+(g+h)) :: R))

--   , test "magSqr"            (magSqr @R)
--   , test "magSqr-ai" (andInc (magSqr @R))
--   , test "magSqr-i"     (inc (magSqr @R))

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

--   , test "three" three
--   , test "threep" three'
--   , test "addThree" addThree

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

test :: Con a b => String -> (a -> b) -> IO ()
test nm _f = oops ("test called on " ++ nm)
{-# NOINLINE test #-}

tst :: Con a b => (a -> b) -> IO ()
tst = test "tst"
{-# NOINLINE tst #-}

-- TODO: maybe a rewrite rule for tst.

#if 0
type Con = Yes2
{-# RULES "ccc (->)" forall nm f. test nm f = runF (ccc f) #-}
#elif 0
type Con = Yes2
{-# RULES "U2" forall nm f. test nm f = runU2 (ccc f) #-}
#elif 0
type Con = Yes2
{-# RULES "Syn" forall nm f. test nm f = runSyn (ccc f) #-}
#elif 0
type Con a b = GO a b
{-# RULES "(:>)" forall nm f. test nm f = runCirc nm (ccc f) #-}
#elif 0
type Con = Uncurriable Syn
{-# RULES "Syn; uncurries" forall nm f. test nm f = runSyn (uncurries (ccc f)) #-}
#elif 0
type Con = Uncurriable Syn
{-# RULES "uncurries; Syn" forall nm f. test nm f = runSyn (ccc (uncurries f)) #-}
#elif 0
type Con = Uncurriable (->)
{-# RULES "(->); uncurries; Syn" forall nm f. test nm f = runSyn (ccc (uncurries (ccc f))) #-}
#elif 1
type Con a b = GO a b
{-# RULES "Syn :**: (:>)" forall nm f. test nm f = runEC nm (ccc f) #-}
#elif 0
type Con a b = GO a b
{-# RULES "(->); Syn :**: (:>)" forall nm f. test nm f = runEC nm (ccc (ccc f)) #-}
#elif 0
type Con a b = (GenBuses (UncDom a b), Uncurriable (Syn :**: (:>)) a b)
{-# RULES "uncurries ; Syn :**: (:>)" forall nm f. test nm f = runEC nm (uncurries (ccc f)) #-}
#elif 0
type Con a b = (GenBuses (UncDom a b), Uncurriable (->) a b)
{-# RULES "uncurries ; Syn :**: (:>)" forall nm f. test nm f = runEC nm (ccc (uncurries f)) #-}
#elif 0
type Con = Okay  -- rename
{-# RULES "(->); (:>)" forall nm f. test nm f = go nm (ccc f) #-}
#elif 0
type Con = Yes2
{-# RULES "L ; Syn" forall nm f. test nm f = runSyn (ccc (\ () -> lmap @R f)) #-}
#elif 0
type Con = Yes2
{-# RULES "(->) ; L ; Syn" forall nm f. test nm f = runSyn (ccc (\ () -> lmap @R (ccc f))) #-}
#elif 0
type Q a b = (V R a :-* V R b) R
type Con a b = (GenBuses (UncDom () (Q a b)), Uncurriable (:>) () (Q a b))
{-# RULES "L ; Syn+circuit" forall nm f.
    test nm f = runEC (nm++"-lmap") (ccc (\ () -> repr (lmap @R f))) #-}
#elif 0
type Con = Yes2
{-# RULES "andDer ; ccc" forall nm f. test nm f = runSyn (ccc (andDer f)) #-}
#elif 0
type Con = Yes2
{-# RULES "(->); D; Syn" forall nm f. test nm f = runSyn (ccc (andDer (ccc f))) #-}
#elif 0
type Con a b = (Ok2 (L R) a b, HasL (V R a))
{-# RULES "(->); D'; EC" forall nm f. test nm f = runSyn (ccc (ADFun.andDer (ccc f))) #-}
#elif 0
type Con a b = GO a b
{-# RULES "(->); D; (:>)" forall nm f. test nm f = runCirc (nm++"-ad") (ccc (andDer (ccc f))) #-}
#elif 0
type Con a b = GO a b
{-# RULES "(->); D; EC" forall nm f. test nm f = runEC (nm++"-ad") (ccc (andDer (ccc f))) #-}
#elif 0
type Con a b = GO a b
{-# RULES "(->); D; EC" forall nm f. test nm f = runEC (nm++"-d") (ccc (der (ccc f))) #-}
#elif 1
type Con a b = GO a b
{-# RULES "(->); D; EC" forall nm f. test nm f = runEC (nm++"-d2") (ccc (der (der (ccc f)))) #-}
#elif 0
type Con a b = (Ok2 (L R) a b, HasL (V R a), GO a b)
{-# RULES "(->); D'; EC" forall nm f. test nm f = runEC (nm++"-adf") (ccc (ADFun.andDer (ccc f))) #-}
#elif 0
type Con a b = (Ok2 (L R) a b, HasL (V R a), GO a b)
{-# RULES "(->); D; EC" forall nm f. test nm f = runEC (nm++"-derf") (ccc (ADFun.der (ccc f))) #-}
#else
 #OOPS#
#endif

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

#if 0

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

#endif
