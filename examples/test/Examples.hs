-- -*- flycheck-disabled-checkers: '(haskell-ghc haskell-stack-ghc); -*-

-- stack build :examples
--
-- stack build && stack build :examples >& ~/Haskell/concat/out/o1

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE DataKinds           #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS -Wno-type-defaults #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-- To keep ghci happy, it appears that the plugin flag must be in the test module.
{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}

{-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
-- {-# OPTIONS_GHC -ddump-simpl #-} 
-- {-# OPTIONS_GHC -dverbose-core2core #-} 

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}

-- Does this flag make any difference?
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

-- Tweak simpl-tick-factor from default of 100
-- {-# OPTIONS_GHC -fsimpl-tick-factor=2800 #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=250 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=5  #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}


----------------------------------------------------------------------
-- |
-- Module      :  Examples
-- Copyright   :  (c) 2017 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Suite of automated tests
----------------------------------------------------------------------

module Main where

import Data.Monoid (Sum(..))
import Data.Foldable (fold)
import Control.Applicative (liftA2)

import ConCat.Misc ((:*),R,sqr,magSqr,Binop,inNew,inNew2)
import ConCat.Incremental (inc)
import ConCat.AD
import ConCat.GradientDescent (maximize,minimize)
import ConCat.Interval
import ConCat.Syntactic (Syn,render)
import ConCat.Circuit (GenBuses,(:>))
import ConCat.Image
import qualified ConCat.RunCircuit as RC
import ConCat.GLSL (genGlsl,CAnim)
import ConCat.AltCat (ccc,U2(..),(:**:)(..),Ok2, Arr, array,arrAt) --, Ok, Ok3
import ConCat.Rebox () -- necessary for reboxing rules to fire
import ConCat.Arr -- (liftArr2,FFun,arrFFun)  -- and (orphan) instances
import qualified ConCat.SMT as SMT

-- These imports bring newtype constructors into scope, allowing CoerceCat (->)
-- dictionaries to be constructed. We could remove the LinearRow import if we
-- changed L from a newtype to data, but we still run afoul of coercions for
-- GHC.Generics newtypes.
-- 
-- TODO: Find a better solution!
import qualified GHC.Generics as G
import qualified ConCat.Free.LinearRow

import Control.Newtype (Newtype(..))

default (Int, Double)

main :: IO ()
main = sequence_
  [ putChar '\n' -- return ()

  -- -- Circuit graphs
  -- , runSynCirc "magSqr"    $ ccc $ magSqr @Double
  -- , runSynCirc "cosSin-xy" $ ccc $ cosSinProd @R
  -- , runSynCirc "xp3y"      $ ccc $ \ (x,y) -> x + 3 * y :: R
  -- , runSynCirc "horner"    $ ccc $ horner @Double [1,3,5]

  -- -- GLSL/WebGL code for GPU-accelerated graphics
  -- , runCircGlsl "wobbly-disk" $ ccc $
  --     \ t -> disk' (0.75 + 0.25 * cos t)
  -- , runCircGlsl "diag-plus-im" $ ccc $
  --     \ t ((x,y) :: R2) -> x + sin t > y
  -- , runCircGlsl "disk-sizing" $ ccc $
  --     disk . cos
  -- , runCircGlsl "disk-sizing-p" $ ccc $
  --     disk' . cos
  -- , runCircGlsl "diag-disk-turning" $ ccc $
  --     \ t -> udisk `intersectR` rotate t xPos
  -- , runCircGlsl "sqr-sqr-anim" $ ccc $
  --     \ t ((x,y) :: R2) -> sqr (sqr x) > y + sin t
  -- , runCircGlsl "diag-disk-turning-sizing" $ ccc $
  --     \ t -> disk' (cos t) `xorR` rotate t xyPos

  -- -- Interval analysis
  -- , runSynCirc "add-iv"    $ ccc $ ivFun $ uncurry ((+) @Int)
  -- , runSynCirc "mul-iv"    $ ccc $ ivFun $ uncurry ((*) @Int)
  -- , runSynCirc "thrice-iv" $ ccc $ ivFun $ \ x -> 3 * x :: Int
  -- , runSynCirc "sqr-iv"    $ ccc $ ivFun $ sqr @Int
  -- , runSynCirc "magSqr-iv" $ ccc $ ivFun $ magSqr @Int
  -- , runSynCirc "xp3y-iv"   $ ccc $ ivFun $ \ ((x,y) :: R2) -> x + 3 * y
  -- , runSynCirc "xyp3-iv"   $ ccc $ ivFun $ \ (x,y) -> x * y + 3 :: R
  -- , runSynCirc "horner-iv" $ ccc $ ivFun $ horner @Double [1,3,5]

  -- -- Automatic differentiation
  -- , runSynCirc "sin-ad"       $ ccc $ andDer $ sin @R
  -- , runSynCirc "cos-ad"       $ ccc $ andDer $ cos @R
  -- , runSynCirc "sqr-ad"       $ ccc $ andDer $ sqr @R
  -- , runSynCirc "magSqr-ad"    $ ccc $ andDer $ magSqr @R
  -- , runSynCirc "cos-2x-ad"    $ ccc $ andDer $ \ x -> cos (2 * x) :: R
  -- , runSynCirc "cos-2xx-ad"   $ ccc $ andDer $ \ x -> cos (2 * x * x) :: R
  -- , runSynCirc "cos-xpy-ad"   $ ccc $ andDer $ \ (x,y) -> cos (x + y) :: R
  -- , runSynCirc "cosSin-xy-ad" $ ccc $ andDer $ cosSinProd @R

  -- -- Dies with "Oops --- ccc called!", without running the plugin.
  -- , print $ andDer sin (1 :: R)

  -- -- (0.8414709848078965,[[0.5403023058681398]]), i.e., (sin 1, [[cos 1]]),
  -- -- where the "[[ ]]" is matrix-style presentation of the underlying
  -- -- linear map.
  -- , runPrint 1     $ andDer $ sin @R
  -- , runPrint (1,1) $ andDer $ \ (x,y) -> cos (x + y) :: R
  -- , runPrint (1,1) $ andDer $ cosSinProd @R

  -- , runPrint 1     $ gradient $ sin @R
  -- , runPrint (1,1) $ gradient $ \ (x,y) -> cos (x + y) :: R

  -- , print (minimize 1 cos 5)  -- (3.141592653589793,6)
  -- , print (maximize 1 cos 5)  -- (6.283185307179586,5)

  -- , runSynCirc "gradient-sin" $ ccc $ gradient sin

  -- -- Incremental differentiation. Currently broken.
  -- , runSynCirc "magSqr-inc" $ ccc $ inc $ andDer $ magSqr @R

  -- , runCirc "smt-a" $ ccc $ (\ (x :: Double) -> sqr x == 9)

  -- , runCircSMT "smt-a" $ ccc $ \ (x :: Double) -> sqr x == 9
  -- , runSMT $ ccc $ \ (x :: Double) -> sqr x == 9
  -- , runSMT $ ccc $ \ (x :: Double) -> sqr x == 9 && x < 0
  -- , runSMT $ ccc $ pred1 @Double
  -- , runSMT $ ccc $ \ b -> (if b then 3 else 5 :: Int) > 4
  -- , runSMT $ ccc $ \ (x::R,y) -> x + y == 15 && x == 2 * y 

  -- -- Broken
  -- , runSMT $ ccc $ (\ (x::R,y) -> x + y == 15 && x * y == 20)  -- "illegal argument" ??
  -- , runSyn $ ccc $ (\ (x :: Int) -> x == 9)

  -- Recursion experiments
  -- , runSynCirc "fac1" $ ccc $ fac1  -- bare unboxed var
  -- , runSynCirc "fac2" $ ccc $ fac2 -- infinite compilation loop
  -- , runSynCirc "fac3" $ ccc $ fac3 -- same infinite compilation loop
  -- , runSynCirc "fac4" $ ccc $ fac4 -- same infinite compilation loop
  -- , runSynCirc "fac5" $ ccc $ -- same infinite compilation loop
  --     \ (n0 :: Int) -> let go n = if n < 1 then 1 else n * go (n-1) in
  --                        go n0

  -- , runSynCirc "fac6" $ ccc $ -- unhandled letrec
  --     \ (n0 :: Int, n1) -> let go n = if n < 1 then n1 else n * go (n-1) in
  --                        go n0

  -- , runSynCirc "fac7" $ ccc $ fac7

  -- , runSynCirc "fac8" $ ccc $ fac8 -- compilation loop
  -- , runSynCirc "fac9" $ ccc $ fac9 -- compilation loop


  -- Array experiments

  -- , runSynCirc "map-negate-arr" $ ccc $ fmap @(Arr Bool) @Int negate

  -- , runSynCirc "map-map-arr" $ ccc $ fmap (+3) . fmap @(Arr Bool) @Int (+2)

  -- , runSynCirc "liftA2-arr-b" $ ccc $ uncurry $ liftA2 @(Arr Bool) ((+) @Int)

  -- , runSynCirc "fmap-arr-bool-plus" $ ccc $ fmap @(Arr Bool) ((+) @Int)
  -- , runSynCirc "app-arr-bool" $ ccc $ (<*>) @(Arr Bool) @Int @Int

  -- , runSynCirc "fmap-fun-bool-plus" $ ccc $ fmap   @((->) Bool) ((+) @Int)
  -- , runSynCirc "app-fun-bool"       $ ccc $ (<*>)  @((->) Bool) @Int @Int

  -- , runSynCirc "liftA2-fun-bool"    $ ccc $ liftA2 @((->) Bool) ((+) @Int)

  -- , runSynCirc "sum-arr-lb1" $ ccc $ sum @(Arr (LB N1)) @Int
  -- , runSynCirc "sum-arr-lb2" $ ccc $ sum @(Arr (LB N2)) @Int
  -- , runSynCirc "sum-arr-lb3" $ ccc $ sum @(Arr (LB N3)) @Int
  -- , runSynCirc "sum-arr-lb4" $ ccc $ sum @(Arr (LB N4)) @Int
  -- , runSynCirc "sum-arr-lb8" $ ccc $ sum @(Arr (LB N8)) @Int

  -- , runSynCirc "fmap-fun-bool-plus" $ ccc $ fmap   @((->) Bool) ((+) @Int)
  -- , runSynCirc "app-fun-bool"       $ ccc $ (<*>)  @((->) Bool) @Int @Int
  -- , runSynCirc "inArr2-liftA2-bool"    $ ccc $
  --      (inNew2 (liftA2 (+)) :: Binop (Arr Bool Int))

  -- , runSynCirc "sum-fun-2" $ ccc $ (sum @((->) Bool) @Int)
  -- , runSynCirc "sum-fun-4" $ ccc $ (sum @((->) (Bool :* Bool)) @Int)

  -- , runSynCirc "sum-fun-8" $ ccc $ (sum @((->) ((Bool :* Bool) :* Bool)) @Int)

  -- , runSynCirc "unpack-arr-2" $ ccc $ (unpack @(Arr Bool Int))
  -- , runSynCirc "unpack-arr-4" $ ccc $ (unpack @(Arr (Bool :* Bool) Int))

  -- , runSynCirc "sum-arr-fun-2"    $ ccc $
  --      (sum . unpack :: Arr Bool Int -> Int)
  -- , runSynCirc "sum-arr-fun-4"    $ ccc $
  --      (sum . unpack :: Arr (Bool :* Bool) Int -> Int)
  -- , runSynCirc "sum-arr-fun-8"    $ ccc $
  --      (sum . unpack :: Arr ((Bool :* Bool) :* Bool) Int -> Int)

  -- , runSynCirc "fmap-arr-bool" $ ccc $ fmap @(Arr Bool) (negate @Int)
  -- , runSynCirc "liftA2-arr-bool" $ ccc $ liftA2 @(Arr Bool) ((+) @Int)
  -- , runSynCirc "liftArr2-bool" $ ccc $ liftArr2 @Bool ((+) @Int)
  -- , runSynCirc "liftArr2-bool-unc" $ ccc $ uncurry (liftArr2 @Bool ((+) @Int))
  -- , runSynCirc "sum-arr-bool" $ ccc $ sum @(Arr Bool) @Int

  -- -- Int equality turns into matching, which takes some care.
  -- -- See boxCon/tweak in ConCat.Plugin
  -- , runSynCirc "equal-3"     $ ccc $ \ (x :: Int) -> x == 3
  -- , runSynCirc "unequal-3"   $ ccc $ \ (x :: Int) -> x /= 3
  -- , runSynCirc "not-equal-3" $ ccc $ \ (x :: Int) -> not (x == 3)

  -- , runSynCirc "multi-if-equal-int" $ ccc $
  --     \ case
  --         1 -> 3
  --         5 -> 7
  --         7 -> 9
  --         (_ :: Int) -> 0 :: Int

  -- , runSynCirc "foo" $ ccc $ div @Int

  -- , runSynCirc "foo" $ ccc $ (*) @Int

  -- , runSynCirc "foo" $ ccc $ \ (x :: Int) -> 13 * x == 130

  , runSynCirc "multi-if-equal-int-scrut" $ ccc $
      \ x -> case 13 * x of
          1 -> 3
          5 -> 7
          7 -> 9
          (_ :: Int) -> 0 :: Int

  -- , runSynCirc "if-equal-int-x" $ ccc $
  --     \ x -> case x of
  --         5 -> x `div` 2
  --         (_ :: Int) -> 0 :: Int

  ]

f1 :: Num a => a -> a
f1 x = x^2

pred1 :: (Num a, Ord a) => a :* a -> Bool
pred1 (x,y) =
    x < y &&
    y < 100 &&
    foo x 20 f &&
    0 <= x - 3 + 7 * y &&
    (x == y || y + 20 == x + 30)
  where
    f z k = z > 100 && k 20
    foo a b g = g 222 (< a + b)


{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

type EC = Syn :**: (:>)

runU2 :: U2 a b -> IO ()
runU2 = print

type GO a b = (GenBuses a, Ok2 (:>) a b)

runSyn :: Syn a b -> IO ()
runSyn syn = putStrLn ('\n' : render syn)

runSynCirc :: GO a b => String -> EC a b -> IO ()
runSynCirc nm (syn :**: circ) = runSyn syn >> runCirc nm circ

runCirc :: GO a b => String -> (a :> b) -> IO ()
runCirc nm circ = RC.run nm [] circ

runCircGlsl :: String -> CAnim -> IO ()
runCircGlsl nm circ = runCirc nm circ >> genGlsl nm circ

runSMT :: (GenBuses a, Show a, SMT.EvalE a) => (a :> Bool) -> IO ()
runSMT circ = SMT.solve circ >>= print

runCircSMT :: (GenBuses a, Show a, SMT.EvalE a) => String -> (a :> Bool) -> IO ()
runCircSMT nm circ = runCirc nm circ >> runSMT circ

-- TODO: rework runCircGlsl and runCircSMT to generate the circuit graph once
-- rather than twice.

runPrint :: Show b => a -> (a -> b) -> IO ()
runPrint a f = print (f a)

{--------------------------------------------------------------------
    Vectors
--------------------------------------------------------------------}

data Nat = Zero | Succ Nat

-- So we don't need -Wno-unticked-promoted-constructors
type Zero = 'Zero
type Succ = 'Succ

type family LVec n a where
  LVec Zero a = ()
  -- LVec (Succ n) a = LVec n a :* a
  LVec N1 a = a
  LVec (Succ (Succ n)) a = LVec (Succ n) a :* a

type LB n = LVec n Bool

type N0  = Zero
-- Generated code
-- 
--   putStrLn $ unlines ["type N" ++ show (n+1) ++ " = S N" ++ show n | n <- [0..31]]
type N1  = Succ N0
type N2  = Succ N1
type N3  = Succ N2
type N4  = Succ N3
type N5  = Succ N4
type N6  = Succ N5
type N7  = Succ N6
type N8  = Succ N7
type N9  = Succ N8
type N10 = Succ N9
type N11 = Succ N10
type N12 = Succ N11
type N13 = Succ N12
type N14 = Succ N13
type N15 = Succ N14
type N16 = Succ N15
-- ...

{--------------------------------------------------------------------
    Misc definitions
--------------------------------------------------------------------}

cosSin :: Floating a => a -> a :* a
cosSin a = (cos a, sin a)

cosSinProd :: Floating a => a :* a -> a :* a
cosSinProd (x,y) = cosSin (x * y)

horner :: Num a => [a] -> a -> a
horner []     _ = 0
horner (c:cs) a = c + a * horner cs a

-- Non-inlining versions:

-- horner coeffs a = foldr (\ w z -> w + a * z) 0 coeffs

-- horner coeffs0 a = go coeffs0
--  where
--    go [] = a
--    go (c:cs) = c + a * go cs

-- foo1 :: R -> L R R R
-- foo1 = coerce

fac1 :: Int -> Int
fac1 0 = 1
fac1 n = n * fac1 (n-1)

fac2 :: Int -> Int
fac2 n = if n < 1 then 1 else n * fac2 (n-1)

fac3 :: Int -> Int
fac3 = go
 where
   go n = if n < 1 then 1 else n * go (n-1)

fac4 :: Int -> Int
fac4 n0 = go n0
 where
   go n = if n < 1 then 1 else n * go (n-1)


fac7 :: Int :* Int -> Int
fac7 (n0,n1) = go n0
 where
   go n = if n < 1 then n1 else n * go (n-1)

fac8 :: Int -> Int
fac8 n0 = go n0 1
 where
   go n acc = if n < 1 then acc else go (n-1) (n * acc)

fac9 :: Int -> Int
fac9 n0 = go (n0,1)
 where
   go (n,acc) = if n < 1 then acc else go (n-1,n * acc)
