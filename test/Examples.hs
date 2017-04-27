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

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS -Wno-type-defaults #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-- To keep ghci happy, it appears that the plugin flag must be in the test module.
{-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}

-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
-- {-# OPTIONS_GHC -dverbose-core2core #-} 

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}

-- Does this flag make any difference?
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

-- Tweak simpl-tick-factor from default of 100
-- {-# OPTIONS_GHC -fsimpl-tick-factor=2800 #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=250 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=5  #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
-- {-# OPTIONS_GHC -dsuppress-uniques #-}
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

import Control.Arrow (second,runKleisli)
import Data.Tuple (swap)
import Data.Maybe
import Distribution.TestSuite
import GHC.Generics hiding (R,D)
import GHC.Exts (lazy,coerce)
import Text.Show.Functions ()  -- for Show

import ConCat.Misc
  (Unop,Binop,(:*),(:+),PseudoFun(..),R,bottom,oops,Yes2,sqr,magSqr)
import ConCat.Rep
import ConCat.Standardize
import ConCat.Free.VectorSpace (V)
import ConCat.Free.LinearRow
import ConCat.Incremental
import ConCat.AD
import ConCat.Interval
import ConCat.Syntactic (Syn,render)
import ConCat.Circuit (GenBuses,(:>),mkGraph)
import ConCat.Image
import qualified ConCat.RunCircuit as RC
import ConCat.RunCircuit (go,Okay)
import ConCat.GLSL (genGlsl,Anim,CAnim)
import ConCat.AltCat ( ccc,reveal,Uncurriable(..),U2(..),(:**:)(..),Ok, Ok2
                     , reprC,abstC,mulC,amb,ambC,asKleisli,recipC, Arr,array,arrAt )
import qualified ConCat.AltCat as A
import ConCat.Rebox () -- experiment
import ConCat.Orphans ()
import ConCat.GradientDescent

import ConCat.Fun

default (Int, Double)

main :: IO ()
main = sequence_
  [ putChar '\n' -- return ()

--   -- Circuit graphs
--   , runEC "magSqr"    (ccc (magSqr @Double))

  , runEC' "magSqr" (magSqr @Double)


--   -- GLSL/WebGL code for GPU-accelerated graphics
--   , runCircGlsl "wobbly-disk" $ ccc $
--       \ t -> disk' (0.75 + 0.25 * cos t)
--   , runCircGlsl "diag-plus-im" $ ccc $
--       \ t ((x,y) :: R2) -> x + sin t > y
--   , runCircGlsl "disk-sizing" $ ccc $
--       disk . cos
--   , runCircGlsl "disk-sizing-p" $ ccc $
--       disk' . cos
--   , runCircGlsl "diag-disk-turning" $ ccc $
--       \ t -> udisk `intersectR` rotate t xPos
--   , runCircGlsl "sqr-sqr-anim" $ ccc $
--       \ t ((x,y) :: R2) -> sqr (sqr x) > y + sin t
--   , runCircGlsl "diag-disk-turning-sizing" $ ccc $
--       \ t -> disk' (cos t) `xorR` rotate t xyPos

  , runCircGlsl' "diag-disk-turning-sizing" $
      \ t -> disk' (cos t) `xorR` rotate t xyPos

--   -- Interval analysis
--   , runEC "add-iv"    (ccc (ivFun (uncurry ((+) @Int))))
--   , runEC "mul-iv"    (ccc (ivFun (uncurry ((*) @Int))))
--   , runEC "thrice-iv" (ccc (ivFun (\ x -> 3 * x :: Int)))
--   , runEC "sqr-iv"    (ccc (ivFun (sqr @Int)))
--   , runEC "magSqr-iv" (ccc (ivFun (magSqr @Int)))
--   , runEC "xp3y-iv"   (ccc (ivFun (\ ((x,y) :: R2) -> x + 3 * y)))
--   , runEC "horner-iv" (ccc (ivFun (horner @Double [1,3,5])))

--   -- Interval analysis
--   , runIv "add"    (uncurry ((+) @Int))
--   , runIv "mul"    (uncurry ((*) @Int))
--   , runIv "thrice" (\ x -> 3 * x :: Int)
--   , runIv "sqr"    (sqr @Int)
--   , runIv "magSqr" (magSqr @Int)
--   , runIv "xp3y"   (\ ((x,y) :: R2) -> x + 3 * y)
--   , runIv "horner" (horner @Double [1,3,5])

  -- Automatic differentiation
  
--   , runEC "sqr-ad" (ccc (andDer (ccc (sqr @R))))

--   , runEC "magSqr-ad" (ccc (andDer (magSqr @R)))

--   , runEC "cos-2x"      (\ x -> cos (2 * x) :: R)
--   , runEC "cos-2xx"     (\ x -> cos (2 * x * x) :: R)
--   , runEC "cos-xpy"     (\ (x,y) -> cos (x + y) :: R)
--   , runEC "cos-xy" (\ (x,y) -> cos (x * y) :: R)
--   , runEC "cos-xy-d1" (der (\ (x,y) -> cos (x * y) :: R))
--   , runEC "cos-xy-d2" (der (der (\ (x,y) -> cos (x * y) :: R)))
--   , runEC "cosSin-xy" (cosSinProd @R)
--   , runEC "cosSin-xy-d1" (der (cosSinProd @R))
--   , runEC "cosSin-xy-ad1" (andDer (\ (x,y) -> cosSin (x * y) :: R2))
--   , runEC "cosSin-xy-ad1-i" (inc (andDer (\ (x,y) -> cosSin (x * y) :: R2)))
--   , runEC "cosSin-xyz" (\ (x,y,z) -> cosSin (x * y + x * z + y * z) :: R2)
--   , runEC "cosSin-xyz-d1" (der (\ (x,y,z) -> cosSin (x * y + x * z + y * z) :: R2))



  ]

runIv :: (Ok2 IF a b, Ok2 (:>) (Iv a) (Iv b))
      => String -> (a -> b) -> IO ()
runIv nm = oops ("runIv " ++ nm)
{-# NOINLINE runIv #-}
{-# RULES "runIv" forall nm f.
  runIv nm f = runEC (nm ++ "-iv") (ccc (ivFun f)) #-}

runEC' :: Ok2 (:>) a b => String -> (a -> b) -> IO ()
runEC' nm = oops ("runEC' " ++ nm)
{-# NOINLINE runEC' #-}
{-# RULES "runEC'" forall nm f.
  runEC' nm f = let (syn :**: circ) = ccc f in runSyn syn >> runCirc nm circ  #-}

runCircGlsl' :: String -> Anim -> IO ()
runCircGlsl' nm = oops ("runCircGlsl' " ++ nm)
{-# NOINLINE runCircGlsl' #-}
{-# RULES "runCircGlsl'" forall nm f.
  runCircGlsl' nm f = let circ = ccc f in runCirc nm circ >> genGlsl nm circ #-}


{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

type EC = Syn :**: (:>)

runU2 :: U2 a b -> IO ()
runU2 = print

type GO a b = (GenBuses a, Ok2 (:>) a b)

runSyn :: Syn a b -> IO ()
runSyn syn = putStrLn ('\n' : render syn)

runEC :: GO a b => String -> EC a b -> IO ()
runEC nm (syn :**: circ) = runSyn syn >> runCirc nm circ

runCirc :: GO a b => String -> (a :> b) -> IO ()
runCirc nm circ = RC.run nm [] circ

runCircGlsl :: String -> CAnim -> IO ()
runCircGlsl nm circ = runCirc nm circ >> genGlsl nm circ

{--------------------------------------------------------------------
    Misc definitions
--------------------------------------------------------------------}

cosSin :: Floating a => a -> a :* a
cosSin a = (cos a, sin a)

cosSinProd :: Floating a => a :* a -> a :* a
cosSinProd (x,y) = (cos z, sin z) where z = (x * y)

horner :: Num a => [a] -> a -> a
horner []     _ = 0
horner (c:cs) a = c + a * horner cs a

-- Non-inlining versions:

-- horner coeffs a = foldr (\ w z -> w + a * z) 0 coeffs

-- horner coeffs0 a = go coeffs0
--  where
--    go [] = a
--    go (c:cs) = c + a * go cs
