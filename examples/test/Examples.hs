-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}
-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showResiduals #-}
-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showCcc #-}

-- To run:
--
--   stack build :misc-examples
--
--   stack build :misc-trace >& ~/Haskell/concat/out/o1
--
-- You might also want to use stack's --file-watch flag for automatic recompilation.

{-# LANGUAGE CPP                     #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE ViewPatterns            #-}
{-# LANGUAGE PatternSynonyms         #-}
{-# LANGUAGE DataKinds               #-}

-- For OkLC as a class
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE MultiParamTypeClasses   #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS -Wno-type-defaults #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

-- Now in concat-examples.cabal
-- {-# OPTIONS_GHC -fplugin=ConCat.Plugin #-}

-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:maxSteps=100 #-}

-- {-# OPTIONS_GHC -fno-specialise #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}
-- {-# OPTIONS_GHC -dverbose-core2core #-}

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}
-- {-# OPTIONS_GHC -ddump-rules #-}

-- Does this flag make any difference?
-- {-# OPTIONS_GHC -fexpose-all-unfoldings #-}

-- Tweak simpl-tick-factor from default of 100
-- {-# OPTIONS_GHC -fsimpl-tick-factor=2500 #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=500 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=250 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=25  #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=5  #-}

-- {-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-idinfo #-}
-- {-# OPTIONS_GHC -dsuppress-module-prefixes #-}

-- {-# OPTIONS_GHC -ddump-tc-trace #-}

-- {-# OPTIONS_GHC -dsuppress-all #-}

-- {-# OPTIONS_GHC -fno-float-in #-}
-- {-# OPTIONS_GHC -ffloat-in #-}
-- {-# OPTIONS_GHC -fdicts-cheap #-}
{-# OPTIONS_GHC -fdicts-strict #-}

-- For experiments
{-# OPTIONS_GHC -Wno-orphans #-}

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

import Prelude hiding (unzip,zip,zipWith) -- (id,(.),curry,uncurry)
import qualified Prelude as P

import Data.Monoid (Sum(..))
import Data.Foldable (fold)
import Control.Applicative (liftA2)
import Control.Arrow (second)
import Control.Monad ((<=<))
import Data.List (unfoldr)  -- TEMP
import Data.Complex (Complex)
import GHC.Exts (inline)
import GHC.Float (int2Double)
import GHC.TypeLits ()

-- packFiniteM experiment
import GHC.TypeLits
import Data.Maybe (fromJust)
import GHC.Integer

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed
import Data.Key
import Data.Distributive
import Data.Functor.Rep
import qualified Data.Functor.Rep as FR
import Data.Vector.Sized (Vector)

import ConCat.Misc
import ConCat.Rep (HasRep(..))
import qualified ConCat.Category as C
import ConCat.Incremental (andInc,inc)
import ConCat.Dual
import ConCat.GAD
import ConCat.Additive
import ConCat.AdditiveFun
import ConCat.AD
import ConCat.ADFun hiding (D)
-- import qualified ConCat.ADFun as ADFun
import ConCat.RAD
import ConCat.Free.VectorSpace (HasV(..),distSqr,(<.>),normalizeV)
-- import ConCat.GradientDescent
import ConCat.Interval
import ConCat.Syntactic (Syn,render)
import ConCat.Circuit (GenBuses,(:>))
import qualified ConCat.RunCircuit as RC
import qualified ConCat.AltCat as A
-- import ConCat.AltCat
import ConCat.AltCat
  (toCcc,toCcc',unCcc,unCcc',conceal,(:**:)(..),Ok,Ok2,U2,equal)
import qualified ConCat.Rep
import ConCat.Rebox () -- necessary for reboxing rules to fire
import ConCat.Orphans ()
import ConCat.Nat
import ConCat.Shaped
-- import ConCat.Scan
-- import ConCat.FFT
import ConCat.Free.LinearRow -- (L,OkLM,linearL)
import ConCat.LC
import ConCat.Deep
import qualified ConCat.Deep as D
-- import ConCat.Finite
import ConCat.Isomorphism
import ConCat.TArr
import qualified ConCat.TArr as TA

-- Experimental
import qualified ConCat.Inline.SampleMethods as I

import qualified ConCat.Regress as R
import ConCat.Free.Affine
import ConCat.Choice
-- import ConCat.RegressChoice

-- import ConCat.Vector -- (liftArr2,FFun,arrFFun)  -- and (orphan) instances
#ifdef CONCAT_SMT
import ConCat.SMT
#endif

-- These imports bring newtype constructors into scope, allowing CoerceCat (->)
-- dictionaries to be constructed. We could remove the LinearRow import if we
-- changed L from a newtype to data, but we still run afoul of coercions for
-- GHC.Generics newtypes.
--
-- TODO: Find a better solution!
import qualified GHC.Generics as G
import qualified ConCat.Free.LinearRow
import qualified Data.Monoid

-- For FFT
import GHC.Generics hiding (C,R,D)

import Control.Newtype.Generics (Newtype(..))

-- Experiments
import GHC.Exts (Coercible,coerce)

import Miscellany

main :: IO ()
main = sequence_ [
    putChar '\n' -- return ()

    -- , runSyn S.t14'

  -- , runSyn $ toCcc $ A.addC . A.dup
  -- , runSyn $ toCcc $ A.addC . (A.id A.&&& A.id)

  -- -- first add . first dup

  -- , runSynStack $ toCcc $ id @ Int

  -- , runSynStack $ toCcc $ negate . negate @ Int

  -- , runSynStack $ toCcc $ \ (x :: Int) -> x  -- fine
  -- , runSyn $ toCcc $ \ (x :: Int) -> (x,x) -- fine
  -- , runSyn $ toCcc $ A.id A.&&& A.id -- fine
  -- , runSyn $ toCcc $ A.addC . (A.id A.&&& A.id) -- okay

  -- , runSynStack $ toCcc $ A.addC . A.dup


  -- -- first add . ((first swapP . (lassocP . id . rassocP) . first swapP) . lassocP . id . rassocP) . first dup
  -- , runSynStack $ toCcc $ A.addC . (A.id A.&&& A.id)

  -- -- [first dup,first addC]
  -- , runChainStack $ toCcc $ A.addC . A.dup

  -- -- [first dup,rassocP,lassocP,first swapP,rassocP,lassocP,first swapP,first addC]
  -- -- [first dup,first addC]  -- with AltCat rule (id &&& id) = dup
  -- , runChainStack $ toCcc $ A.addC . (A.id A.&&& A.id)

  -- -- twice x = x + x
  -- , runSyn        $ toCcc twice  -- addC . dup
  -- , runSynStack   $ toCcc twice  -- first addC . first dup

  -- , runSynStack $ toCcc $ \ x     -> x + x  -- addC . dup, [Dup,Add]
  -- , runSynStack $ toCcc $ \ (x,y) -> x * y  -- mulC, [Mul]

  -- -- addC . (exl *** mulC . (const 3 *** exr) . dup) . dup
  -- -- [Dup,Push,Exl,Pop,Swap,Push,Dup,Push,Const 3,Pop,Swap,Push,Exr,Pop,Swap,Mul,Pop,Swap,Add]
  -- -- TODO: better categorical optimization
  -- , runSynStack $ toCcc $ \ (x,y) -> x + 3 * y

  -- , runSynStack $ toCcc $ \ y -> 3 * y

  -- , runSyn $ toCcc' $ A.lassocP A.. A.rassocP                  -- id
  -- , runSyn $ toCcc' $ A.lassocP A.. A.id A.. A.rassocP         -- id
  -- , runSyn $ toCcc' $ A.first A.id                             -- id
  -- , runSyn $ toCcc' $ A.lassocP A.. A.first A.id A.. A.rassocP -- id

  -- , runSynCirc "sum-fun-B" $ toCcc $ sum @((->) Bool) @Int
  -- , runSynCirc "sum-fun-BxB" $ toCcc $ sum @((->) (Bool :* Bool)) @Int

  -- , runSynCirc "foo" $ toCcc $ \ (arr :: Arr Bool Int) -> arr `FR.index` False -- okay

  -- , runSynCirc "sum-arr-B"   $ toCcc $ sum @(Arr Bool) @Int -- okay

  -- , runSynCirc "arrSplitProd-B-B" $ toCcc $ arrSplitProd @Bool @Bool @Int -- okay

  -- , runSynCirc "foo" $ toCcc $ arrSplitProd @Bool @Bool @(Sum Int) -- okay

  -- , runSynCirc "foo" $ toCcc $ fmap fold . arrSplitProd @Bool @Bool @(Sum Int) -- fail

  -- , runSynCirc "foo" $ toCcc $ fmap @(Vector 2) not -- okay

  -- , runSynCirc "foo" $ toCcc $ fmap @(Arr Bool) not -- okay

  -- , runSynCirc "foo" $ toCcc $ fmap @(Arr Bool) @(Arr Bool (Sum Int)) fold 

  -- , runSynCirc "foo" $ toCcc $ fold @(Arr Bool) @(Sum Int) --

  -- , runSynCirc "foo" $ toCcc $ (TA.!) @Bool @(Sum Int)

  -- , runSynCirc "sum-arr-BxB" $ toCcc $ sum @(Arr (Bool :* Bool)) @Int -- okay

  -- , runSynCirc "sum-arr-BxBxB-r" $ toCcc $ sum @(Arr (Bool :* (Bool :* Bool))) @Int -- okay
  -- , runSynCirc "sum-arr-BxBxB-l" $ toCcc $ sum @(Arr ((Bool :* Bool) :* Bool)) @Int -- okay

  -- , runSynCirc "foo" $ toCcc $ sum @((->) (Bool :* (Bool :* ()))) @Int -- okay
  -- , runSynCirc "foo" $ toCcc $ sum @(Arr (Bool :* ())) @Int -- okay
  -- , runSynCirc "foo" $ toCcc $ sum @(Arr (Bool :* (Bool :* ()))) @Int -- okay

  -- , runSynCirc "sum-flat-rbin-3" $ toCcc $ sum @(Flat (RBin N3)) @Int -- okay
  -- , runSynCirc "sum-flat-lbin-3" $ toCcc $ sum @(Flat (LBin N3)) @Int -- okay

  -- , runSynCirc "fmap-rbin-4" $ toCcc $ fmap @(Flat (LBin N4)) not -- 

  -- , runSynCirc "add-int" $ toCcc $ (+) @Int -- fine

  -- , runSynCirc "add-int" $ toCcc $ (+) @Integer -- 

  -- , runSynCirc "foo" $ toCcc $ toFin @Bool -- works

  -- , runSyn $ toCcc $ unFin @Bool -- breaks

  -- , runSyn $ toCcc $ finVal @2 -- 

  -- , runSyn $ toCcc $ unFin @() -- works

  -- , runSyn{-Circ "foo"-} $ toCcc $ sum @((->) (Finite 5)) @Int -- breaks

  -- , runSynCirc "foo" $ toCcc $ sum @((->) (Bool :* (Bool :* ()))) @Int -- works

  -- , runCirc "foo" $ toCcc $ fmap @(Arr (Bool :* (Bool :* ()))) not -- works

  -- , runCirc "foo" $ toCcc $ fmap @(Flat (RBin N6)) not -- works

  -- , runCirc "foo" $ toCcc $ sum @(Arr (Bool :* (Bool :* ()))) @Int -- nope

  -- , runCirc "foo" $ toCcc $ fmap @(Arr (Bool :* (Bool :* ()))) not -- works with Syn but not Circ

  -- , runSynCirc "sum-rbin-3" $ toCcc $ sum @(RBin N3) @Int

  -- , runSyn{-Circ "sum-flat-rbin-1"-} $ toCcc $ sum @(Flat (RBin N1)) @Int -- ?

  -- , runSynCirc "packFinite" $ toCcc $ packFinite @5 -- fail (missing INLINE)

  -- , runSynCirc "packFiniteM" $ toCcc $ packFiniteM @5 @Maybe -- okay 

  -- , runSynCirc "vecIndexDef" $ toCcc $ vecIndexDef @5 @R -- okay

  -- , runSynCirc "finite" $ toCcc $ Finite @5 -- okay

  -- , runSynCirc "add-integer" $ toCcc $ uncurry ((+) @Integer) -- fine

  -- , runSynCirc "sum1" $ toCcc $ sum @Par1 @R -- ??

  -- , runSynCirc "sum2" $ toCcc $ sum @Pair @R -- ??

  -- , runSynCirc "sumV" $ toCcc $ sum @(Vector 5) @R -- ??

  -- , runSynCirc "sumAV" $ toCcc $ sumA @(Vector 5) @R -- ??

  -- , runSynCirc "foo" $ toCcc $ andDerR $ \ () -> zero @((Vector 3 :.: Bump (Vector 2)) R) -- fail

  -- , runSynCirc "foo" $ toCcc $ andDerR $ \ () -> zero @((Vector 3 :.: Vector 2) R) -- o2 fail

  -- , runSynCirc "foo" $ toCcc $ \ () -> zero @((Vector 3 :.: Vector 2) R) -- o3 fail

  -- , runSynCirc "foo" $ toCcc $ \ () -> zero @((Vector 3 :.: Par1) R) -- o4 fail; o7, o1 (without vector-sized mod)


  -- , runSynCirc "foo" $ toCcc $ point @(Vector 3 :.: Par1) @R -- o6 okay


  -- , runSynCirc "foo" $ toCcc $ \ () -> zero @((Par1 :.: Par1) R) -- okay
  -- , runSynCirc "foo" $ toCcc $ \ () -> zero @(Vector 3 R) -- okay
  -- , runSynCirc "foo" $ toCcc $ \ () -> zero @((Par1 :.: Par1) R) -- okay
  -- , runSynCirc "foo" $ toCcc $ point @(Vector 3 :.: Vector 2) @R -- okay
  -- , runSynCirc "foo" $ toCcc $ andDerR $ \ () -> zero @(Vector 3 R) -- okay
  -- , runSynCirc "foo" $ toCcc $ (^+^) @(Vector 3 R) -- okay
  -- , runSynCirc "foo" $ toCcc $ andDerR $ id @(Vector 2 R) -- okay
  -- , runSynCirc "foo" $ toCcc $ andDerR $ id @((Vector 3 :.: Bump (Vector 2)) R) -- okay

  -- , runSynCirc "step-lr1" $ toCcc $ D.step (lr1 @(Vector 2) @(Vector 3)) 0.01

  -- , runSynCirc "errGrad-lr1" $ toCcc $ D.errGrad (lr1 @(Vector 2) @(Vector 3)) -- fails with cast confusion

  -- , runSynCirc "step-lr2" $ toCcc $ D.step (lr2 @(Vector 2) @(Vector 3) @(Vector 5)) 0.01

    -- , runSynCirc "fmap" $ toCcc $ fmap @(Vector 7) not

    -- , runSynCirc "constV" $ toCcc $ \ () -> pure 1 :: Vector 7 Int

    -- , runSynCirc "pointV" $ toCcc $ point @(Vector 7) @Bool

    -- , runSynCirc "addV" $ toCcc $ (^+^) @(Vector 7 R)

    -- , runSynCirc "zeroV" $ toCcc $ \ () -> zero @(Vector 7 R)

    -- , runSynCirc "addR" $ toCcc $ (^+^) @R
   
    -- , runSyn $ toCcc $ \ () -> finite @2 (nat @1) -- okay

    -- , runSyn $ toCcc $ \ (i :: Finite 2) -> finite @2 (nat @2 - 1) -- okay

    -- , runSyn $ toCcc $ \ (i :: Finite 2) -> finite (nat @2 - 1) - i -- okay

    -- , runSyn $ toCcc $ reverseFinite @5  -- Fine

    -- , runSynCirc "reverseFinite" $ toCcc $ reverseFinite @5

    -- , runSynCirc "reverseF-pair" $ toCcc $ reverseF @Pair @Int

    -- , runSynCirc "reverseF-vec" $ toCcc $ reverseF @(Vector 5) @Int

    -- , runSynCirc "reverseFin-Bool-802" $ toCcc $ isoFwd (reverseFinIso @Bool)

    -- , runSynCirc "reverseFin-vec" $ toCcc $ isoFwd (reverseFinIso @(A.Finite 5))

    -- , runSynCirc "reverseFin-Bool-cheat" $ toCcc $ unFin @Bool . (1 -) . toFin @Bool

    -- -- https://github.com/conal/concat/issues/49
    -- -- , putStrLn $ render (toCcc (\f g x -> f (g (x))))
    -- , putStrLn $ render (toCcc (\ (f :: Int -> Bool) (g :: Bool -> Int) x -> f (g (x))))

  -- Circuit graphs
  , runSynCirc "add"         $ toCcc $ (+) @R
  , runSynCirc "add-uncurry" $ toCcc $ uncurry ((+) @R)
  , runSynCirc "dup"         $ toCcc $ A.dup @(->) @R
  , runSynCirc "fst"         $ toCcc $ fst @R @R
  , runSynCirc "twice"       $ toCcc $ twice @R
  , runSynCirc "sqr"         $ toCcc $ sqr @R
  , runSynCirc "complex-mul" $ toCcc $ uncurry ((*) @C)
  , runSynCirc "magSqr"      $ toCcc $ magSqr @R
  , runSynCirc "cosSinProd"  $ toCcc $ cosSinProd @R
  , runSynCirc "xp3y"        $ toCcc $ \ (x,y) -> x + 3 * y :: R
  , runSynCirc "horner"      $ toCcc $ horner @R [1,3,5]
  , runSynCirc "cos-2xx"     $ toCcc $ \ x -> cos (2 * x * x) :: R

  -- -- Automatic differentiation
  -- , runSynCircDers "add"     $ uncurry ((+) @R)
  -- , runSynCircDers "fst"     $ fst @R @R
  -- , runSynCircDers "twice"   $ twice @R
  -- , runSynCircDers "sqr"     $ sqr @R
  -- , runSynCircDers "sin"     $ sin @R
  -- , runSynCircDers "cos"     $ cos @R
  -- , runSynCircDers "magSqr"  $ magSqr  @R
  -- , runSynCircDers "cos-2x"  $ \ x -> cos (2 * x) :: R
  -- , runSynCircDers "cos-2xx" $ \ x -> cos (2 * x * x) :: R
  -- , runSynCircDers "cos-xpy" $ \ (x,y) -> cos (x + y) :: R
  -- , runSynCircDers "cos-xpytz" $ \ (x,y,z) -> cos (x + y * z) :: R

  -- , runSynCirc "cos-xpy-adr-802" $ toCcc $ andGradR $ \ (x,y) -> cos (x + y) :: R

  -- , runSynCirc "sqr-adr-802" $ toCcc $ andGradR $ sqr @R

  -- , runSynCirc "magSqr-adr"  $ toCcc $ andDerR $ magSqr  @R
  -- , runSynCirc "cosSinProd-adr"  $ toCcc $ andDerR $ cosSinProd @R
  -- , runSynCirc "cosSinProd-gradr"  $ toCcc $ andGrad2R $ cosSinProd @R

  -- , runSynCirc "cosSinProd-adf" $ toCcc $ andDerF $ cosSinProd @R
  -- , runSynCirc "cosSinProd-adr" $ toCcc $ andDerR $ cosSinProd @R

  -- , runCirc "affRelu"         $ toCcc $                affRelu @(Vector 2) @(Vector 3) @R
  -- , runCirc "affRelu-err"     $ toCcc $ errSqrSampled (affRelu @(Vector 2) @(Vector 3) @R)
  -- , runCirc "affRelu-errGrad" $ toCcc $ errGrad (affRelu @(Vector 2) @(Vector 3) @R)

  -- , runCirc "affRelu2"         $ toCcc $                lr2 @(Vector 5) @(Vector 3) @(Vector 2)
  -- , runCirc "affRelu2-err"     $ toCcc $ errSqrSampled (lr2 @(Vector 5) @(Vector 3) @(Vector 2))
  -- , runCirc "affRelu2-errGrad" $ toCcc $ errGrad       (lr2 @(Vector 5) @(Vector 3) @(Vector 2))

  -- , runCirc "affRelu3"         $ toCcc $                lr3 @(Vector 7) @(Vector 5) @(Vector 3) @(Vector 2)
  -- , runCirc "affRelu3-err"     $ toCcc $ errSqrSampled (lr3 @(Vector 7) @(Vector 5) @(Vector 3) @(Vector 2))
  -- , runCirc "affRelu3-errGrad" $ toCcc $ errGrad       (lr3 @(Vector 7) @(Vector 5) @(Vector 3) @(Vector 2))

  ]

data P = P R R

instance HasRep P where
  type Rep P = R :* R
  repr (P x y) = (x,y)
  abst (x,y) = P x y

instance Additive P where
  zero = P zero zero
  P a b ^+^ P c d = P (a+c) (b+d)

#if 0

-- | Convert an 'Integer' into a 'Finite', returning 'Nothing' if the input is out of bounds.
-- This version has an INLINE pragma.
packFiniteM :: forall n m. (KnownNat n, Monad m) => Integer -> m (Finite n)
packFiniteM x | 0 <= x && x < natValAt @n = return (Finite x)
              | otherwise                 = fail "packFiniteM: bad index"
{-# INLINE packFiniteM #-}

-- Index a sized vector with an integer, given a default
vecIndexDef :: KnownNat n => a -> Vector n a -> Integer -> a
vecIndexDef def v i = maybe def (FR.index v) (packFiniteM i)
{-# INLINE vecIndexDef #-}

#endif

-- foo :: Stack Syn Int Int
-- foo = toCcc $ A.addC . (A.id A.&&& A.id) --

-- foo = toCcc $ A.addC . (A.id A.&&& A.id) --
-- foo = reveal $ toCcc $ A.addC . (A.id A.&&& A.id) -- 
-- foo = toCcc $ \ x -> x + x
-- foo = toCcc $ A.reveal (A.addC . (A.id A.&&& A.id))

-- z2 :: Syn ((Int :* Bool) :* z) ((Int :* Bool) :* z)
-- z2 = S.z2

-- z1 :: Int -> Int
-- z1 = A.addC A.. (A.id A.&&& A.id)

-- z2 :: Stack Syn Int Int
-- z2 = A.addC A.. (A.id A.&&& A.id)

-- z2' :: Stack Syn Int Int
-- z2' = A.reveal (A.addC A.. (A.id A.&&& A.id))

-- z3 :: Stack Syn Int Int
-- z3 = toCcc (\ x -> x + x)

-- z4 :: Stack Syn Int Int
-- z4 = toCcc' (\ x -> x + x)

-- z5 :: Syn (Int :* ()) (Int :* ())
-- z5 = S.unStack (toCcc' (\ x -> x + x))

-- z5 :: Syn (Int :* ()) (Int :* ())
-- z5 = S.unStack (toCcc (\ x -> x + x))

-- z2' :: Syn (Int :* ()) (Int :* ())
-- z2' = unStack z2

-- z3 :: Syn (Int :* ()) (Int :* ())
-- z3 = toCcc $ \ x -> x + x

-- z3' :: Syn (Int :* ()) (Int :* ())
-- z3' = unStack z3


-- z5 :: Stack Syn Int Int
-- z5 = A.negateC A.. A.negateC

-- z5' :: Stack Syn Int Int
-- z5' = A.reveal (A.negateC A.. A.negateC)

-- z6 :: Stack Syn (Int :* Int) (Int :* Int)
-- z6 = A.negateC A.*** A.negateC

-- z6' :: Stack Syn (Int :* Int) (Int :* Int)
-- z6' = A.reveal (A.negateC A.*** A.negateC)

-- z6'' :: Stack Syn (Int :* Int) (Int :* Int)
-- z6'' = C.negateC C.*** C.negateC

-- z7 :: Stack Syn (Int :* Int) (Int :* Int)
-- z7 = C.negateC `C.crossSecondFirst` C.negateC

-- z7' :: Stack Syn (Int :* Int) (Int :* Int)
-- z7' = C.negateC `A.crossSecondFirst` C.negateC

-- z8 :: Stack Syn (Int :* Int) (Int :* Int)
-- z8 = C.negateC C.*** C.negateC

-- z8' :: Stack Syn (Int :* Int) (Int :* Int)
-- z8' = C.negateC `S.cross` C.negateC

-- z8'' :: Stack Syn (Int :* Int) (Int :* Int)
-- z8'' = C.negateC `C.crossSecondFirst` C.negateC

-- z8' :: Stack Syn (Int :* Int) (Int :* Int)
-- z8' = C.negateC A.*** C.negateC

-- z9 :: Stack Syn (Int :* Int) (Int :* Int)
-- z9 = C.negateC `S.cross` C.negateC
