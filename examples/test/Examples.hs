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
-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}
-- {-# OPTIONS_GHC -dverbose-core2core #-}

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}
-- {-# OPTIONS_GHC -ddump-rules #-}

-- Does this flag make any difference?
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

-- Tweak simpl-tick-factor from default of 100
-- {-# OPTIONS_GHC -fsimpl-tick-factor=2800 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=500 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=250 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=25  #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=5  #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
-- {-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

-- {-# OPTIONS_GHC -ddump-tc-trace #-}

-- {-# OPTIONS_GHC -dsuppress-all #-}

-- Experiments
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

import Prelude hiding (zip,zipWith) -- (id,(.),curry,uncurry)
import qualified Prelude as P

import Data.Monoid (Sum(..))
import Data.Foldable (fold)
import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import Data.List (unfoldr)  -- TEMP
import Data.Complex (Complex)
import GHC.Exts (inline)
import GHC.Float (int2Double)

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed
import Data.Key
import Data.Distributive
import Data.Functor.Rep
import Data.Finite
import Data.Vector.Sized (Vector)
import qualified Data.Vector.Sized as VS

import ConCat.Misc
  ((:*),(:+),R,sqr,magSqr,Unop,Binop,inNew,inNew2,Yes1,oops,type (&+&),PseudoFun(..))
import ConCat.Incremental (andInc,inc)
import ConCat.AD
import ConCat.ADFun hiding (D)
import ConCat.Free.VectorSpace (HasV(..),distSqr)
import ConCat.GradientDescent
import ConCat.Interval
import ConCat.Syntactic (Syn,render)
import ConCat.Circuit (GenBuses,(:>))
import qualified ConCat.RunCircuit as RC
import qualified ConCat.AltCat as A
-- import ConCat.AltCat
import ConCat.AltCat
  (toCcc,toCcc',unCcc,unCcc',reveal,conceal,(:**:)(..),Ok,Ok2,U2,equal)
import ConCat.AltAggregate ()
import qualified ConCat.AltAggregate as A
import qualified ConCat.Rep
import ConCat.Rebox () -- necessary for reboxing rules to fire
import ConCat.Nat
import ConCat.Shaped
import ConCat.Scan
import ConCat.FFT
import ConCat.Free.LinearRow -- (L,OkLM,linearL)
import ConCat.LC

-- Experimental
import qualified ConCat.Inline.SampleMethods as I

import qualified ConCat.Regress as R
import ConCat.Free.Affine
import ConCat.Choice
import ConCat.RegressChoice

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

import Control.Newtype (Newtype(..))

-- Experiments
import GHC.Exts (Coercible,coerce)

-- default (Int, Double)

type C = Complex R

main :: IO ()
main = sequence_
  [ putChar '\n' -- return ()

  -- Circuit graphs
  , runSynCirc "twice"       $ toCcc $ twice @R
  , runSynCirc "complex-mul" $ toCcc $ uncurry ((*) @C)
  , runSynCirc "magSqr"      $ toCcc $ magSqr @R
  , runSynCirc "cosSin-xy"   $ toCcc $ cosSinProd @R
  , runSynCirc "xp3y"        $ toCcc $ \ (x,y) -> x + 3 * y :: R
  , runSynCirc "horner"      $ toCcc $ horner @R [1,3,5]
  , runSynCirc "cos-2xx"     $ toCcc $ \ x -> cos (2 * x * x) :: R

  -- , runSynCirc "log" $ toCcc $ log @R
  -- , runSynCirc "pow" $ toCcc $ uncurry ((**) @R)

  -- -- Play with the "cat equal" trick.
  -- , runSyn $ toCcc $ (==) @Int
  -- , runSyn $ toCcc $ uncurry ((==) @Int)

  -- , runCirc "equal-pair-b" $ toCcc $ (==) @(R :* Int)

  -- , runCirc "equal-pair-uncurry-b" $ toCcc $ uncurry ((==) @(R :* Int))

  -- , runSynCirc "equal-pair-a" $ toCcc $ uncurry ((==) @(Bool :* Int))

  -- , runSynCirc "equal-pair-b" $ toCcc $ uncurry ((==) @(Int :* R))

  -- , runSynCirc "equal-pair-d" $ toCcc $ toCcc $ uncurry ((==) @(Int :* R))

  -- , runSyn{-Circ "equal-pair-b"-} $ toCcc $ uncurry ((==) @(Bool :* Int))

  -- , runSynCirc "add" $ toCcc $ (+) @Integer

  -- -- Try sized vector operations directly.
  -- , runSyn $ toCcc $ VS.sum @R @4  -- fail

  -- Choice

  -- , onChoice @GenBuses (runCirc "choice-add" . toCcc) -- okay
  --     (toCcc (choose @GenBuses ((+) @R)))

  -- -- This one fails with Ok (:>) vs GenBuses preventing toCcc'/unCcc'
  -- , onChoice @(Ok (:>)) (runCirc "choice-add" . toCcc)
  --     (toCcc (choose @(Ok (:>)) ((+) @R)))

  -- , onChoice @OkLC (runCirc "choice-add" . toCcc) -- okay
  --     (toCcc (choose @OkLC ((+) @R)))

  -- -- This one breaks. Seems to be GenBuses vs Ok (:>) in toCcc'/unCcc'.
  -- -- Bug in GHC's handling of rewrite rules?
  -- , onChoice @(Ok (:>)) (runCirc "choice-add" . toCcc)  -- fail
  --     (toCcc (choose @(Ok (:>)) ((+) @R)))

  -- , onChoice @GenBuses (runCirc "choice-foo" . toCcc)
  --     (toCcc (choose @GenBuses (\ b x -> x + b :: R))) 

  -- , onChoice @(Ok (:>)) (runCirc "choice-foo" . toCcc)
  --     (toCcc (choose @(Ok (:>)) (\ b x -> x + b :: R))) 

  -- , onChoice @GenBuses (runCirc "choice-line" . toCcc)
  --     (toCcc (choose @GenBuses (\ (m,b) x -> m * x + b :: R)))

  -- , onChoice @GenBuses (runCirc "choice-line" . toCcc)
  --     (toCcc (choose @GenBuses line))
  -- , onChoice @GenBuses (runCirc "choice-line-lam" . toCcc)  -- fail
  --     (toCcc (\ x -> choose @GenBuses line x))
  -- , onChoice @GenBuses (runCirc "choice-line-2x" . toCcc)
  --     (toCcc (\ x -> choose @GenBuses line (2 * x)))

  -- , onChoice @GenBuses (runCirc "choice-line-lam-2" . toCcc)
  --     (toCcc (\ x -> choose @GenBuses line (choose @GenBuses line x)))
  -- , onChoice @GenBuses (runCirc "choice-line-sin-line-a" . toCcc)
  --     (toCcc (\ x -> choose @GenBuses line (sin (choose @GenBuses line x))))
  -- , onChoice @GenBuses (runCirc "choice-line-sin-line-b" . toCcc)
  --     (toCcc (choose @GenBuses line . sin . choose @GenBuses line))

  -- , onChoice @OkLC (runCirc "choice-line" . toCcc)
  --     (toCcc (choose @OkLC line)) 

  -- , runSynCirc "foo" $ toCcc (step @R line)  -- Loops

  -- , runSynCirc "distSqr-v" $ toCcc $ distSqr @R @(Vector 5)
  -- , runSynCirc "sqErr-vv" $ toCcc $ R.sqErr @R @(Vector 5 R) @(Vector 11 R)
  -- , runCirc "sqErrF-vv" $ toCcc $ R.sqErrF @R @(Vector 5 R) @(Vector 11)


  -- , runSynCirc "zipWith-v" $ toCcc $ zipWith @(Vector 7) (||)


  -- , runSynCirc "foo-der" $ toCcc $
  --     \ (v :: Par1 R) ->
  --       derF (distSqr v)


  -- , runSynCirc "sqErrF-der-pp" $ toCcc $
  --     \ (ab :: Par1 R :* Par1 R) ->
  --       derF (R.sqErrF @R ab . applyA @R)


  -- , runSynCirc "sqErr-der-pp" $ toCcc $
  --     \ (ab :: Par1 R :* Par1 R) ->
  --       derF (R.sqErr @R ab . applyA @R)


  -- , runSynCirc "sqErr-der-vv" $ toCcc $
  --     \ (ab :: Vector 5 R :* Vector 11 R) ->
  --       derF (R.sqErr @R ab . applyA @R)

  -- , runSynCirc "sqErr-vv-c" $ toCcc $
  --     \ (ab :: Vector 5 R :* Vector 11 R) ->
  --       (R.sqErr @R ab . applyA @R)

  -- , runSynCirc "applyA-vv" $ toCcc $
  --       applyA @R @(Vector 5 R) @(Vector 11 R)

  -- -- 50 sec with AD; 11 sec with ADFun.
  -- , onChoice @OkLFC (\ f -> runCirc "regress-line" (toCcc (step @R f)))
  --     (toCcc (choose @OkLFC line))

  -- , runCirc "regress-line-d" $ toCcc $ \ ab p -> sqErr @R ab (line p) -- ok

  -- , onChoice @OkLC (runCirc "choice-add" . toCcc)  -- fine
  --     (toCcc (choose @OkLC ((+) @R)))

  -- , onChoice @GenBuses (runCirc "choice-line" . toCcc)  -- ok (base)
  --     (toCcc (choose @GenBuses line))

  -- , onChoice @OkLC (\ f -> runCirc "regress-line-a" --
  --                    (toCcc (\ ab p -> sqErr @R ab (f p))))
  --     (toCcc (choose @OkLC line))

  -- -- 48 sec
  -- , onChoice @OkLC (\ f -> runCirc "regress-line-b" $ toCcc $
  --                     \ ab -> negateV (gradient (sqErr @R ab . f)))
  --     (toCcc (choose @OkLC line))

  -- -- wrong constraint. takes forever?
  -- , onChoice @OkLC (\ f -> runCirc "bar3" $ toCcc $
  --                     \ ab -> derF (sqErr @R ab . f))
  --     (toCcc (choose @OkLC line))

  -- -- 12 sec
  -- , onChoice @OkLFC (\ f -> runCirc "regress-line-df" $ toCcc $  -- ok 
  --                     \ ab -> derF (negate . sqErr @R ab . f))
  --     (toCcc (choose @OkLFC line))

  -- -- 12 sec
  -- , onChoice @OkLFC (\ f -> runCirc "regress-line-gf" $ toCcc $  -- ok 
  --                     \ ab -> gradF @R (negate . sqErr ab . f))
  --     (toCcc (choose @OkLFC line))

  -- , oops "Hrmph" (toCcc (choose @GenBuses (||)) :: Choice GenBuses Bool Bool)

  -- Integer

  -- , runSynCirc "eq-integer"       $ toCcc ((==) @Integer)
  -- , runSynCirc "ne-integer"       $ toCcc ((/=) @Integer)
  -- , runSynCirc "le-integer"       $ toCcc ((<=) @Integer)
  -- , runSynCirc "ne-integer-b"     $ toCcc (\ (x :: Integer, y) -> not (x == y))
  -- , runSynCirc "ge-integer-b"     $ toCcc (\ (x :: Integer, y) -> not (x < y))
  -- , runSynCirc "plus-integer"     $ toCcc ((+) @Integer)
  -- , runSynCirc "plus-mul-integer" $ toCcc (\ (x :: Integer, y) -> x * (x + y))

  -- , runSynCirc "fmap-not-v" $ toCcc $ (fmap not :: Unop (Vector 2 Bool))
  -- , runCirc "point-v"       $ toCcc $ (point :: Bool -> Vector 8 Bool)
  -- , runCirc "sum-v"         $ toCcc $ (sum :: Vector 8 Int -> Int)
  -- , runCirc "sum-point-v"   $ toCcc $ (sum . (point :: Int -> Vector 8 Int))
  -- , runSynCirc "tabulate-v" $ toCcc (tabulate :: (Finite 8 -> Bool) -> Vector 8 Bool)

  -- , runCirc "distribute" $ toCcc (distribute @Pair @Pair @R)

  -- , runSynCirc "distribute" $ toCcc (distribute @(Vector 4) @(U1 :*: Par1) @R)

  -- , runSynCirc "distribute" $ toCcc (distribute :: (Vector 4) ((Par1 :*: Par1) R) -> ((Par1 :*: Par1)) (Vector 4 R))  -- ok

  -- , runSynCirc "foo" $ toCcc $ id @((Par1 :*: Par1) (Vector 4 R)) -- hangs genBuses

  -- , runSynCirc "foo" $ toCcc $ id @(Vector 4 Bool :* Bool)

  -- , runSynCirc "distribute" $ toCcc (A.distributeC :: ((Par1 :*: Par1)) (Vector 4 R) -> (Vector 4) ((Par1 :*: Par1) R))

  -- , runSynCirc "distribute-p-v" $ toCcc (distribute @(Vector 4) @Pair @R)
  -- , runSynCirc "distribute-v-p" $ toCcc (distribute @Pair @(Vector 4) @R)

  -- , runSynCirc "fmap-idL-v" $ toCcc (\ (h :: Vector 8 R -> Vector 8 R) -> h <$> idL)

  -- , runSynCirc "linearF-v" $ toCcc $ linearF @R @(Vector 8) @Par1

  -- , runSynCirc "linear-v-1" $ toCcc $ linear @R @(Vector 8 R) @R
  -- , runSynCirc "linear-v-2" $ toCcc $ linear @R @(Vector 8 R) @(R :* R)
  -- , runSynCirc "linear-1-v" $ toCcc $ linear @R @R @(Vector 8 R)
  -- , runSynCirc "linear-2-v" $ toCcc $ linear @R @(R :* R) @(Vector 8 R)

  -- , runSynCirc "sum-v-adf" $ toCcc $ andDerF (sumC :: Vector 8 R -> R)

  -- , runCirc "sum-v-adfl" $ toCcc $ andDerFL @R (sumC :: Vector 8 R -> R)

  -- , runCirc "foo" $ toCcc $ \ () -> dualV (\ (x,y,z) -> x + y + z :: R) -- fail

  -- , runCirc "foo" $ toCcc $ \ () -> dualV (sumC :: Pair R -> R) -- ok

  -- , runCirc "foo" $ toCcc $ unV @R @(Vector 2 R)

  -- , runCirc "foo" $ toCcc $ \ () -> dualV4 (sumC :: Vector Bool R -> R) -- fail

  -- , runCirc "foo" $ toCcc $ \ () -> diag @(Vector Bool) @R  -- OK

  -- , runCirc "foo" $ toCcc $ fmapC @(->) @(Vector Bool) @R @R -- OK

  -- , runCirc "foo" $ toCcc $ (sumC :: Vector Bool R -> R) -- OK

  -- , runCirc "foo" $ toCcc $ (dualV @R @(Vector Bool R)) --

  -- , runSyn $ toCcc $ \ () -> dualV (sumC :: Vector Bool R -> R) -- Ok

  -- , runCirc "dual-sum-pair" $ toCcc $ \ () -> dualV (sumC :: Pair R -> R)

  -- , runCirc "dual-sum-par1" $ toCcc $ \ () -> dualV (sumC :: Par1 R -> R)

  -- , runCirc "dual-sum-arr" $ toCcc $ \ () -> dualV (sumC :: Vector Bool R -> R)

  -- , runCirc "dual-sum-arr-unit" $ toCcc $ \ () -> dualV (sumC :: Vector () R -> R)

  -- , runCirc "foo" $ toCcc $ \ () -> dualV (sumC :: Vector Bool R -> R)

  -- , runCirc "sum-arr-v3-adf" $ toCcc $ andDerF (sumC :: Vector (RVec N3 Bool) R -> R)

  -- , runSynCirc "sum-arr-v3-adfl" $ toCcc $ andDerFL' @R (sumC :: Vector (RVec N3 Bool) R -> R)

  -- , runSynCirc "fmapC-id-arr" $ toCcc $ (fmapC id :: Unop (Vector Bool R))

  -- , runSynCirc "fmap-not" $ toCcc $ (fmapC not :: Unop (Pair Bool))

  -- , runSyn $ toCcc $ sqr @R

  -- , runSyn $ toCcc $ (fmapC sqr :: Unop (Pair R))

  -- , runSynCirc "fmap-par1-sqr-adf"  $ toCcc $ andDerF (fmap  sqr :: Unop (Par1 R))

  -- , runSynCirc "fmapC-par1-sqr-adf" $ toCcc $ andDerF (fmapC sqr :: Unop (Par1 R))

  -- , runSyn{-Circ "fmapC-pair-sqr-adf"-} $ toCcc $ andDerF (fmapC sqr :: Unop (Pair R))

  -- , runSynCirc "fmapC-pair-sqr-adf" $ toCcc $ andDerF (fmapC sqr :: Unop (Pair R))

  -- , runSynCirc "fmapC-pair-sqr-adf" $ toCcc $ andDerF (fmapC sqr :: Unop (Pair R))

  -- , runSyn $ toCcc $ andDer @R (fmapC sqr :: Unop (Pair R))

  -- -- Circuit graphs on trees etc
  -- , runSynCirc "sum-pair"   $ toCcc $ sum   @Pair      @Int
  -- , runSynCirc "sum-rb4"    $ toCcc $ sum   @(RBin N4) @Int
  -- , runSynCirc "lsums-pair" $ toCcc $ lsums @Pair      @Int
  -- , runSynCirc "lsums-rb2"  $ toCcc $ lsums @(RBin N2) @Int
  -- , runSynCirc "lsums-rb3"  $ toCcc $ lsums @(RBin N3) @Int
  -- , runSynCirc "lsums-rb4"  $ toCcc $ lsums @(RBin N4) @Int

  -- , runCirc "fft-pair" $ toCcc $ fft @Pair @Double
  -- , runCirc "fft-rb1"  $ toCcc $ fft @(RBin N1) @Double
  -- , runCirc "fft-rb2"  $ toCcc $ fft @(RBin N2) @Double
  -- , runCirc "fft-rb3"  $ toCcc $ fft @(RBin N3) @Double
  -- , runCirc "fft-rb4"  $ toCcc $ fft @(RBin N4) @Double

  -- , runCirc "foo" $ toCcc $ \ ( fc :: ( (Pair :.: Pair) (Complex Double) )) -> fft fc

  -- -- Interval analysis
  -- , runSynCirc "add-iv"    $ toCcc $ ivFun $ uncurry ((+) @Int)
  -- , runSynCirc "mul-iv"    $ toCcc $ ivFun $ uncurry ((*) @Int)
  -- , runSynCirc "thrice-iv" $ toCcc $ ivFun $ \ x -> 3 * x :: Int
  -- , runSynCirc "sqr-iv"    $ toCcc $ ivFun $ sqr @Int
  -- , runSynCirc "magSqr-iv" $ toCcc $ ivFun $ magSqr @Int
  -- , runSynCirc "xp3y-iv"   $ toCcc $ ivFun $ \ ((x,y) :: R2) -> x + 3 * y
  -- , runSynCirc "xyp3-iv"   $ toCcc $ ivFun $ \ (x,y) -> x * y + 3 :: R
  -- , runSynCirc "horner-iv" $ toCcc $ ivFun $ horner @R [1,3,5]

  -- -- Automatic differentiation
  -- , runSynCirc "sin-ad"        $ toCcc $ andDer @R @R $ sin    @R
  -- , runSynCirc "cos-ad"        $ toCcc $ andDer @R @R $ cos    @R
  -- , runSynCirc "twice-ad"      $ toCcc $ andDer @R @R $ twice  @R
  -- , runSynCirc "sqr-ad"        $ toCcc $ andDer @R $ sqr    @R
  -- , runSynCirc "magSqr-ad"     $ toCcc $ andDer @R $ magSqr @R
  -- , runSynCirc "cos-2x-ad"     $ toCcc $ andDer @R $ \ x -> cos (2 * x) :: R
  -- , runSynCirc "cos-2xx-ad"    $ toCcc $ andDer @R $ \ x -> cos (2 * x * x) :: R
  -- , runSynCirc "cos-xpy-ad"    $ toCcc $ andDer @R $ \ (x,y) -> cos (x + y) :: R
  -- , runSynCirc "cosSinProd-ad" $ toCcc $ andDer @R $ cosSinProd @R

  -- Fails (I think)
  -- , runSynCirc "sum-pair-ad"     $ toCcc $ andDer @R $ sum @Pair @R
  -- , runSynCirc "product-pair-ad" $ toCcc $ andDer @R $ product @Pair @R

  -- , runSynCirc "sum-2-ad"$ toCcc $ andDer @R $ \ (a,b) -> a+b :: R

  -- , runSynCirc "sum-3-ad"$ toCcc $ andDer @R $ \ (a,b,c) -> a+b+c :: R

  -- , runSynCirc "product-3-ad"$ toCcc $ andDer @R $ \ (a,b,c) -> a*b*c :: R

  -- , runSynCirc "product-4-ad"$ toCcc $ andDer @R $ \ (a,b,c,d) -> a*b*c*d :: R

  -- , runSynCirc "sum-4-ad"$ toCcc $ andDer @R $ \ (a,b,c,d) -> a+b+c+d :: R

  -- , runSynCirc "sum-rb2-ad"$ toCcc $ andDer @R $ sum @(RBin N2) @R

  -- -- Dies with "Oops --- toCcc called!", without running the plugin.
  -- , print $ andDer @R sin (1 :: R)

  -- -- Linear
  -- , runSynCirc "linear-r-r"   $ toCcc $ linear @R @R @R
  -- , runSynCirc "linear-r2-r"  $ toCcc $ linear @R @(R :* R) @R
  -- , runSynCirc "linear-r-r2"  $ toCcc $ linear @R @R @(R :* R)
  -- , runSynCirc "linear-r2-r2" $ toCcc $ linear @R @(R :* R) @(R :* R)

  -- , runCirc "equal-Int" $ toCcc $ (==) @Int
  -- , runCirc "equal-sum" $ toCcc $ (==) @(() :+ ())

  -- , runSynCirc "diag-2" $ toCcc $ diag @(Par1 :*: Par1) @R

  -- , runCirc "idL-2" $ toCcc (\ () -> idL @(Par1 :*: Par1) @R) -- fail
  -- , runSynCirc "tabulate2" $ toCcc $ tabulateC @(->) @(Par1 :*: Par1) @R  -- fail

  -- , runCirc "idL-v" $ toCcc (\ () -> idL @(Vector 8) @R) -- ok

  -- , runCirc "equal-v" $ toCcc $ (==) @(Vector 5 Int)

  -- , runSynCirc "linear-v-r" $ toCcc $ linear @R @(Vector 4 R) @R

  -- , runSynCirc "distribute-1-4" $ toCcc $ distributeC @(->) @(V R R) @(V R (Vector 4 R)) @R

  -- , runSynCirc "distribute-4-1" $ toCcc $ distributeC @(->) @(V R (Vector 4 R)) @(V R R) @R

  -- , runSynCirc "distribute-1-4" $ toCcc $ (distributeC :: V R R (V R (Vector 4 R) R) -> V R (Vector 4 R) (V R R R))

  -- -- Automatic differentiation with ADFun:
  -- , runSynCirc "sin-adf"        $ toCcc $ andDerF $ sin @R
  -- , runSynCirc "cos-adf"        $ toCcc $ andDerF $ cos @R
  -- , runSynCirc "twice-adf"      $ toCcc $ andDerF $ twice @R
  -- , runSynCirc "sqr-adf"        $ toCcc $ andDerF $ sqr @R
  -- , runSynCirc "magSqr-adf"     $ toCcc $ andDerF $ magSqr  @R
  -- , runSynCirc "cos-2x-adf"     $ toCcc $ andDerF $ \ x -> cos (2 * x) :: R
  -- , runSynCirc "cos-2xx-adf"    $ toCcc $ andDerF $ \ x -> cos (2 * x * x) :: R
  -- , runSynCirc "cos-xpy-adf"    $ toCcc $ andDerF $ \ (x,y) -> cos (x + y) :: R
  -- , runSynCirc "cosSinProd-adf" $ toCcc $ andDerF $ cosSinProd @R

  -- , runSynCirc "product-4-adf"$ toCcc $ andDerF $ \ (a,b,c,d) -> a*b*c*d :: R

  -- , runSynCirc "sum-rb3-adf"$ toCcc $ andDerF $ sum @(RBin N3) @R

  -- , runSynCirc "product-rb3-adf"$ toCcc $ andDerF $ product @(RBin N3) @R

  -- -- Automatic differentiation with ADFun + linear
  -- , runSynCirc "sin-adfl"        $ toCcc $ andDerFL @R $ sin @R
  -- , runSynCirc "cos-adfl"        $ toCcc $ andDerFL @R $ cos @R
  -- , runSynCirc "sqr-adfl"        $ toCcc $ andDerFL @R $ sqr @R
  -- , runSynCirc "magSqr-adfl"     $ toCcc $ andDerFL @R $ magSqr @R -- breaks
  -- , runSynCirc "cos-2x-adfl"     $ toCcc $ andDerFL @R $ \ x -> cos (2 * x) :: R
  -- , runSynCirc "cos-2xx-adfl"    $ toCcc $ andDerFL @R $ \ x -> cos (2 * x * x) :: R
  -- , runSynCirc "cos-xpy-adfl"    $ toCcc $ andDerFL @R $ \ (x,y) -> cos (x + y) :: R
  -- , runSynCirc "cosSinProd-adfl" $ toCcc $ andDerFL @R $ cosSinProd @R


  -- , runSynCirc "product-4-adfl"$ toCcc $ andDerFL @R $ \ (a,b,c,d) -> a*b*c*d :: R

  -- , runSynCirc "product-rb3-adf"$ toCcc $ andDerF $ product @(RBin N3) @R

  -- , runSynCirc "product-rb3-adfl"$ toCcc $ andDerFL @R $ product @(RBin N3) @R

  -- , runSyn $ toCcc $ andDerFL @R $ product @(RBin N4) @R

  -- , runSyn $ toCcc $ andDerF $ product @(RBin N4) @R

  -- -- (0.8414709848078965,[[0.5403023058681398]]), i.e., (sin 1, [[cos 1]]),
  -- -- where the "[[ ]]" is matrix-style presentation of the underlying
  -- -- linear map.
  -- , runPrint 1     $ andDer @R $ sin @R
  -- , runPrint (1,1) $ andDer @R $ \ (x,y) -> cos (x + y) :: R
  -- , runPrint (1,1) $ andDer @R $ cosSinProd @R

  -- , runPrint 1     $ gradient' $ toCcc $ sin @R
  -- , runPrint (1,1) $ gradient' $ toCcc $ \ (x,y) -> cos (x + y) :: R

  -- , runChase 1 $ gradient' $ toCcc $ sin @R -- 1.5707963267948966

  -- , runCircChase "sin-grad" 1 $ toCcc $ gradient $ sin @R -- 1.5707963267948966

  -- , print (minimizeN 1 (toCcc cos) 5)  -- (3.141592653589793,6)
  -- , print (maximizeN 1 (toCcc cos) 5)  -- (6.283185307179586,5)

  -- , runCircMin "cos-min" 5 $ toCcc $ cos  -- (3.141592653589793,6)

  -- , runSynCirc "gradient-sin" $ toCcc $ gradient $ toCcc (sin @R)

  -- -- Regression tests
  -- , runCirc "ss"   $ toCcc $ ss   @Pair
  -- , runCirc "rss"  $ toCcc $ rss  @Pair
  -- , runCirc "mean" $ toCcc $ mean @Pair @R
  -- , runCirc "mse"  $ toCcc $ mse  @Pair
  -- , runCirc "r2"   $ toCcc $ r2   @Pair
  -- , runCirc "tss"  $ toCcc $ tss  @Pair

  -- , runSynCirc "mse-samples0"  $ toCcc $ mse samples0

  -- , runCirc "mse-samples0-ad" $ toCcc $ andDer @R $ mse samples0
  -- , runCirc "mse-samples0-der" $ toCcc $ der $ mse samples0

  -- , runCirc "mse-samples0-grad" $ toCcc $ gradient $ mse samples0

  -- , runSynCirc "q1" $ toCcc $ \ (a :: R) -> andDer @R (\ y -> y * a)
  -- , runSynCirc "q2" $ toCcc $ \ (a :: R) -> andDer @R (\ y -> a * y)

  -- , runCirc "mse-pair-grad" $ toCcc $ \ (samples :: Par1 Sample) -> gradient $ mse samples

  -- , runCirc "mse-samples0-grad" $ toCcc $ gradient $ mse samples0

  -- , runSynCirc "mse-samples1-ad" $ toCcc $ andDer @R $ mse samples1

  -- , runCircChase "mse-regress0" (0,0) $ toCcc $ gradient $ negate . mse samples0

  -- , runCirc "mse-regress1" $ toCcc $ gradient $ negate . mse samples1

  -- , runPrint (0,0) $ take 1000 . drop 10000 . minimizeL 0.01 (toCcc (mse samples1))

  -- , runCircChase "mse-regress0b" $ toCcc $ regress (0,0) mse samples0

  -- , runSynCirc "foo" $ toCcc $ \ (x,y) -> sqr (4 - (y + x * 3)) :: R

  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> x - y :: R -- fail
  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> 4 - (y + x) :: R -- fail
  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> sqr (4 - (y + x)) :: R -- fail
  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> sqr (4 - (y + x * 3)) :: R  -- fail

  -- , runSyn $ toCcc $ andDer @R $ uncurry ((+) @R) -- okay

  -- , runSyn $ toCcc $ andDer @R $ uncurry ((-) @R) -- fail

  -- , runSyn $ toCcc $ uncurry ((-) @R) -- okay

  -- , runSyn $ toCcc $ \ x -> x - 1 :: R -- okay

  -- , runSyn $ toCcc $ andDer @R $ \ x -> x - 1 :: R -- fail


  -- , runSyn $ toCcc $ andDer @R $ uncurry ((+) @R) . A.second negate -- fail


  -- , runSyn $ toCcc $ andDer @R $ \ x -> x + negate 1 :: R -- okay
  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> (y + x) :: R -- okay

  -- , runSynCirc "mse-samples1"  $ toCcc $ mse samples1
  -- , runSynCirc "mse-samples1-ad" $ toCcc $ andDer @R $ mse samples1

-- Broken

    -- , runCirc "mse-samples1-der"  $ toCcc $ gradient $ mse samples1

  -- , print (minimizeN 0.01 (mse samples1) (0,0))

  -- , print (regress mse samples1)

  -- , print (regress r2 samples1)


  -- -- Incremental evaluation. Partly brooken
  -- , runSynCirc "prod-ai" $ toCcc $ andInc $ uncurry ((*) @R)
  -- , runSynCirc "sop1-ai" $ toCcc $ andInc $ \ (x,y,z) -> x * y + y * z + x * z :: R
  -- , runSynCirc "magSqr-inc" $ toCcc $ inc $ andDer @R $ magSqr @R

#ifdef CONCAT_SMT
  -- , runCirc "smt-a" $ toCcc $ (\ (x :: R) -> sqr x == 9)

  -- , runCircSMT "smt-a" $ toCcc $ \ (x :: R) -> sqr x == 9

  -- , runSolve $ toCcc $ \ (x :: R) -> sqr x == 9
  -- , runSolve $ toCcc $ \ (x :: R) -> sqr x == 9 && x < 0
  -- , runSolve $ toCcc $ pred1 @R
  -- , runSolve $ toCcc $ \ b -> (if b then 3 else 5 :: Int) > 4

  -- , runSolve $ toCcc $ \ (x::R,y) -> x + y == 15 && x == 2 * y

  -- , runSolve $ toCcc $ fermat      @Int        -- Just (12,9,15)
  -- , runSolve $ toCcc $ fermatUnder @Int 10     -- Just (4,3,5)
  -- , runSolve $ toCcc $ fermatUnder @Int 100    -- Just (45,60,75)
  -- , runSolve $ toCcc $ fermatUnder @Int 1000   -- Just (975,140,985)
  -- , runSolve $ toCcc $ fermatUnder @Int 10000  -- Just (7635,4072,8653)

  -- , runSolve $ toCcc $ fermatMax @Int -- Just ((3,4,5),5)

  -- , runSolveAsc $ toCcc $ fermatMax @Int

  -- , runSolveAsc $ toCcc $ fermatMaxUnder @Int 10
  -- , runSolveAsc $ toCcc $ fermatMaxUnder @Int 100
  -- , runSolveAsc $ toCcc $ fermatMaxUnder @Int 1000
  -- , runSolveAsc $ toCcc $ fermatMaxUnder @Int 10000

  -- , runSolveAscFrom 500 $ toCcc $ (\ (x :: Int,y) -> x == y)

  -- -- Broken
  -- , runSolve $ toCcc $ (\ (x::R,y) -> x + y == 15 && x * y == 20)  -- "illegal argument" ??
#endif

  -- Recursion experiments
  -- , runSynCirc "fac1" $ toCcc $ fac1  -- bare unboxed var
  -- , runSynCirc "fac2" $ toCcc $ fac2 -- infinite compilation loop
  -- , runSynCirc "fac3" $ toCcc $ fac3 -- same infinite compilation loop
  -- , runSynCirc "fac4" $ toCcc $ fac4 -- same infinite compilation loop
  -- , runSynCirc "fac5" $ toCcc $ -- same infinite compilation loop
  --     \ (n0 :: Int) -> let go n = if n < 1 then 1 else n * go (n-1) in
  --                        go n0

  -- , runSynCirc "fac6" $ toCcc $ -- unhandled letrec
  --     \ (n0 :: Int, n1) -> let go n = if n < 1 then n1 else n * go (n-1) in
  --                        go n0

  -- , runSynCirc "fac7" $ toCcc $ fac7

  -- , runSynCirc "fac8" $ toCcc $ fac8 -- compilation loop
  -- , runSynCirc "fac9" $ toCcc $ fac9 -- compilation loop


  -- Array experiments

  -- , runSynCirc "map-negate-arr" $ toCcc $ fmap @(Vector Bool) @Int negate

  -- , runSynCirc "map-map-arr" $ toCcc $ fmap (+3) . fmap @(Vector Bool) @Int (+2)

  -- , runSynCirc "liftA2-arr-b" $ toCcc $ uncurry $ liftA2 @(Vector Bool) ((+) @Int)

  -- , runSynCirc "fmap-arr-bool-plus" $ toCcc $ fmap @(Vector Bool) ((+) @Int)
  -- , runSynCirc "app-arr-bool" $ toCcc $ (<*>) @(Vector Bool) @Int @Int

  -- , runSynCirc "fmap-fun-bool-plus" $ toCcc $ fmap   @((->) Bool) ((+) @Int)
  -- , runSynCirc "app-fun-bool"       $ toCcc $ (<*>)  @((->) Bool) @Int @Int

  -- , runSynCirc "liftA2-fun-bool"    $ toCcc $ liftA2 @((->) Bool) ((+) @Int)

  -- , runSynCirc "sum-arr-lb1" $ toCcc $ sum @(Vector (LB N1)) @Int
  -- , runSynCirc "sum-arr-lb2" $ toCcc $ sum @(Vector (LB N2)) @Int
  -- , runSynCirc "sum-arr-lb3" $ toCcc $ sum @(Vector (LB N3)) @Int
  -- , runSynCirc "sum-arr-lb4" $ toCcc $ sum @(Vector (LB N4)) @Int
  -- , runSynCirc "sum-arr-lb8" $ toCcc $ sum @(Vector (LB N8)) @Int

  -- , runSynCirc "sum-arr-rb1" $ toCcc $ sum @(Vector (RB N1)) @Int
  -- , runSynCirc "sum-arr-rb2" $ toCcc $ sum @(Vector (RB N2)) @Int
  -- , runSynCirc "sum-arr-rb3" $ toCcc $ sum @(Vector (RB N3)) @Int
  -- , runSynCirc "sum-arr-rb4" $ toCcc $ sum @(Vector (RB N4)) @Int
  -- , runSynCirc "sum-arr-rb8" $ toCcc $ sum @(Vector (RB N8)) @Int

  -- , runSynCirc "fmap-fun-bool-plus" $ toCcc $ fmap   @((->) Bool) ((+) @Int)
  -- , runSynCirc "app-fun-bool"       $ toCcc $ (<*>)  @((->) Bool) @Int @Int
  -- , runSynCirc "inArr2-liftA2-bool"    $ toCcc $
  --      (inNew2 (liftA2 (+)) :: Binop (Vector Bool Int))

  -- , runSynCirc "sum-fun-2" $ toCcc $ (sum @((->) Bool) @Int)
  -- , runSynCirc "sum-fun-4" $ toCcc $ (sum @((->) (Bool :* Bool)) @Int)

  -- , runSynCirc "sum-fun-8" $ toCcc $ (sum @((->) ((Bool :* Bool) :* Bool)) @Int)

  -- , runSynCirc "unpack-arr-2" $ toCcc $ (unpack @(Vector Bool Int))
  -- , runSynCirc "unpack-arr-4" $ toCcc $ (unpack @(Vector (Bool :* Bool) Int))

  -- , runSynCirc "sum-arr-fun-2"    $ toCcc $
  --      (sum . unpack :: Vector Bool Int -> Int)
  -- , runSynCirc "sum-arr-fun-4"    $ toCcc $
  --      (sum . unpack :: Vector (Bool :* Bool) Int -> Int)
  -- , runSynCirc "sum-arr-fun-8"    $ toCcc $
  --      (sum . unpack :: Vector ((Bool :* Bool) :* Bool) Int -> Int)

  -- , runSynCirc "fmap-arr-bool" $ toCcc $ fmap @(Vector Bool) (negate @Int)
  -- , runSynCirc "liftA2-arr-bool" $ toCcc $ liftA2 @(Vector Bool) ((+) @Int)
  -- , runSynCirc "liftArr2-bool" $ toCcc $ liftArr2 @Bool ((+) @Int)
  -- , runSynCirc "liftArr2-bool-unc" $ toCcc $ uncurry (liftArr2 @Bool ((+) @Int))
  -- , runSynCirc "sum-arr-bool" $ toCcc $ sum @(Vector Bool) @Int

  -- -- Int equality turns into matching, which takes some care.
  -- -- See boxCon/tweak in ConCat.Plugin
  -- , runSynCirc "equal-3"     $ toCcc $ \ (x :: Int) -> x == 3
  -- , runSynCirc "unequal-3"   $ toCcc $ \ (x :: Int) -> x /= 3
  -- , runSynCirc "not-equal-3" $ toCcc $ \ (x :: Int) -> not (x == 3)

  -- , runSynCirc "multi-if-equal-int" $ toCcc $
  --     \ case
  --         1 -> 3
  --         5 -> 7
  --         7 -> 9
  --         (_ :: Int) -> 0 :: Int

  -- , runSynCirc "foo" $ toCcc $ div @Int

  -- , runSynCirc "foo" $ toCcc $ (*) @Int

  -- , runSynCirc "foo" $ toCcc $ \ (x :: Int) -> 13 * x == 130

  -- , runSynCirc "multi-if-equal-int-scrut" $ toCcc $
  --     \ x -> case 13 * x of
  --         1 -> 3
  --         5 -> 7
  --         7 -> 9
  --         (_ :: Int) -> 0 :: Int

  -- , runSynCirc "if-equal-int-x" $ toCcc $
  --     \ x -> case x of
  --         5 -> x `div` 2
  --         (_ :: Int) -> 0 :: Int

  ]

f1 :: Num a => a -> a
f1 x = x^2

pred1 :: (Num a, Ord a) => a :* a -> Bool
pred1 (x,y) =    x < y
              && y < 100
              && foo x 20 f
              && 0 <= x - 3 + 7 * y
              && (x == y || y + 20 == x + 30)
  where
    f z k = z > 100 && k 20
    foo a b g = g 222 (< a + b)

fermat :: (Ord a, Num a) => (a,a,a) -> Bool
fermat (a,b,c) = sqr a + sqr b == sqr c && a > 0 && b > 0 && c > 0

max3 :: (Ord a, Num a) => (a,a,a) -> a
max3 (a,b,c) = a `max` b `max` c

fermatUnder :: (Ord a, Num a) => a -> (a,a,a) -> Bool
fermatUnder upper w = fermat w && max3 w <= upper

-- Maximal Fermat triple, measured by maximum element.
fermatMax :: (Ord a, Num a) => ((a,a,a),a) -> Bool
fermatMax (w,m) = fermat w && m == max3 w

-- fermatMax but with an upper bound.
fermatMaxUnder :: (Ord a, Num a) => a -> ((a,a,a),a) -> Bool
fermatMaxUnder upper q = fermatMax q && snd q <= upper

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

#ifdef CONCAT_SMT
runSolve :: (GenBuses a, Show a, EvalE a) => (a :> Bool) -> IO ()
runSolve = print . solve
-- runSolve = print <=< solve

runSolveAscFrom :: ( GenBuses a, Show a, EvalE a, GenBuses r, EvalE r
                   , OrdCat (:>) r, ConstCat (:>) r, Show r )
  => r -> (a :* r :> Bool) -> IO ()
-- runSolveAscFrom r = print . solveAscendingFrom r
-- runSolveAscFrom r = putStrLn . take 25 . show . solveAscendingFrom r
-- runSolveAscFrom r = print . null . solveAscendingFrom r
-- runSolveAscFrom r = print . (> 3) . length . take 4 . solveAscendingFrom r
runSolveAscFrom r = mapM_ print . solveAscendingFrom r

-- runSolve = print <=< solve

runCircSMT :: (GenBuses a, Show a, EvalE a) => String -> (a :> Bool) -> IO ()
runCircSMT nm circ = runCirc nm circ >> runSolve circ

-- TODO: rework runCircSMT to generate the circuit graph once
-- rather than twice.

runSolveAsc :: ( GenBuses a, Show a, GenBuses r, Show r, EvalE a, EvalE r
               , OrdCat (:>) r, ConstCat (:>) r )
            => (a :* r :> Bool) -> IO ()
runSolveAsc = mapM_ print . solveAscending

-- The following definition hangs with infinite lists. More generally, it
-- produces no list output until all of the list elements have been constructed.
-- I'm stumped as to why.

-- runSolveAsc = print . solveAscending

-- runSolveAsc = print <=< solveAscending

#endif

runPrint :: Show b => a -> (a -> b) -> IO ()
runPrint a f = print (f a)

runChase :: (HasV R a, Zip (V R a), Eq a, Show a)
         => a -> (a -> a) -> IO ()
runChase a0 f = print (chase 1 f a0)

runCircChase :: (GO a R, HasV R a, Zip (V R a), Eq a, Show a)
             => String -> a -> ((:>) :**: (->)) a a -> IO ()
runCircChase nm a0 (circ :**: f) = runCirc nm circ >> runChase a0 f

-- gradient :: HasV R a => (a -> R) -> a -> a

-- gradientD :: HasV R a => D R a R -> a -> a


{--------------------------------------------------------------------
    Misc definitions
--------------------------------------------------------------------}

twice :: Num a => a -> a
twice x = x + x

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


samples0 :: Par1 Sample
samples0 = Par1 (3,4)

samples1 :: Pair Sample
-- samples1 = (0,0) :# (1,1)
samples1 = (3,4) :# (5,6)

samples2 :: [Sample]
samples2 = [(3,4),(5,6)]

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

---------

-- -- coerceTest :: Pair R -> (Par1 :*: Par1) R
-- -- coerceTest = coerce

-- #if 0

-- -- type OkLC = Ok (L R) &+& Ok (:>)
-- type OkLC = OkLM R &+& GenBuses

-- #else

-- -- class    (Ok (L R) a, Ok (:>) a) => OkLC a
-- -- instance (Ok (L R) a, Ok (:>) a) => OkLC a

-- class    (OkLM R a, GenBuses a) => OkLC a
-- instance (OkLM R a, GenBuses a) => OkLC a

-- --     • The constraint ‘OkLM R a’ is no smaller than the instance head
-- --       (Use UndecidableInstances to permit this)
-- --     • In the instance declaration for ‘OkLC a’
-- -- test/Examples.hs:688:10-41: error: …
-- --     • The constraint ‘GenBuses a’ is no smaller than the instance head
-- --       (Use UndecidableInstances to permit this)

-- instance OpCon (:*) (Sat OkLC) where
--   inOp = Entail (Sub Dict)
--   {-# INLINE inOp #-}

-- #endif

-- foo1 :: (R -> R -> R) -> Choice Yes1 R R
-- -- foo1 f = reveal (toCcc' (unCcc' (conceal (Choice @Yes1 f))))
-- foo1 f = toCcc (unCcc (Choice @Yes1 f))

type OkLC' = OkLM R &+& GenBuses

-- Experimenting with a rule failure. See 2017-10-20 notes.

-- -- Works ok
-- foo1 :: Choice (Ok (:>)) a b -> Choice GenBuses a b
-- foo1 z = toCcc (unCcc z)

