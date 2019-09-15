{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
-- {-# OPTIONS_GHC -Wall            #-}

{-# OPTIONS_GHC -freduction-depth=0 #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=500 #-}

-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:trace #-}

module BasicTests where

import           ConCat.ADFun hiding (D)
import           ConCat.AdditiveFun
import           ConCat.AltCat (toCcc, toCcc')
import qualified ConCat.AltCat as A
import           ConCat.Deep
import           ConCat.Dual
import           ConCat.FFT
import           ConCat.Free.LinearRow
import           ConCat.Free.VectorSpace (HasV(..))
import           ConCat.GAD
import           ConCat.Incremental
import           ConCat.Interval
import           ConCat.Misc ((:*), (:+), R, C, Unop, Binop, magSqr, sqr, unzip)
import           ConCat.Nat
import           ConCat.Orphans ()
import           ConCat.RAD
import           ConCat.Rebox ()
import           ConCat.Shaped
import           Control.Applicative (liftA2)
import           Data.Distributive
import           Data.Finite
import           Data.Functor.Rep
import           Data.Key
import           Data.Pointed
import           Data.Vector.Sized (Vector)
import           GHC.Generics hiding (C, D, R)
import           GHC.TypeLits ()
import           Miscellany hiding (runSynCirc,runSynCircDers)
import           Prelude hiding (unzip, zip, zipWith)
import           Test.Tasty (TestTree, testGroup)
import           Utils


-- import ConCat.AltCat (toCcc)
-- import ConCat.Circuit (mkGraph, graphDot)
-- import ConCat.Syntactic (render)
-- import Data.ByteString.Lazy.Char8 (pack)
-- import Data.Semigroup ((<>))
-- import Miscellany (GO)
-- import Test.Tasty (TestTree, testGroup)
-- import Test.Tasty.Golden

basicTests :: TestTree
basicTests = testGroup "basic tests"
  [ testGroup "" []

  -- -- Circuit graphs

  -- , runSynCirc' "add" (toCcc ((+) @R)) (toCcc ((+) @R))

  -- , runSynCirc "add"         $ (+) @R

  -- , runSynCirc "add" ((+) @R)

  -- , runSynCirc "add-uncurry" $ uncurry ((+) @R)
  -- , runSynCirc "dup"         $ A.dup @(->) @R
  -- , runSynCirc "fst"         $ fst @R @R
  -- , runSynCirc "twice"       $ twice @R
  -- , runSynCirc "sqr"         $ sqr @R

  , runSynCirc "complex-mul" $ uncurry ((*) @C)

  -- , runSynCirc "magSqr"      $ magSqr @R
  -- , runSynCirc "cosSinProd"  $ cosSinProd @R
  -- , runSynCirc "xp3y"        $ \ (x,y) -> x + 3 * y :: R
  -- , runSynCirc "horner"      $ horner @R [1,3,5]
  -- , runSynCirc "cos-2xx"     $ \ x -> cos (2 * x * x) :: R

  -- -- Automatic differentiation variants
  -- , runSynCircDers "add"     $ uncurry ((+) @R)
  -- , runSynCircDers "sin"     $ sin @R
  -- , runSynCircDers "cos"     $ cos @R
  -- , runSynCircDers "twice"   $ twice @R
  -- , runSynCircDers "sqr"     $ sqr @R

  -- , runSynCircDers "magSqr"  $ magSqr  @R

  -- , runSynCircDers "cos-2x"  $ \ x -> cos (2 * x) :: R
  -- , runSynCircDers "cos-2xx" $ \ x -> cos (2 * x * x) :: R
  -- , runSynCircDers "cos-xpy" $ \ (x,y) -> cos (x + y) :: R

  -- , runSynCirc "cosSinProd" $ andDerR $ cosSinProd @R

#if 0

  , runSynCirc "times-13" $ \(x :: Int) -> 13 * x == 130

  , runSynCirc "mul-int" $ (*) @Int

  , runSynCirc "div-int" $ div @Int

  , runSynCirc "not-equal-3" $ \(x :: Int) -> not (x == 3)

  , runSynCirc "unequal-3" $ \(x :: Int) -> x /= 3

    -- Int equality turns into matching, which takes some care.
    -- See boxCon/tweak in ConCat.Plugin
  , runSynCirc "equal-3" $ \(x :: Int) -> x == 3

  , runSynCirc "sum-fun-8" $
      (sum @((->) ((Bool :* Bool) :* Bool)) @Int)

  , runSynCirc "sum-fun-4" $ (sum @((->) (Bool :* Bool)) @Int)

  , runSynCirc "sum-fun-2" $ (sum @((->) Bool) @Int)

  , runSynCirc "app-fun-bool" $ (<*>) @((->) Bool) @Int @Int

  , runSynCirc "liftA2-fun-bool" $ liftA2 @((->) Bool) ((+) @Int)

  , runSynCirc "fmap-fun-bool-plus" $ fmap @((->) Bool) ((+) @Int)

  , runSynCirc "mul-andInc"    $ andInc $ uncurry ((*) @R)

  , runSynCirc "subtract-1" $ \x -> x - 1 :: R

  , runSynCirc "subtract-uncurry" $ uncurry ((-) @R)

  , runSynCirc "random-math" $ \(x, y) -> sqr (4 - (y + x * 3)) :: R

  , runSynCirc "fmap-cos-adr" $ andDerR $ fmap @(Vector 5) @R cos

  , runSynCirc "zip-adr" $ andDerR $ uncurry (zip @(Vector 5) @R @R)

  , runSynCirc "sumA-gradr" $ andGradR $ sumA @(Vector 5) @R

  , runSynCirc "sumA-adr" $ andDerR $ sumA @(Vector 5) @R

  , runSynCirc "sumA-fad" $ andDeriv @(-+>) $ sumA @(Vector 5) @R

  , runSynCirc "sumA" $ sumA @(Vector 5) @R

  , runSynCirc "sumA-adf" $ andDeriv @(->) $ sumA @(Vector 5) @R

  , runSynCirc "dup-gradr" $ andGrad2R $ A.dup @(->) @R

  , runSynCirc "cos-xpy-gradr" $
      andGradR $ \(x, y) -> cos (x + y) :: R

  , runSynCirc "exl" $ A.exl @(->) @R @R

  -- , runSynCirc "fst-dual" $ toDual $ fst @R @R -- seems to loop endlessly

  , runSynCirc "fst-af" $ addFun $ fst @R @R

  -- -- !! compile failed
  -- , runSynCirc "point-dual" $ toDual $ point @(Vector 5) @R

  , runSynCirc "sumA-dual" $ toDual $ sumA @(Vector 5) @R

  , runSynCirc "cos-adfl" $ andDerFL @R $ cos @R

  -- Automatic differentiation with ADFun + linear

  , runSynCirc "sin-adfl" $ andDerFL @R $ sin @R

  , runSynCirc "foo9-d" $ derF (\(_ :: R) -> 1 :: R)

  , runSynCirc "deriv-sin" $ \x -> derF (sin @R) x 1

  , runSynCirc "sin-df" $ derF $ sin @R

  , runSynCirc "idL-v" (\() -> idL @(Vector 8) @R) -- ok

  -- , runSynCirc "idL-2" (\() -> idL @(Par1 :*: Par1) @R) -- fail

  , runSynCirc "equal-sum" $ (==) @(() :+ ())

  , runSynCirc "equal-Int" $ (==) @Int

  -- -- !! compile failed
  -- , runSynCirc "horner-iv" $ ivFun $ horner @R [1,3,5]

  -- -- !! compile failed
  -- , runSynCirc "xyp3-iv"   $ ivFun $ \ (x,y) -> x * y + 3 :: R

  -- -- !! compile failed
  -- , runSynCirc "magSqr-iv" $ ivFun $ magSqr @Int

  -- -- !! compile failed
  -- , runSynCirc "sqr-iv" $ ivFun $ sqr @Int

  -- -- !! compile failed
  -- , runSynCirc "thrice-iv" $ ivFun $ \x -> 3 * x :: Int

  -- -- !! compile failed
  -- , runSynCirc "mul-iv"    $ ivFun $ uncurry ((*) @Int)

  -- Interval analysis
  -- , runSynCirc "add-iv" $ ivFun $ uncurry ((+) @Int)

  , runSynCirc "fft-pair" $ fft @Pair @Double

  , runSynCirc "sum-rb4"    $ sum   @(RBin N4) @Int

  -- Circuit graphs on trees etc
  , runSynCirc "sum-pair" $ sum @Pair @Int

  , runSynCirc "unV-r-v2" $ unV @R @(Vector 2 R)

  , runSynCirc "linearF-v" $ linearF @R @(Vector 8) @Par1

  , runSynCirc "fmap-idL-v" (\ (h :: Vector 8 R -> Vector 8 R) -> h <$> idL)

  , runSynCirc "distribute-v-p" (distribute @Pair @(Vector 4) @R)

  , runSynCirc "distribute-p-v" (distribute @(Vector 4) @Pair @R)

  , runSynCirc "distribute" $
        (A.distributeC :: ((Par1 :*: Par1)) (Vector 4 R) -> (Vector 4) ((Par1 :*: Par1) R))

  , runSynCirc "foo" $ id @(Vector 4 Bool :* Bool)

  , runSynCirc "id-pair-v" $ id @((Par1 :*: Par1) (Vector 4 R))

  , runSynCirc "distribute-par" $
        (distribute :: (Vector 4) ((Par1 :*: Par1) R) -> ((Par1 :*: Par1)) (Vector 4 R))

  , runSynCirc "distribute-v" (distribute @(Vector 4) @(U1 :*: Par1) @R)

  , runSynCirc "distribute-pair-pair-r" (distribute @Pair @Pair @R)

  , runSynCirc "tabulate-v" $
      (tabulate :: (Finite 8 -> Bool) -> Vector 8 Bool)

  -- -- !! compile failed
  -- , runSynCirc "point-v" $ (point :: Bool -> Vector 8 Bool)

  , runSynCirc "fmap-not-v" $ (fmap not :: Unop (Vector 2 Bool))

  , runSynCirc "plus-mul-integer" (\(x :: Integer, y) -> x * (x + y))

  , runSynCirc "plus-integer" ((+) @Integer)

  , runSynCirc "ge-integer-b" (\(x :: Integer, y) -> not (x < y))

  , runSynCirc "ne-integer-b" (\(x :: Integer, y) -> not (x == y))

  , runSynCirc "le-integer" ((<=) @Integer)

  , runSynCirc "ne-integer" ((/=) @Integer)

  , runSynCirc "eq-integer" ((==) @Integer)

  , runSynCirc "zipWith-v" $ zipWith @(Vector 7) (||)

  , runSynCirc "fmap-v-dl" $ derFL @R $ (fmap negate :: Unop (Vector 5 R))

  , runSynCirc "y-plus-x" $ \(x, y) -> y + x :: R

  , runSynCirc "const-y" $ \(_x :: R, y :: R) -> y

  -- Correct, but more complex/effortful than I'd like. See 2017-12-02 notes.
  , runSynCirc "fmapT-oops-b" $ \ (x, v :: Vector 5 R) -> fmap (+x) v

  , runSynCirc "fmapT" $ \x (v :: Vector 5 R) -> fmap (+ x) v

  -- -- !! compile failed
  -- , runSynCirc "fmap-point" $
  --     \(x :: R) -> fmap negate (point @(Vector 5) x)

  , runSynCirc "fmap-negate2" $
      \(v :: Vector 5 R) -> fmap negate (fmap (+ 1) v)

  , runSynCirc "fmap-v-d" $ derF (fmap negate :: Unop (Vector 5 R))

  , runSynCirc "fmap-r-const" $ fmap @(Vector 5) @R (const True)

  , runSynCirc "fmap-v-der-e" $ andDerF $ fmap @(Vector 5) @R negate

  , runSynCirc "relu-ad" $ andDerF $ max @R 0

  , runSynCirc "max-ad" $ andDerF $ uncurry (max @R)

  , runSynCirc "maxC-der" $ andDerF $ A.maxC @(->) @R

  , runSynCirc "max" $ uncurry (max @R)

  , runSynCirc "negate-derF" $ derF $ fmap @(Vector 5) @R negate

  , runSynCirc "unzip-b" $ unzip @(Vector 5) @R @R

  , runSynCirc "fmap-complex-b" $ (\ (x,xs :: Vector 5 R) -> fmap (+x) xs)

  , runSynCirc "fst-bool-r" $ fst @Bool @R

  , runSynCirc "fmap-b" $ (fmap negate :: Unop (Vector 5 R))

  , runSynCirc "fmap-negate-unop" $ (fmap negate :: Unop (Vector 5 R))

  , runSynCirc "zipWith-mult-v" $ (zipWith (*) :: Binop (Vector 5 R))

  , runSynCirc "zipWith-vv" $
      uncurry (zipWith (*) :: Binop (Vector 5 R))

  , runSynCirc "foo2" $ uncurry $ \(x :: R) -> (sin x *)

  , runSynCirc "der-sin" $ derFL @R $ sin @R

  , runSynCirc "mul-sin" $ \(x :: R) -> (sin x *)

  , runSynCirc "equal-pair-b" $ uncurry ((==) @(Bool :* Int))

  , runSynCirc "equal-pair-d" $ uncurry ((==) @(Int :* R))

  , runSynCirc "equal-pair-b-int" $ uncurry ((==) @(Int :* R))

  , runSynCirc "equal-pair-a" $ uncurry ((==) @(Bool :* Int))

  , runSynCirc "equal-pair-uncurry-b" $ uncurry ((==) @(R :* Int))

  , runSynCirc "equal-pair-curried-b" $ (==) @(R :* Int)

  , runSynCirc "uncurry-eq-i" $ uncurry ((==) @Int)

  -- Play with the "cat equal" trick.
  , runSynCirc "eq-i" $ (==) @Int

  , runSynCirc "err1Grad-c" $ uncurry $ err1Grad (\ (p,q) z -> p * z + q)
  , runSynCirc "err1-c" $ \(a, b) -> err1 (\z -> a * z + b)

  , runSynCirc "err1-b" $ err1 (\z -> 3 * z + 2)

  , runSynCirc "err1-a" $ uncurry err1

  , runSynCirc "linear" $ ConCat.Deep.linear @(Vector 10) @(Vector 20) @R

  , runSynCirc "const" $ A.const @(->) @R @R

#endif

  ]

runSynCircDers :: (GO a b, Num b) => String -> (a -> b) -> TestTree
runSynCircDers nm f =
  testGroup (nm ++ "-ders")
  [ {- runSynCirc nm               $ id       $ f
  , runSynCirc (nm ++ "-adf")   $ andDerF  $ f
  , runSynCirc (nm ++ "-adr")   $ andDerR  $ f
  , -} runSynCirc (nm ++ "-gradr") $ andGradR $ f
  ]
{-# INLINE runSynCircDers #-}
