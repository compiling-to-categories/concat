{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -Wall            #-}

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
import           ConCat.Interval
import           ConCat.Misc ((:*), (:+), Binop, R, Unop, magSqr, sqr, unzip)
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
import           Miscellany
import           Prelude hiding (unzip, zip, zipWith)
import           Test.Tasty (TestTree, testGroup)
import           Utils


basicTests :: TestTree
basicTests = testGroup "basic tests"
  [ testGroup "" []

  , runSynCircGold "times-13" $ toCcc $ \(x :: Int) -> 13 * x == 130

  , runSynCircGold "mul-int" $ toCcc $ (*) @Int

  , runSynCircGold "div-int" $ toCcc $ div @Int

  , runSynCircGold "not-equal-3" $ toCcc $ \(x :: Int) -> not (x == 3)

  , runSynCircGold "unequal-3" $ toCcc $ \(x :: Int) -> x /= 3

    -- Int equality turns into matching, which takes some care.
    -- See boxCon/tweak in ConCat.Plugin
  , runSynCircGold "equal-3" $ toCcc $ \(x :: Int) -> x == 3

  , runSynCircGold "sum-fun-8" $
      toCcc $ (sum @((->) ((Bool :* Bool) :* Bool)) @Int)

  , runSynCircGold "sum-fun-4" $ toCcc $ (sum @((->) (Bool :* Bool)) @Int)

  , runSynCircGold "sum-fun-2" $ toCcc $ (sum @((->) Bool) @Int)

  , runSynCircGold "app-fun-bool" $ toCcc $ (<*>) @((->) Bool) @Int @Int

  , runSynCircGold "liftA2-fun-bool" $ toCcc $ liftA2 @((->) Bool) ((+) @Int)

  , runSynCircGold "fmap-fun-bool-plus" $ toCcc $ fmap @((->) Bool) ((+) @Int)

  -- -- !! compile timeout
  -- , runSynCircGold "mul-andInc"    $ toCcc $ andInc $ uncurry ((*) @R)

  , runSynCircGold "subtract-1" $ toCcc $ \x -> x - 1 :: R

  , runSynCircGold "subtract-uncurry" $ toCcc $ uncurry ((-) @R)

  , runSynCircGold "random-math" $ toCcc $ \(x, y) -> sqr (4 - (y + x * 3)) :: R

  , runSynCircGold "fmap-cos-adr" $ toCcc $ andDerR $ fmap @(Vector 5) @R cos

  , runSynCircGold "zip-adr" $ toCcc $ andDerR $ uncurry (zip @(Vector 5) @R @R)

  , runSynCircGold "sumA-gradr" $ toCcc $ andGradR $ sumA @(Vector 5) @R

  , runSynCircGold "sumA-adr" $ toCcc $ andDerR $ sumA @(Vector 5) @R

  , runSynCircGold "sumA-fad" $ toCcc $ andDeriv @(-+>) $ sumA @(Vector 5) @R

  , runSynCircGold "sumA" $ toCcc $ sumA @(Vector 5) @R

  , runSynCircGold "sumA-adf" $ toCcc $ andDeriv @(->) $ sumA @(Vector 5) @R

  , runSynCircGold "dup-gradr" $ toCcc $ andGrad2R $ A.dup @(->) @R

  , runSynCircGold "cos-xpy-gradr" $
      toCcc $ andGradR $ \(x, y) -> cos (x + y) :: R

  , runSynCircGold "fst-gradr" $ toCcc $ andGradR (fst @R @R)

  , runSynCircGold "add-gradr" $ toCcc $ andGradR $ uncurry ((+) @R)

  , runSynCircGold "cos-gradr" $ toCcc $ andGradR $ cos @R

  , runSynCircGold "sin-gradr" $ toCcc $ andGradR $ sin @R

  , runSynCircGold "cos-xpy-adr" $ toCcc $ andDerR $ \(x, y) -> cos (x + y) :: R

  , runSynCircGold "fst-adr" $ toCcc $ andDerR (fst @R @R)

  , runSynCircGold "add-adr" $ toCcc $ andDerR $ uncurry ((+) @R)

  , runSynCircGold "cos-adr" $ toCcc $ andDerR $ cos @R

  , runSynCircGold "sin-adr" $ toCcc $ andDerR $ sin @R

  , runSynCircGold "exl" $ toCcc $ A.exl @(->) @R @R

  , runSynCircGold "fst-dual" $ toCcc $ toDual $ fst @R @R

  , runSynCircGold "fst-af" $ toCcc $ addFun $ fst @R @R

  , runSynCircGold "point-dual" $ toCcc $ toDual $ point @(Vector 5) @R

  , runSynCircGold "sumA-dual" $ toCcc $ toDual $ sumA @(Vector 5) @R

  , runSynCircGold "cos-adfl" $ toCcc $ andDerFL @R $ cos @R

  -- Automatic differentiation with ADFun + linear
  , runSynCircGold "sin-adfl" $ toCcc $ andDerFL @R $ sin @R

  , runSynCircGold "cos-adf" $ toCcc $ andDerF $ cos @R

  -- Automatic differentiation with ADFun:
  , runSynCircGold "sin-adf" $ toCcc $ andDerF $ sin @R

  , runSynCircGold "foo9-d" $ toCcc $ derF (\(_ :: R) -> 1 :: R)

  , runSynCircGold "deriv-sin" $ toCcc $ \x -> derF (sin @R) x 1

  , runSynCircGold "sin-df" $ toCcc $ derF $ sin @R

  , runSynCircGold "idL-v" $ toCcc (\() -> idL @(Vector 8) @R) -- ok

  , runSynCircGold "idL-2" $ toCcc (\() -> idL @(Par1 :*: Par1) @R) -- fail

  , runSynCircGold "equal-sum" $ toCcc $ (==) @(() :+ ())

  , runSynCircGold "equal-Int" $ toCcc $ (==) @Int

  -- -- !! compile timeout
  -- , runSynCircGold "horner-iv" $ toCcc $ ivFun $ horner @R [1,3,5]

  -- -- !! compile timeout
  -- , runSynCircGold "xyp3-iv"   $ toCcc $ ivFun $ \ (x,y) -> x * y + 3 :: R

  -- -- !! compile timeout
  -- , runSynCircGold "magSqr-iv" $ toCcc $ ivFun $ magSqr @Int

  , runSynCircGold "sqr-iv" $ toCcc $ ivFun $ sqr @Int

  , runSynCircGold "thrice-iv" $ toCcc $ ivFun $ \x -> 3 * x :: Int

  -- -- !! compile timeout
  -- , runSynCircGold "mul-iv"    $ toCcc $ ivFun $ uncurry ((*) @Int)

  -- Interval analysis
  , runSynCircGold "add-iv" $ toCcc $ ivFun $ uncurry ((+) @Int)

  , runSynCircGold "fft-pair" $ toCcc $ fft @Pair @Double

  -- -- !! compile timeout
  -- , runSynCircGold "sum-rb4"    $ toCcc $ sum   @(RBin N4) @Int

  -- Circuit graphs on trees etc
  , runSynCircGold "sum-pair" $ toCcc $ sum @Pair @Int

  , runSynCircGold "unV-r-v2" $ toCcc $ unV @R @(Vector 2 R)

  , runSynCircGold "linearF-v" $ toCcc $ linearF @R @(Vector 8) @Par1

  -- -- !! compile failed
  -- , runSynCircGold "fmap-idL-v" $ toCcc (\ (h :: Vector 8 R -> Vector 8 R) -> h <$> idL)

  , runSynCircGold "distribute-v-p" $ toCcc (distribute @Pair @(Vector 4) @R)

  , runSynCircGold "distribute-p-v" $ toCcc (distribute @(Vector 4) @Pair @R)

  , runSynCircGold "distribute" $
      toCcc
        (A.distributeC :: ((Par1 :*: Par1)) (Vector 4 R) -> (Vector 4) ((Par1 :*: Par1) R))

  , runSynCircGold "foo" $ toCcc $ id @(Vector 4 Bool :* Bool)

  , runSynCircGold "id-pair-v" $ toCcc $ id @((Par1 :*: Par1) (Vector 4 R))

  , runSynCircGold "distribute-par" $
      toCcc
        (distribute :: (Vector 4) ((Par1 :*: Par1) R) -> ((Par1 :*: Par1)) (Vector 4 R))

  , runSynCircGold "distribute-v" $ toCcc (distribute @(Vector 4) @(U1 :*: Par1) @R)

  , runSynCircGold "distribute-pair-pair-r" $ toCcc (distribute @Pair @Pair @R)

  , runSynCircGold "tabulate-v" $
      toCcc (tabulate :: (Finite 8 -> Bool) -> Vector 8 Bool)

  , runSynCircGold "point-v" $ toCcc $ (point :: Bool -> Vector 8 Bool)

  , runSynCircGold "fmap-not-v" $ toCcc $ (fmap not :: Unop (Vector 2 Bool))

  , runSynCircGold "plus-mul-integer" $ toCcc (\(x :: Integer, y) -> x * (x + y))

  , runSynCircGold "plus-integer" $ toCcc ((+) @Integer)

  , runSynCircGold "ge-integer-b" $ toCcc (\(x :: Integer, y) -> not (x < y))

  , runSynCircGold "ne-integer-b" $ toCcc (\(x :: Integer, y) -> not (x == y))

  , runSynCircGold "le-integer" $ toCcc ((<=) @Integer)

  , runSynCircGold "ne-integer" $ toCcc ((/=) @Integer)

  , runSynCircGold "eq-integer" $ toCcc ((==) @Integer)

  -- -- !! compile timeout
  -- , runSynCircGold "zipWith-v" $ toCcc $ zipWith @(Vector 7) (||)

  -- -- !! compile timeout
  -- , runSynCircGold "fmap-v-dl" $ toCcc $ derFL @R $ (fmap negate :: Unop (Vector 5 R))

  , runSynCircGold "y-plus-x" $ toCcc $ \(x, y) -> y + x :: R

  , runSynCircGold "const-y" $ toCcc $ \(_x :: R, y :: R) -> y

  -- -- !! compile failed
  -- -- Correct, but more complex/effortful than I'd like. See 2017-12-02 notes.
  -- , runSynCircGold "fmapT-oops-b" $ toCcc $ \ (x, v :: Vector 5 R) -> fmap (+x) v

  , runSynCircGold "fmapT" $ toCcc $ \x (v :: Vector 5 R) -> fmap (+ x) v

  , runSynCircGold "fmap-point" $
      toCcc $ \(x :: R) -> fmap negate (point @(Vector 5) x)

  , runSynCircGold "fmap-negate2" $
      toCcc $ \(v :: Vector 5 R) -> fmap negate (fmap (+ 1) v)

  , runSynCircGold "fmap-v-d" $ toCcc $ derF (fmap negate :: Unop (Vector 5 R))

  , runSynCircGold "fmap-r-const" $ toCcc $ fmap @(Vector 5) @R (const True)

  , runSynCircGold "fmap-v-der-e" $ toCcc $ andDerF $ fmap @(Vector 5) @R negate

  -- -- !! compile timeout
  -- , runSynCircGold "relu-ad" $ toCcc $ andDerF $ max @R 0

  , runSynCircGold "max-ad" $ toCcc $ andDerF $ uncurry (max @R)

  , runSynCircGold "maxC-der" $ toCcc $ andDerF $ A.maxC @(->) @R

  , runSynCircGold "max" $ toCcc $ uncurry (max @R)

  , runSynCircGold "negate-derF" $ toCcc $ derF $ fmap @(Vector 5) @R negate

  , runSynCircGold "unzip-b" $ toCcc $ unzip @(Vector 5) @R @R

  -- -- -- !! compile failed
  -- -- , runSynCircGold $ toCcc $ (\ (x,xs :: Vector 5 R) -> fmap (+x) xs)

  -- -- !! compile failed
  -- , runSynCircGold "fmap-complex-b" $ toCcc $ (\ (x,xs :: Vector 5 R) -> fmap (+x) xs)

  , runSynCircGold "fst-bool-r" $ toCcc' $ fst @Bool @R

  , runSynCircGold "fmap-b" $ toCcc $ (fmap negate :: Unop (Vector 5 R))

  , runSynCircGold "fmap-negate-unop" $ toCcc $ (fmap negate :: Unop (Vector 5 R))

  , runSynCircGold "zipWith-mult-v" $ toCcc $ (zipWith (*) :: Binop (Vector 5 R))

  , runSynCircGold "zipWith-vv" $
      toCcc $ uncurry (zipWith (*) :: Binop (Vector 5 R))

  , runSynCircGold "foo2" $ toCcc $ uncurry $ \(x :: R) -> (sin x *)

  -- -- !! compile timeout
  -- , runSynCircGold "foo" $ toCcc $ derFL @R $ sin @R

  , runSynCircGold "mul-sin" $ toCcc $ \(x :: R) -> (sin x *)

  , runSynCircGold "add" $ toCcc $ (+) @Integer

  , runSynCircGold "equal-pair-b" $ toCcc $ uncurry ((==) @(Bool :* Int))

  -- -- !! compile timeout
  -- , runSynCircGold "equal-pair-d" $ toCcc $ toCcc $ uncurry ((==) @(Int :* R))

  -- -- !! compile timeout
  -- , runSynCircGold "equal-pair-b" $ toCcc $ uncurry ((==) @(Int :* R))

  -- -- !! compile timeout
  -- , runSynCircGold "equal-pair-a" $ toCcc $ uncurry ((==) @(Bool :* Int))

  , runSynCircGold "equal-pair-uncurry-b" $ toCcc $ uncurry ((==) @(R :* Int))

  , runSynCircGold "equal-pair-b" $ toCcc $ (==) @(R :* Int)

  , runSynCircGold "uncurry-eq-i" $ toCcc $ uncurry ((==) @Int)

  -- Play with the "cat equal" trick.
  , runSynCircGold "eq-i" $ toCcc $ (==) @Int

  , runSynCircGold "pow" $ toCcc $ uncurry ((**) @R)

  , runSynCircGold "log" $ toCcc $ log @R

  , runSynCircGold "truncate" $ toCcc $ truncate @R @Int

  , runSynCircGold "cos-2xx" $ toCcc $ \x -> cos (2 * x * x) :: R

  , runSynCircGold "horner" $ toCcc $ horner @R [1, 3, 5]

  , runSynCircGold "xp3y" $ toCcc $ \(x, y) -> x + 3 * y :: R

  , runSynCircGold "cosSinProd" $ toCcc $ cosSinProd @R

  , runSynCircGold "magSqr" $ toCcc $ magSqr @R

  -- -- !! compile failed
  -- , runSynCircGold "complex-mul" $ toCcc $ uncurry ((*) @C)

  , runSynCircGold "sqr" $ toCcc $ sqr @R

  , runSynCircGold "twice" $ toCcc $ twice @R

  , runSynCircGold "fst" $ toCcc $ fst @R @R

  , runSynCircGold "dup" $ toCcc $ A.dup @(->) @R

  , runSynCircGold "add-uncurry" $ toCcc $ uncurry ((+) @R)

  -- -- !! compile timeout
  -- , runSynCircGold "err1Grad-c" $ toCcc $ uncurry $ err1Grad (\ (p,q) z -> p * z + q)

  , runSynCircGold "err1-c" $ toCcc $ \(a, b) -> err1 (\z -> a * z + b)

  , runSynCircGold "err1-b" $ toCcc $ err1 (\z -> 3 * z + 2)

  , runSynCircGold "err1-a" $ toCcc $ uncurry err1

  -- -- !! compile failed
  -- , runSynCircGold "linear" $ toCcc' $ D.linear @(Vector 10) @(Vector 20) @R

  , runSynCircGold "const" $ toCcc' $ A.const @(->) @R @R

  ]

