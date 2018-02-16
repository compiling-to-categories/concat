{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
-- {-# OPTIONS_GHC -Wall            #-}

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
import           ConCat.Misc ((:*), (:+), R, C, Unop, Binop, magSqr, sqr, unzip)
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
import           Miscellany hiding (runSynCirc)
import           Prelude hiding (unzip, zip, zipWith)
import           Test.Tasty (TestTree, testGroup)
import           Utils


basicTests :: TestTree
basicTests = testGroup "basic tests"
  [ testGroup "" []

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

  -- Automatic differentiation with ADFun:
  , runSynCirc "sin-adf"        $ toCcc $ andDerF $ sin @R
  , runSynCirc "cos-adf"        $ toCcc $ andDerF $ cos @R
  , runSynCirc "twice-adf"      $ toCcc $ andDerF $ twice @R
  , runSynCirc "sqr-adf"        $ toCcc $ andDerF $ sqr @R
  , runSynCirc "magSqr-adf"     $ toCcc $ andDerF $ magSqr  @R
  , runSynCirc "cos-2x-adf"     $ toCcc $ andDerF $ \ x -> cos (2 * x) :: R
  , runSynCirc "cos-2xx-adf"    $ toCcc $ andDerF $ \ x -> cos (2 * x * x) :: R
  , runSynCirc "cos-xpy-adf"    $ toCcc $ andDerF $ \ (x,y) -> cos (x + y) :: R
  , runSynCirc "cosSinProd-adf" $ toCcc $ andDerF $ cosSinProd @R

  , runSynCirc "times-13" $ toCcc $ \(x :: Int) -> 13 * x == 130

  , runSynCirc "mul-int" $ toCcc $ (*) @Int

  , runSynCirc "div-int" $ toCcc $ div @Int

  , runSynCirc "not-equal-3" $ toCcc $ \(x :: Int) -> not (x == 3)

  , runSynCirc "unequal-3" $ toCcc $ \(x :: Int) -> x /= 3

    -- Int equality turns into matching, which takes some care.
    -- See boxCon/tweak in ConCat.Plugin
  , runSynCirc "equal-3" $ toCcc $ \(x :: Int) -> x == 3

  , runSynCirc "sum-fun-8" $
      toCcc $ (sum @((->) ((Bool :* Bool) :* Bool)) @Int)

  , runSynCirc "sum-fun-4" $ toCcc $ (sum @((->) (Bool :* Bool)) @Int)

  , runSynCirc "sum-fun-2" $ toCcc $ (sum @((->) Bool) @Int)

  , runSynCirc "app-fun-bool" $ toCcc $ (<*>) @((->) Bool) @Int @Int

  , runSynCirc "liftA2-fun-bool" $ toCcc $ liftA2 @((->) Bool) ((+) @Int)

  , runSynCirc "fmap-fun-bool-plus" $ toCcc $ fmap @((->) Bool) ((+) @Int)

  -- -- !! compile failed
  -- , runSynCirc "mul-andInc"    $ toCcc $ andInc $ uncurry ((*) @R)

  , runSynCirc "subtract-1" $ toCcc $ \x -> x - 1 :: R

  , runSynCirc "subtract-uncurry" $ toCcc $ uncurry ((-) @R)

  , runSynCirc "random-math" $ toCcc $ \(x, y) -> sqr (4 - (y + x * 3)) :: R

  , runSynCirc "fmap-cos-adr" $ toCcc $ andDerR $ fmap @(Vector 5) @R cos

  , runSynCirc "zip-adr" $ toCcc $ andDerR $ uncurry (zip @(Vector 5) @R @R)

  , runSynCirc "sumA-gradr" $ toCcc $ andGradR $ sumA @(Vector 5) @R

  , runSynCirc "sumA-adr" $ toCcc $ andDerR $ sumA @(Vector 5) @R

  , runSynCirc "sumA-fad" $ toCcc $ andDeriv @(-+>) $ sumA @(Vector 5) @R

  , runSynCirc "sumA" $ toCcc $ sumA @(Vector 5) @R

  , runSynCirc "sumA-adf" $ toCcc $ andDeriv @(->) $ sumA @(Vector 5) @R

  , runSynCirc "dup-gradr" $ toCcc $ andGrad2R $ A.dup @(->) @R

  , runSynCirc "cos-xpy-gradr" $
      toCcc $ andGradR $ \(x, y) -> cos (x + y) :: R

  , runSynCirc "fst-gradr" $ toCcc $ andGradR (fst @R @R)

  , runSynCirc "add-gradr" $ toCcc $ andGradR $ uncurry ((+) @R)

  , runSynCirc "cos-gradr" $ toCcc $ andGradR $ cos @R

  , runSynCirc "sin-gradr" $ toCcc $ andGradR $ sin @R

  , runSynCirc "cos-xpy-adr" $ toCcc $ andDerR $ \(x, y) -> cos (x + y) :: R

  , runSynCirc "fst-adr" $ toCcc $ andDerR (fst @R @R)

  , runSynCirc "add-adr" $ toCcc $ andDerR $ uncurry ((+) @R)

  , runSynCirc "cos-adr" $ toCcc $ andDerR $ cos @R

  , runSynCirc "sin-adr" $ toCcc $ andDerR $ sin @R

  , runSynCirc "exl" $ toCcc $ A.exl @(->) @R @R

  , runSynCirc "fst-dual" $ toCcc $ toDual $ fst @R @R

  , runSynCirc "fst-af" $ toCcc $ addFun $ fst @R @R

  , runSynCirc "point-dual" $ toCcc $ toDual $ point @(Vector 5) @R

  , runSynCirc "sumA-dual" $ toCcc $ toDual $ sumA @(Vector 5) @R

  , runSynCirc "cos-adfl" $ toCcc $ andDerFL @R $ cos @R

  -- Automatic differentiation with ADFun + linear
  , runSynCirc "sin-adfl" $ toCcc $ andDerFL @R $ sin @R

  , runSynCirc "foo9-d" $ toCcc $ derF (\(_ :: R) -> 1 :: R)

  , runSynCirc "deriv-sin" $ toCcc $ \x -> derF (sin @R) x 1

  , runSynCirc "sin-df" $ toCcc $ derF $ sin @R

  , runSynCirc "idL-v" $ toCcc (\() -> idL @(Vector 8) @R) -- ok

  , runSynCirc "idL-2" $ toCcc (\() -> idL @(Par1 :*: Par1) @R) -- fail

  , runSynCirc "equal-sum" $ toCcc $ (==) @(() :+ ())

  , runSynCirc "equal-Int" $ toCcc $ (==) @Int

  -- -- !! compile failed
  -- , runSynCirc "horner-iv" $ toCcc $ ivFun $ horner @R [1,3,5]

  -- -- !! compile failed
  -- , runSynCirc "xyp3-iv"   $ toCcc $ ivFun $ \ (x,y) -> x * y + 3 :: R

  -- -- !! compile failed
  -- , runSynCirc "magSqr-iv" $ toCcc $ ivFun $ magSqr @Int

  -- -- !! compile failed
  -- , runSynCirc "sqr-iv" $ toCcc $ ivFun $ sqr @Int

  -- -- !! compile failed
  -- , runSynCirc "thrice-iv" $ toCcc $ ivFun $ \x -> 3 * x :: Int

  -- -- !! compile failed
  -- , runSynCirc "mul-iv"    $ toCcc $ ivFun $ uncurry ((*) @Int)

  -- Interval analysis
  , runSynCirc "add-iv" $ toCcc $ ivFun $ uncurry ((+) @Int)

  , runSynCirc "fft-pair" $ toCcc $ fft @Pair @Double

  -- -- !! compile failed
  -- , runSynCirc "sum-rb4"    $ toCcc $ sum   @(RBin N4) @Int

  -- Circuit graphs on trees etc
  , runSynCirc "sum-pair" $ toCcc $ sum @Pair @Int

  , runSynCirc "unV-r-v2" $ toCcc $ unV @R @(Vector 2 R)

  , runSynCirc "linearF-v" $ toCcc $ linearF @R @(Vector 8) @Par1

  , runSynCirc "fmap-idL-v" $ toCcc (\ (h :: Vector 8 R -> Vector 8 R) -> h <$> idL)

  , runSynCirc "distribute-v-p" $ toCcc (distribute @Pair @(Vector 4) @R)

  , runSynCirc "distribute-p-v" $ toCcc (distribute @(Vector 4) @Pair @R)

  , runSynCirc "distribute" $
      toCcc
        (A.distributeC :: ((Par1 :*: Par1)) (Vector 4 R) -> (Vector 4) ((Par1 :*: Par1) R))

  , runSynCirc "foo" $ toCcc $ id @(Vector 4 Bool :* Bool)

  , runSynCirc "id-pair-v" $ toCcc $ id @((Par1 :*: Par1) (Vector 4 R))

  , runSynCirc "distribute-par" $
      toCcc
        (distribute :: (Vector 4) ((Par1 :*: Par1) R) -> ((Par1 :*: Par1)) (Vector 4 R))

  , runSynCirc "distribute-v" $ toCcc (distribute @(Vector 4) @(U1 :*: Par1) @R)

  , runSynCirc "distribute-pair-pair-r" $ toCcc (distribute @Pair @Pair @R)

  , runSynCirc "tabulate-v" $
      toCcc (tabulate :: (Finite 8 -> Bool) -> Vector 8 Bool)

  , runSynCirc "point-v" $ toCcc $ (point :: Bool -> Vector 8 Bool)

  , runSynCirc "fmap-not-v" $ toCcc $ (fmap not :: Unop (Vector 2 Bool))

  , runSynCirc "plus-mul-integer" $ toCcc (\(x :: Integer, y) -> x * (x + y))

  , runSynCirc "plus-integer" $ toCcc ((+) @Integer)

  , runSynCirc "ge-integer-b" $ toCcc (\(x :: Integer, y) -> not (x < y))

  , runSynCirc "ne-integer-b" $ toCcc (\(x :: Integer, y) -> not (x == y))

  , runSynCirc "le-integer" $ toCcc ((<=) @Integer)

  , runSynCirc "ne-integer" $ toCcc ((/=) @Integer)

  , runSynCirc "eq-integer" $ toCcc ((==) @Integer)

  , runSynCirc "zipWith-v" $ toCcc $ zipWith @(Vector 7) (||)

  -- -- !! compile timeout
  -- , runSynCirc "fmap-v-dl" $ toCcc $ derFL @R $ (fmap negate :: Unop (Vector 5 R))

  , runSynCirc "y-plus-x" $ toCcc $ \(x, y) -> y + x :: R

  , runSynCirc "const-y" $ toCcc $ \(_x :: R, y :: R) -> y

  -- Correct, but more complex/effortful than I'd like. See 2017-12-02 notes.
  , runSynCirc "fmapT-oops-b" $ toCcc $ \ (x, v :: Vector 5 R) -> fmap (+x) v

  , runSynCirc "fmapT" $ toCcc $ \x (v :: Vector 5 R) -> fmap (+ x) v

  , runSynCirc "fmap-point" $
      toCcc $ \(x :: R) -> fmap negate (point @(Vector 5) x)

  , runSynCirc "fmap-negate2" $
      toCcc $ \(v :: Vector 5 R) -> fmap negate (fmap (+ 1) v)

  , runSynCirc "fmap-v-d" $ toCcc $ derF (fmap negate :: Unop (Vector 5 R))

  , runSynCirc "fmap-r-const" $ toCcc $ fmap @(Vector 5) @R (const True)

  , runSynCirc "fmap-v-der-e" $ toCcc $ andDerF $ fmap @(Vector 5) @R negate

  -- -- !! compile timeout
  -- , runSynCirc "relu-ad" $ toCcc $ andDerF $ max @R 0

  -- -- !! compile timeout
  -- , runSynCirc "max-ad" $ toCcc $ andDerF $ uncurry (max @R)

  , runSynCirc "maxC-der" $ toCcc $ andDerF $ A.maxC @(->) @R

  , runSynCirc "max" $ toCcc $ uncurry (max @R)

  , runSynCirc "negate-derF" $ toCcc $ derF $ fmap @(Vector 5) @R negate

  , runSynCirc "unzip-b" $ toCcc $ unzip @(Vector 5) @R @R

  -- -- !! compile failed
  -- , runSynCirc $ toCcc $ (\ (x,xs :: Vector 5 R) -> fmap (+x) xs)

  , runSynCirc "fmap-complex-b" $ toCcc $ (\ (x,xs :: Vector 5 R) -> fmap (+x) xs)

  , runSynCirc "fst-bool-r" $ toCcc' $ fst @Bool @R

  , runSynCirc "fmap-b" $ toCcc $ (fmap negate :: Unop (Vector 5 R))

  , runSynCirc "fmap-negate-unop" $ toCcc $ (fmap negate :: Unop (Vector 5 R))

  , runSynCirc "zipWith-mult-v" $ toCcc $ (zipWith (*) :: Binop (Vector 5 R))

  , runSynCirc "zipWith-vv" $
      toCcc $ uncurry (zipWith (*) :: Binop (Vector 5 R))

  , runSynCirc "foo2" $ toCcc $ uncurry $ \(x :: R) -> (sin x *)

  , runSynCirc "der-sin" $ toCcc $ derFL @R $ sin @R

  , runSynCirc "mul-sin" $ toCcc $ \(x :: R) -> (sin x *)

  , runSynCirc "equal-pair-b" $ toCcc $ uncurry ((==) @(Bool :* Int))

  , runSynCirc "equal-pair-d" $ toCcc $ toCcc $ uncurry ((==) @(Int :* R))

  , runSynCirc "equal-pair-b" $ toCcc $ uncurry ((==) @(Int :* R))

  , runSynCirc "equal-pair-a" $ toCcc $ uncurry ((==) @(Bool :* Int))

  , runSynCirc "equal-pair-uncurry-b" $ toCcc $ uncurry ((==) @(R :* Int))

  , runSynCirc "equal-pair-curried-b" $ toCcc $ (==) @(R :* Int)

  , runSynCirc "uncurry-eq-i" $ toCcc $ uncurry ((==) @Int)

  -- Play with the "cat equal" trick.
  , runSynCirc "eq-i" $ toCcc $ (==) @Int

  -- -- !! compile timeout
  -- , runSynCirc "err1Grad-c" $ toCcc $ uncurry $ err1Grad (\ (p,q) z -> p * z + q)

  , runSynCirc "err1-c" $ toCcc $ \(a, b) -> err1 (\z -> a * z + b)

  , runSynCirc "err1-b" $ toCcc $ err1 (\z -> 3 * z + 2)

  , runSynCirc "err1-a" $ toCcc $ uncurry err1

  -- -- !! compile failed
  -- , runSynCirc "linear" $ toCcc' $ D.linear @(Vector 10) @(Vector 20) @R

  , runSynCirc "const" $ toCcc' $ A.const @(->) @R @R

  ]

