{-# LANGUAGE CPP                 #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wall #-}

module GoldTests where

import           ConCat.ADFun hiding (D)
import           ConCat.AdditiveFun
import           ConCat.AltCat (toCcc,toCcc',(:**:)(..),Ok2,U2)
import qualified ConCat.AltCat as A
import           ConCat.Circuit (GenBuses,(:>))
import           ConCat.Deep
import           ConCat.Dual
import           ConCat.FFT
import           ConCat.Free.LinearRow
import           ConCat.Free.VectorSpace (HasV(..))
import           ConCat.GAD
import           ConCat.Interval
import           ConCat.Misc ((:*),(:+),R,sqr,magSqr,Unop,Binop,unzip)
import           ConCat.Orphans ()
import           ConCat.RAD
import           ConCat.Rebox ()
import           ConCat.Rep (HasRep(..))
import qualified ConCat.RunCircuit as RC
import           ConCat.Shaped
import           ConCat.Syntactic (Syn,render)
import           Control.Applicative (liftA2)
import           Data.Distributive
import           Data.Finite
import           Data.Functor.Rep
import           Data.Key
import           Data.Pointed
import           Data.Vector.Sized (Vector)
import           GHC.Generics hiding (C,R,D)
import           GHC.TypeLits ()
import           Prelude hiding (unzip,zip,zipWith)


main :: IO ()
main = sequence_
  [ pure ()

  , runSynCirc "foo" $ toCcc $ \ (x :: Int) -> 13 * x == 130

  , runSynCirc "foo" $ toCcc $ (*) @Int

  , runSynCirc "foo" $ toCcc $ div @Int

  , runSynCirc "not-equal-3" $ toCcc $ \ (x :: Int) -> not (x == 3)

  , runSynCirc "unequal-3"   $ toCcc $ \ (x :: Int) -> x /= 3

  -- Int equality turns into matching, which takes some care.
  -- See boxCon/tweak in ConCat.Plugin
  , runSynCirc "equal-3"     $ toCcc $ \ (x :: Int) -> x == 3

  , runSynCirc "sum-fun-8" $ toCcc $ (sum @((->) ((Bool :* Bool) :* Bool)) @Int)

  , runSynCirc "sum-fun-4" $ toCcc $ (sum @((->) (Bool :* Bool)) @Int)

  , runSynCirc "sum-fun-2" $ toCcc $ (sum @((->) Bool) @Int)

  , runSynCirc "app-fun-bool"       $ toCcc $ (<*>)  @((->) Bool) @Int @Int

  , runSynCirc "fmap-fun-bool-plus" $ toCcc $ fmap   @((->) Bool) ((+) @Int)

  , runSynCirc "liftA2-fun-bool"    $ toCcc $ liftA2 @((->) Bool) ((+) @Int)

  , runSynCirc "app-fun-bool"       $ toCcc $ (<*>)  @((->) Bool) @Int @Int

  , runSynCirc "fmap-fun-bool-plus" $ toCcc $ fmap   @((->) Bool) ((+) @Int)

  -- -- !! compile timeout
  -- , runSynCirc "mul-andInc"    $ toCcc $ andInc $ uncurry ((*) @R)

  , runSyn $ toCcc $ \ x -> x - 1 :: R

  , runSyn $ toCcc $ uncurry ((-) @R)

  , runSynCirc "foo" $ toCcc $ \ (x,y) -> sqr (4 - (y + x * 3)) :: R

  , runSynCirc "fmap-cos-adr"       $ toCcc $ andDerR  $ fmap @(Vector 5) @R cos

  , runSynCirc "zip-adr"            $ toCcc $ andDerR  $ uncurry (zip @(Vector 5) @R @R)

  , runSynCirc "sumA-gradr"          $ toCcc $ andGradR $ sumA @(Vector 5) @R

  -- Having trouble with fmap
  , runSyn{-Circ "fmap-cos-adr"-}       $ toCcc $ andDerR  $ fmap @(Vector 5) @R cos

  , runSynCirc "zip-adr"            $ toCcc $ andDerR  $ uncurry (zip @(Vector 5) @R @R)

  , runSynCirc "sumA-adr" $ toCcc $ andDerR $ sumA @(Vector 5) @R

  , runSynCirc "sumA-fad" $ toCcc $ andDeriv @(-+>) $ sumA @(Vector 5) @R

  , runSynCirc "sumA" $ toCcc $ sumA @(Vector 5) @R

  , runSynCirc "sumA-adr" $ toCcc $ andDerR $ sumA @(Vector 5) @R


  , runSynCirc "sumA-adf" $ toCcc $ andDeriv @(->) $ sumA @(Vector 5) @R

  , runSynCirc "dup-gradr"     $ toCcc $ andGrad2R $ A.dup @(->) @R

  , runSynCirc "cos-xpy-gradr" $ toCcc $ andGradR $ \ (x,y) -> cos (x + y) :: R

  , runSynCirc "fst-gradr"     $ toCcc $ andGradR (fst @R @R)

  , runSynCirc "add-gradr"     $ toCcc $ andGradR $ uncurry ((+) @R)

  , runSynCirc "cos-gradr"     $ toCcc $ andGradR $ cos @R

  , runSynCirc "sin-gradr"     $ toCcc $ andGradR $ sin @R

  , runSynCirc "cos-xpy-adr"    $ toCcc $ andDerR $ \ (x,y) -> cos (x + y) :: R

  , runSynCirc "fst-adr"        $ toCcc $ andDerR (fst @R @R)

  , runSynCirc "add-adr"        $ toCcc $ andDerR $ uncurry ((+) @R)

  , runSynCirc "cos-adr"        $ toCcc $ andDerR $ cos @R

  , runSynCirc "sin-adr"        $ toCcc $ andDerR $ sin @R

  , runSyn $ toCcc $ fst @R @R  -- works, but needs optimization

  , runSyn $ toCcc $ A.exl @(->) @R @R

  , runSynCirc "fst-dual" $ toCcc $ toDual $ fst @R @R

  , runSynCirc "fst-af"  $ toCcc $ addFun $ fst @R @R

  , runSynCirc "point-dual" $ toCcc $ toDual $ point @(Vector 5) @R

  , runSynCirc "sumA-dual"  $ toCcc $ toDual $ sumA @(Vector 5) @R

  , runSynCirc "cos-adfl"        $ toCcc $ andDerFL @R $ cos @R

  -- Automatic differentiation with ADFun + linear
  , runSynCirc "sin-adfl"        $ toCcc $ andDerFL @R $ sin @R

  , runSynCirc "cos-adf"        $ toCcc $ andDerF $ cos @R

  -- Automatic differentiation with ADFun:
  , runSynCirc "sin-adf"        $ toCcc $ andDerF $ sin @R

  , runSynCirc "foo9-d"  $ toCcc $ derF (\ (_ :: R) -> 1 :: R)

  , runSynCirc "foo1" $ toCcc $ \ x -> derF (sin @R) x 1

  , runSynCirc "sin-df"        $ toCcc $ derF $ sin @R

  , runCirc "idL-v" $ toCcc (\ () -> idL @(Vector 8) @R) -- ok

  , runCirc "idL-2" $ toCcc (\ () -> idL @(Par1 :*: Par1) @R) -- fail

  , runCirc "equal-sum" $ toCcc $ (==) @(() :+ ())

  , runCirc "equal-Int" $ toCcc $ (==) @Int

  -- -- !! compile timeout
  -- , runSynCirc "horner-iv" $ toCcc $ ivFun $ horner @R [1,3,5]

  -- -- !! compile timeout
  -- , runSynCirc "xyp3-iv"   $ toCcc $ ivFun $ \ (x,y) -> x * y + 3 :: R

  -- -- !! compile timeout
  -- , runSynCirc "magSqr-iv" $ toCcc $ ivFun $ magSqr @Int

  , runSynCirc "sqr-iv"    $ toCcc $ ivFun $ sqr @Int

  , runSynCirc "thrice-iv" $ toCcc $ ivFun $ \ x -> 3 * x :: Int

  -- -- !! compile timeout
  -- , runSynCirc "mul-iv"    $ toCcc $ ivFun $ uncurry ((*) @Int)

  -- Interval analysis
  , runSynCirc "add-iv"    $ toCcc $ ivFun $ uncurry ((+) @Int)

  , runCirc "fft-pair" $ toCcc $ fft @Pair @Double

  -- -- !! compile timeout
  -- , runSynCirc "sum-rb4"    $ toCcc $ sum   @(RBin N4) @Int

  -- Circuit graphs on trees etc
  , runSynCirc "sum-pair"   $ toCcc $ sum   @Pair      @Int

  , runSyn $ toCcc $ sqr @R

  , runCirc "foo" $ toCcc $ unV @R @(Vector 2 R)

  , runSynCirc "linearF-v" $ toCcc $ linearF @R @(Vector 8) @Par1

  -- -- !! compile failed
  -- , runSynCirc "fmap-idL-v" $ toCcc (\ (h :: Vector 8 R -> Vector 8 R) -> h <$> idL)

  , runSynCirc "distribute-v-p" $ toCcc (distribute @Pair @(Vector 4) @R)

  , runSynCirc "distribute-p-v" $ toCcc (distribute @(Vector 4) @Pair @R)

  , runSynCirc "distribute" $ toCcc (A.distributeC :: ((Par1 :*: Par1)) (Vector 4 R) -> (Vector 4) ((Par1 :*: Par1) R))

  , runSynCirc "foo" $ toCcc $ id @(Vector 4 Bool :* Bool)

  , runSynCirc "foo" $ toCcc $ id @((Par1 :*: Par1) (Vector 4 R)) -- hangs genBuses

  , runSynCirc "distribute" $ toCcc (distribute :: (Vector 4) ((Par1 :*: Par1) R) -> ((Par1 :*: Par1)) (Vector 4 R))  -- ok

  , runSynCirc "distribute" $ toCcc (distribute @(Vector 4) @(U1 :*: Par1) @R)

  , runCirc "distribute" $ toCcc (distribute @Pair @Pair @R)

  , runSynCirc "tabulate-v" $ toCcc (tabulate :: (Finite 8 -> Bool) -> Vector 8 Bool)

  , runCirc "point-v"       $ toCcc $ (point :: Bool -> Vector 8 Bool)

  , runSynCirc "fmap-not-v" $ toCcc $ (fmap not :: Unop (Vector 2 Bool))

  , runSynCirc "plus-mul-integer" $ toCcc (\ (x :: Integer, y) -> x * (x + y))

  , runSynCirc "plus-integer"     $ toCcc ((+) @Integer)

  , runSynCirc "ge-integer-b"     $ toCcc (\ (x :: Integer, y) -> not (x < y))

  , runSynCirc "ne-integer-b"     $ toCcc (\ (x :: Integer, y) -> not (x == y))

  , runSynCirc "le-integer"       $ toCcc ((<=) @Integer)

  , runSynCirc "ne-integer"       $ toCcc ((/=) @Integer)

  , runSynCirc "eq-integer"       $ toCcc ((==) @Integer)

  -- -- !! compile timeout
  -- , runSynCirc "zipWith-v" $ toCcc $ zipWith @(Vector 7) (||)


  -- -- !! compile timeout
  -- , runSynCirc "fmap-v-dl" $ toCcc $ derFL @R $ (fmap negate :: Unop (Vector 5 R))

  , runCirc "foo" $ toCcc $ \ (x,y) -> y + x :: R

  , runCirc "foo" $ toCcc $ \ (_x :: R,y :: R) -> y

  -- -- !! compile failed
  -- -- Correct, but more complex/effortful than I'd like. See 2017-12-02 notes.
  -- , runSynCirc "fmapT-oops-b" $ toCcc $ \ (x, v :: Vector 5 R) -> fmap (+x) v

  , runCirc "fmapT" $ toCcc $ \ x (v :: Vector 5 R) -> fmap (+x) v

  , runCirc "fmap-point" $ toCcc $ \ (x :: R) -> fmap negate (point @(Vector 5) x)

  , runCirc "fmap-negate2" $ toCcc $ \ (v :: Vector 5 R) -> fmap negate (fmap (+ 1) v)

  , runSynCirc "fmap-v-d" $ toCcc $ derF (fmap negate :: Unop (Vector 5 R))

  , runSyn $ toCcc $ fmap @(Vector 5) @R (const True)

  , runSynCirc "fmap-v-der-e" $ toCcc $ andDerF $ fmap @(Vector 5) @R negate

  , runCirc "fmap-v-der-e" $ toCcc $ andDerF $ fmap @(Vector 5) @R negate

  , runSyn $ toCcc $ andDerF $ fmap @(Vector 5) @R negate

  -- -- !! compile timeout
  -- , runSynCirc "relu-ad" $ toCcc $ andDerF $ max @R 0

  , runSynCirc "max-ad" $ toCcc $ andDerF $ uncurry (max @R)

  , runSyn $ toCcc $ andDerF $ uncurry (max @R)

  , runSyn $ toCcc $ andDerF $ A.maxC @(->) @R

  , runSyn $ toCcc $ uncurry (max @R)

  , runSynCirc "max" $ toCcc $ uncurry (max @R)

  , runSyn $ toCcc $ derF $ fmap @(Vector 5) @R negate

  , runSynCirc "unzip-b" $ toCcc $ unzip @(Vector 5) @R @R

  -- -- !! compile failed
  -- , runSyn $ toCcc $ (\ (x,xs :: Vector 5 R) -> fmap (+x) xs)

  -- -- !! compile failed
  -- , runCirc "fmap-complex-b" $ toCcc $ (\ (x,xs :: Vector 5 R) -> fmap (+x) xs)

  -- -- !! compile failed
  -- , runSynCirc "fmap-complex-b" $ toCcc $ (\ (x,xs :: Vector 5 R) -> fmap (+x) xs)

  , runSyn $ toCcc' $ fst @Bool @R

  , runSynCirc "fmap-b" $ toCcc $ (fmap negate :: Unop (Vector 5 R))

  , runCirc "fmap-b" $ toCcc $ (fmap negate :: Unop (Vector 5 R))

  , runSyn $ toCcc $ (fmap negate :: Unop (Vector 5 R))

  , runSyn $ toCcc $ (zipWith (*) :: Binop (Vector 5 R))

  , runSynCirc "zipWith-vv" $ toCcc $ uncurry (zipWith (*) :: Binop (Vector 5 R))

  , runSynCirc "foo2" $ toCcc $ uncurry $ \ (x :: R) -> (sin x *)

  -- -- !! compile timeout
  -- , runSynCirc "foo" $ toCcc $ derFL @R $ sin @R

  , runSynCirc "foo1" $ toCcc $ \ (x :: R) -> (sin x *)

  , runSynCirc "add" $ toCcc $ (+) @Integer

  , runSyn{-Circ "equal-pair-b"-} $ toCcc $ uncurry ((==) @(Bool :* Int))

  -- -- !! compile timeout
  -- , runSynCirc "equal-pair-d" $ toCcc $ toCcc $ uncurry ((==) @(Int :* R))

  -- -- !! compile timeout
  -- , runSynCirc "equal-pair-b" $ toCcc $ uncurry ((==) @(Int :* R))

  -- -- !! compile timeout
  -- , runSynCirc "equal-pair-a" $ toCcc $ uncurry ((==) @(Bool :* Int))

  , runCirc "equal-pair-uncurry-b" $ toCcc $ uncurry ((==) @(R :* Int))

  , runCirc "equal-pair-b" $ toCcc $ (==) @(R :* Int)

  , runSyn $ toCcc $ uncurry ((==) @Int)

  -- Play with the "cat equal" trick.
  , runSyn $ toCcc $ (==) @Int

  , runSynCirc "pow" $ toCcc $ uncurry ((**) @R)

  , runSynCirc "log" $ toCcc $ log @R

  , runSynCirc "truncate" $ toCcc $ truncate @R @Int

  , runSynCirc "cos-2xx"     $ toCcc $ \ x -> cos (2 * x * x) :: R

  , runSynCirc "horner"      $ toCcc $ horner @R [1,3,5]

  , runSynCirc "xp3y"        $ toCcc $ \ (x,y) -> x + 3 * y :: R

  , runSynCirc "cosSinProd"  $ toCcc $ cosSinProd @R

  , runSynCirc "magSqr"      $ toCcc $ magSqr @R

  -- -- !! compile failed
  -- , runSynCirc "complex-mul" $ toCcc $ uncurry ((*) @C)

  , runSynCirc "sqr"         $ toCcc $ sqr @R

  , runSynCirc "twice"       $ toCcc $ twice @R

  , runSynCirc "fst"         $ toCcc $ fst @R @R

  , runSynCirc "dup"         $ toCcc $ A.dup @(->) @R

  , runSynCirc "add"         $ toCcc $ uncurry ((+) @R)

  -- -- !! compile timeout
  -- , runCirc "err1Grad-c" $ toCcc $ uncurry $ err1Grad (\ (p,q) z -> p * z + q)

  , runCirc "err1-c" $ toCcc $ \ (a,b) -> err1 (\ z -> a * z + b)

  , runCirc "err1-b" $ toCcc $ err1 (\ z -> 3 * z + 2)

  , runCirc "err1-a" $ toCcc $ uncurry err1

  -- -- !! compile failed
  -- , runCirc "linear" $ toCcc' $ D.linear @(Vector 10) @(Vector 20) @R

  , runCirc "const" $ toCcc' $ A.const @(->) @R @R

  , runSynCirc "sin-adf"        $ toCcc $ andDerF $ sin @R

  ]


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

#if 0

runSolveAsc :: ( GenBuses a, Show a, GenBuses r, Show r, EvalE a, EvalE r
               , OrdCat (:>) r, ConstCat (:>) r )
            => (a :* r :> Bool) -> IO ()
runSolveAsc = mapM_ print . solveAscending

#endif

-- The following definition hangs with infinite lists. More generally, it
-- produces no list output until all of the list elements have been constructed.
-- I'm stumped as to why.

-- runSolveAsc = print . solveAscending

-- runSolveAsc = print <=< solveAscending

#endif

runPrint :: Show b => a -> (a -> b) -> IO ()
runPrint a f = print (f a)

#if 0

runChase :: (HasV R a, Zip (V R a), Eq a, Show a)
         => a -> (a -> a) -> IO ()
runChase a0 f = print (chase 1 f a0)

runCircChase :: (GO a R, HasV R a, Zip (V R a), Eq a, Show a)
             => String -> a -> ((:>) :**: (->)) a a -> IO ()
runCircChase nm a0 (circ :**: f) = runCirc nm circ >> runChase a0 f

#endif


twice :: Num a => a -> a
twice x = x + x

cosSin :: Floating a => a -> a :* a
cosSin a = (cos a, sin a)

cosSinProd :: Floating a => a :* a -> a :* a
cosSinProd (x,y) = cosSin (x * y)

horner :: Num a => [a] -> a -> a
horner []     _ = 0
horner (c:cs) a = c + a * horner cs a


#if 0

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


#endif


data Foo = Foo Double

negateFoo :: Unop Foo
negateFoo (Foo x) = Foo (negate x)

instance HasRep Foo where
  type Rep Foo = R
  abst x = Foo x
  repr (Foo x) = x

