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

-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:maxSteps=50 #-}

-- {-# OPTIONS_GHC -fplugin-opt=ConCat.Plugin:showCcc #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}
-- {-# OPTIONS_GHC -dverbose-core2core #-}

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}
-- {-# OPTIONS_GHC -ddump-rules #-}

-- Does this flag make any difference?
-- {-# OPTIONS_GHC -fexpose-all-unfoldings #-}

-- Tweak simpl-tick-factor from default of 100
-- {-# OPTIONS_GHC -fsimpl-tick-factor=2500 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=500 #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=250 #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=25  #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=5  #-}

-- {-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

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

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed
import Data.Key
import Data.Distributive
import Data.Functor.Rep
import Data.Finite
import Data.Vector.Sized (Vector)
import qualified Data.Vector.Sized as VS

import ConCat.Misc
  ((:*),(:+),R,result,sqr,magSqr,Unop,Binop,unzip,inNew,inNew2,Yes1,oops,type (&+&),PseudoFun(..))
import ConCat.Rep (HasRep(..))
import qualified ConCat.Category as C
import ConCat.Incremental (andInc,inc)
import ConCat.Dual
import ConCat.GAD
import ConCat.AdditiveFun
import ConCat.AD
import ConCat.ADFun hiding (D)
-- import qualified ConCat.ADFun as ADFun
import ConCat.RAD
import ConCat.Free.VectorSpace (HasV(..),distSqr,(<.>),normalizeV)
import ConCat.GradientDescent
import ConCat.Interval
import ConCat.Syntactic (Syn,render)
import ConCat.Circuit (GenBuses,(:>))
import qualified ConCat.RunCircuit as RC
import qualified ConCat.AltCat as A
-- import ConCat.AltCat
import ConCat.AltCat
  (toCcc,toCcc',unCcc,unCcc',reveal,conceal,(:**:)(..),Ok,Ok2,U2,equal)
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

import Control.Newtype (Newtype(..))

-- Experiments
import GHC.Exts (Coercible,coerce)

import Test.Tasty (defaultMain)
import GoldTests (basicTests)

-- default (Int, Double)

type C = Complex R

main :: IO ()
main = sequence_
  [ putChar '\n' -- return ()

  , defaultMain basicTests

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "jamPF" $ toCcc $ A.jamPF @(->) @(Finite 10) @R

  -- -- !! 2018-02-10: run failed
  -- , runCirc "curry1-adf" $ toCcc' $ andDerF' $ (*) @R

  -- -- !! 2018-02-10: run failed
  -- , runCirc "curry2-adf" $ toCcc' $ andDerF' $ \ (a :: Vector 10 R) b -> fmap (+ b) a

  -- , runCirc "err1-d" $ toCcc $ \ ab (p,q) -> err1 (\ z -> p * z + q) ab

  -- -- !! 2018-02-10: compile timeout
  -- , runCirc "err1Grad-a" $ toCcc $ \ ab -> gradR (\ (p,q) -> err1 (\ z -> p * z + q) ab)

  -- -- !! 2018-02-10: compile timeout
  -- , runCirc "err1Grad-b" $ toCcc $ err1Grad (\ (p,q) z -> p * z + q)

  -- , runCirc "dot" $ toCcc $ D.dotV @(Vector 3) @R

  -- , runCirc "dot-unc"       $ toCcc $            uncurry $ D.dotV @(Vector 3) @R
  -- , runCirc "dot-unc-adr"   $ toCcc $ andDerR  $ uncurry $ D.dotV @(Vector 3) @R
  -- , runCirc "dot-unc-gradr" $ toCcc $ andGradR $ uncurry $ D.dotV @(Vector 3) @R

  -- , runSynCirc "dot-u-adr" $ toCcc $ andDerR . D.dotV @(Vector 3) @R
  -- , runSynCirc "dot-u-gradr" $ toCcc $ andGradR . D.dotV @(Vector 3) @R

  -- , runCirc "linear" $ toCcc $ D.linear @(Vector 2) @(Vector 3) @R

  -- , runCirc "linear-adf"   $ toCcc $ andDerF  . D.linear @(Vector 2) @(Vector 3) @R
  -- , runCirc "linear-adr"   $ toCcc $ andDerR  . D.linear @(Vector 2) @(Vector 3) @R
  -- , runCirc "linear-gradr" $ toCcc $ andGradR . D.linear @(Vector 2) @(Vector 3) @R

  -- , runCirc "affine"       $ toCcc $            D.affine @(Vector 2) @(Vector 3) @R
  -- , runCirc "affine-adf"   $ toCcc $ andDerF  . D.affine @(Vector 2) @(Vector 3) @R
  -- , runCirc "affine-adr"   $ toCcc $ andDerR  . D.affine @(Vector 2) @(Vector 3) @R
  -- , runCirc "affine-gradr" $ toCcc $ andGradR . D.affine @(Vector 2) @(Vector 3) @R

  -- , runCirc "relu"  $ toCcc $ max @R 0
  -- , runCirc "relus" $ toCcc $ relus @(Vector 3) @R

  -- , runSynCirc "max" $ toCcc $ uncurry (max @R)

  -- , runSynCirc "max-adr-b" $ toCcc $ andDerR $ uncurry (max @R)

  -- , runSynCirc "relu-adr" $ toCcc $ andDerR $ max @R 0

  -- , runSynCirc "relu-gradr" $ toCcc $ andGradR $ max @R 0

  -- , runSynCirc "relus-adr" $ toCcc $ andDerR $ relus @(Vector 3) @R
  -- , runSynCirc "relus-gradr" $ toCcc $ andGradR $ relus @(Vector 3) @R

  -- , runCirc "affRelu"       $ toCcc $            D.affRelu @(Vector 2) @(Vector 3) @R
  -- , runCirc "affRelu-adf"   $ toCcc $ andDerF  . D.affRelu @(Vector 2) @(Vector 3) @R
  -- , runCirc "affRelu-adr"   $ toCcc $ andDerR  . D.affRelu @(Vector 2) @(Vector 3) @R
  -- , runCirc "affRelu-gradr" $ toCcc $ andGradR . D.affRelu @(Vector 2) @(Vector 3) @R

  -- , runCirc "linear-err" $ toCcc $ errSqrSampled (D.linear @(Vector 2) @(Vector 3) @R)
  -- , runCirc "linear-err-adf" $ toCcc $ andDerF . errSqrSampled (D.linear @(Vector 2) @(Vector 3) @R)
  -- , runCirc "linear-err-adr" $ toCcc $ andDerR . errSqrSampled (D.linear @(Vector 2) @(Vector 3) @R)

  -- , runCirc "linear-errGrad" $ toCcc $ errGrad (D.linear @(Vector 2) @(Vector 3) @R)
  -- , runCirc "affine-errGrad" $ toCcc $ errGrad (D.affine @(Vector 2) @(Vector 3) @R)
  -- , runCirc "affRelu-errGrad" $ toCcc $ errGrad (affRelu @(Vector 2) @(Vector 3) @R)

  -- , runCirc "affRelu-errGrad" $ toCcc $ errGrad (lr1 @(Vector 2) @(Vector 3))

  -- , runSynCirc "not-adf-b" $ toCcc $ andDerF not
  -- , runSynCirc "not-adr-b" $ toCcc $ andDerR not

  -- , runSynCirc "not-gradr" $ toCcc $ andGradR not -- nope. Bool not a Num

  -- , runCirc "affRelu1" $ toCcc $ lr1 @(Vector 2) @(Vector 3) @(Vector 5)

  -- , runCirc "affRelu2" $ toCcc $ lr2 @(Vector 2) @(Vector 3) @(Vector 5)

  -- , runCirc "affRelu2-errGrad" $ toCcc $ errGrad (lr2 @(Vector 2) @(Vector 3) @(Vector 5))

  -- , runCirc "normalize" $ toCcc $ normalize @(Vector 5) @R
  -- , runCirc "normalize-adf" $ toCcc $ andDerF $ normalize @(Vector 5) @R
  -- , runCirc "normalize-adr" $ toCcc $ andDerR $ normalize @(Vector 5) @R
  -- , runCirc "normalize-gradr" $ toCcc $ andGradR $ normalize @(Vector 5) @R

  -- , runCirc "linear-err-gradr" $ toCcc $ errGrad (D.linear @(Vector 2) @(Vector 3) @R)

  -- , runCirc "lin1-b" $ toCcc $ \ ab -> errSqr ab . D.linear @(Vector 10) @(Vector 20) @R

  -- , runCirc "elr1-b" $ toCcc $ \ ab -> gradR (errSqr ab . D.linear @(Vector 10) @(Vector 20) @R)

  -- , runCirc "elr2-b" $ toCcc $ \ (ab :: Vector 5 R) -> gradR (dotV ab) -- breaks

  -- , runCirc "elr2-c" $ toCcc' $ \ (ab :: Vector 5 R) -> andDerR (dotV ab)

  -- , runCirc "elr2-d" $ toCcc' $ \ (ab :: Vector 5 R) -> unD $ toCcc' @RAD $ dotV ab

  -- , runCirc "elr3-b" $ toCcc $ gradR (sumA @(Vector 5) @R) --

  -- , runCirc "dual-a" $ toCcc $ A.reprC $ toDual @(-+>) (sumA @(Vector 5) @R)

  -- , runCirc "dual-b" $ toCcc $ unAddFun $ toDual @(-+>) (sumA @(Vector 5) @R)

  -- -- !! 2018-02-10: compile timeout
  -- , runCirc "elr1" $ toCcc $ errGrad (D.linear @(Vector 10) @(Vector 20) @R)

  -- -- Circuit graphs

  -- -- Try sized vector operations directly.
  -- -- !! 2018-02-10: run failed
  -- , runSyn $ toCcc $ VS.sum @R @4

  -- -- Choice

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-add" . toCcc)
  --     (toCcc (choose @GenBuses ((+) @R)))

  -- -- This one fails with Ok (:>) vs GenBuses preventing toCcc'/unCcc'
  -- -- !! 2018-02-10: compile failed
  -- , onChoice @(Ok (:>)) (runCirc "choice-add" . toCcc)
  --     (toCcc (choose @(Ok (:>)) ((+) @R)))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @OkLC (runCirc "choice-add" . toCcc)
  --     (toCcc (choose @OkLC ((+) @R)))

  -- -- This one breaks. Seems to be GenBuses vs Ok (:>) in toCcc'/unCcc'.
  -- -- Bug in GHC's handling of rewrite rules?
  -- -- !! 2018-02-10: compile failed
  -- , onChoice @(Ok (:>)) (runCirc "choice-add" . toCcc)
  --     (toCcc (choose @(Ok (:>)) ((+) @R)))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-foo" . toCcc)
  --     (toCcc (choose @GenBuses (\ b x -> x + b :: R)))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @(Ok (:>)) (runCirc "choice-foo" . toCcc)
  --     (toCcc (choose @(Ok (:>)) (\ b x -> x + b :: R)))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-line" . toCcc)
  --     (toCcc (choose @GenBuses (\ (m,b) x -> m * x + b :: R)))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-line" . toCcc)
  --     (toCcc (choose @GenBuses line))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-line-lam" . toCcc)
  --     (toCcc (\ x -> choose @GenBuses line x))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-line-2x" . toCcc)
  --     (toCcc (\ x -> choose @GenBuses line (2 * x)))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-line-lam-2" . toCcc)
  --     (toCcc (\ x -> choose @GenBuses line (choose @GenBuses line x)))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-line-sin-line-a" . toCcc)
  --     (toCcc (\ x -> choose @GenBuses line (sin (choose @GenBuses line x))))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-line-sin-line-b" . toCcc)
  --     (toCcc (choose @GenBuses line . sin . choose @GenBuses line))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @OkLC (runCirc "choice-line" . toCcc)
  --     (toCcc (choose @OkLC line))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "foo" $ toCcc (step @R line)  -- Loops

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "distSqr-v" $ toCcc $ distSqr @R @(Vector 5)

  -- -- !! 2018-02-10: run failed
  -- , runSynCirc "sqErr-vv" $ toCcc $ R.sqErr @R @(Vector 5 R) @(Vector 11 R)

  -- -- !! 2018-02-10: run failed
  -- , runCirc "sqErrF-vv" $ toCcc $ R.sqErrF @R @(Vector 5 R) @(Vector 11)

  -- -- !! 2018-02-10: run failed
  -- , runSynCirc "sqErrF-uncurry-vv-c" $ toCcc $ uncurry (R.sqErrF @R @(Vector 5 R) @(Vector 11))

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sqErrF-der-a" $ toCcc $ \ sample -> andDerF $ \ aff ->
  --     R.sqErrF @R @(Vector 5 R) @(Vector 11) (applyA @R aff) sample

  -- $s$*_sl5c :: (:-*) (V R (Vector 5 R)) (V R (Vector 11 R)) R
  --              -> V R (Vector 5 R) R -> V R (Vector 11 R) R

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "dot-vv" $ toCcc $ (<.>) @R @(Vector 5)

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "sum-vv" $ toCcc $ sum @(Vector 5) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-vv-der" $ toCcc $ andDerF $ sum @(Vector 5) @R

  -- -- !! 2018-02-10: run failed
  -- , runCirc "zipWith-vv-adf" $ toCcc $ andDerF $ (zipWith (*) :: Binop (Vector 5 R))

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "zipWithC-vv-der" $ toCcc $ andDerF $ (A.zipWithC A.mulC :: Vector 5 R :* Vector 5 R -> Vector 5 R)

  -- -- !! 2018-02-10: run failed
  -- , runSynCirc "normalize" $ toCcc $ normalizeV @(Vector 5) @R

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "fmapC-v-der-b" $ toCcc $ andDerF $ (A.fmapC :: Unop R -> Unop (Vector 5 R))

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "dot-vv-der" $ toCcc $ andDerF $ (<.>) @R @(Vector 5)

  -- -- !! 2018-02-10: compile timeout
  -- , runCirc "foo" $ toCcc $ andDerF $ A.uncurry (A.fmapC :: Unop R -> Unop (Par1 R))

  -- -- !! 2018-02-10: run failed
  -- , runCirc "lapply-vv" $ toCcc $ ($*) @R @(Vector 5) @(Vector 11)

  -- -- !! 2018-02-10: run failed
  -- , runCirc "lapply-vv-der" $ toCcc $ andDerF $ ($*) @R @(Vector 5) @(Vector 11)

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sqErrF-der-b" $ toCcc $
  --     \ (sample :: Vector 5 R :* Vector 11 R) -> andDerF $ \ aff ->
  --        R.sqErrF (applyA @R aff) sample

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "foo-der" $ toCcc $
  --     \ (v :: Par1 R) ->
  --       derF (distSqr v)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sqErrF-der-pp" $ toCcc $
  --     \ (ab :: Par1 R :* Par1 R) ->
  --       derF (R.sqErrF @R ab . applyA @R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sqErr-der-pp" $ toCcc $
  --     \ (ab :: Par1 R :* Par1 R) ->
  --       derF (R.sqErr @R ab . applyA @R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sqErr-der-vv" $ toCcc $
  --     \ (ab :: Vector 5 R :* Vector 11 R) ->
  --       derF (R.sqErr @R ab . applyA @R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sqErr-vv-c" $ toCcc $
  --     \ (ab :: Vector 5 R :* Vector 11 R) ->
  --       (R.sqErr @R ab . applyA @R)

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "applyA-vv" $ toCcc $
  --       applyA @R @(Vector 5 R) @(Vector 11 R)

  -- -- !! 2018-02-10: compile failed
  -- -- 50 sec with AD; 11 sec with ADFun.
  -- , onChoice @OkLFC (\ f -> runCirc "regress-line" (toCcc (step @R f)))
  --     (toCcc (choose @OkLFC line))

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "regress-line-d" $ toCcc $ \ ab p -> sqErr @R ab (line p)

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @OkLC (runCirc "choice-add" . toCcc)
  --     (toCcc (choose @OkLC ((+) @R)))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @GenBuses (runCirc "choice-line" . toCcc)
  --     (toCcc (choose @GenBuses line))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @OkLC (\ f -> runCirc "regress-line-a"
  --                    (toCcc (\ ab p -> sqErr @R ab (f p))))
  --     (toCcc (choose @OkLC line))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @OkLC (\ f -> runCirc "regress-line-b" $ toCcc $
  --                     \ ab -> negateV (gradient (sqErr @R ab . f)))
  --     (toCcc (choose @OkLC line))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @OkLC (\ f -> runCirc "bar3" $ toCcc $
  --                     \ ab -> derF (sqErr @R ab . f))
  --     (toCcc (choose @OkLC line))

  -- -- !! 2018-02-10: compile failed
  -- , onChoice @OkLFC (\ f -> runCirc "regress-line-df" $ toCcc $
  --                     \ ab -> derF (negate . sqErr @R ab . f))
  --     (toCcc (choose @OkLFC line))

  -- -- !! 2018-02-10: compile failed
  -- -- 12 sec
  -- , onChoice @OkLFC (\ f -> runCirc "regress-line-gf" $ toCcc $
  --                     \ ab -> gradF @R (negate . sqErr ab . f))
  --     (toCcc (choose @OkLFC line))

  -- -- !! 2018-02-10: run failed
  -- , oops "Hrmph" (toCcc (choose @GenBuses (||)) :: Choice GenBuses Bool Bool)

  -- -- Integer

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "sum-v"         $ toCcc $ (sum :: Vector 8 Int -> Int)

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "sum-point-v"   $ toCcc $ (sum . (point :: Int -> Vector 8 Int))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "linear-v-1" $ toCcc $ linear @R @(Vector 8 R) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "linear-v-2" $ toCcc $ linear @R @(Vector 8 R) @(R :* R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "linear-1-v" $ toCcc $ linear @R @R @(Vector 8 R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "linear-2-v" $ toCcc $ linear @R @(R :* R) @(Vector 8 R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-v-adf" $ toCcc $ andDerF (sumAC :: Vector 8 R -> R)

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "sum-v-adfl" $ toCcc $ andDerFL @R (sumAC :: Vector 8 R -> R)

  -- -- !! 2018-02-10: run failed
  -- , runCirc "foo" $ toCcc $ \ () -> dualV (\ (x,y,z) -> x + y + z :: R) -- fail

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "foo" $ toCcc $ \ () -> dualV (sumAC :: Pair R -> R) -- ok

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "foo" $ toCcc $ \ () -> dualV4 (sumAC :: Vector Bool R -> R) -- fail

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "foo" $ toCcc $ \ () -> diag @(Vector Bool) @R  -- OK

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "foo" $ toCcc $ fmapC @(->) @(Vector Bool) @R @R -- OK

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "foo" $ toCcc $ (sumAC :: Vector Bool R -> R) -- OK

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "foo" $ toCcc $ (dualV @R @(Vector Bool R)) --

  -- -- !! 2018-02-10: compile failed
  -- , runSyn $ toCcc $ \ () -> dualV (sumAC :: Vector Bool R -> R) -- Ok

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "dual-sum-pair" $ toCcc $ \ () -> dualV (sumAC :: Pair R -> R)

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "dual-sum-par1" $ toCcc $ \ () -> dualV (sumAC :: Par1 R -> R)

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "dual-sum-arr" $ toCcc $ \ () -> dualV (sumAC :: Vector Bool R -> R)

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "dual-sum-arr-unit" $ toCcc $ \ () -> dualV (sumAC :: Vector () R -> R)

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "foo" $ toCcc $ \ () -> dualV (sumAC :: Vector Bool R -> R)

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "sum-arr-v3-adf" $ toCcc $ andDerF (sumAC :: Vector (RVec N3 Bool) R -> R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-v3-adfl" $ toCcc $ andDerFL' @R (sumAC :: Vector (RVec N3 Bool) R -> R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fmapC-id-arr" $ toCcc $ (fmapC id :: Unop (Vector Bool R))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fmap-not" $ toCcc $ (fmapC not :: Unop (Pair Bool))

  -- -- !! 2018-02-10: compile failed
  -- , runSyn $ toCcc $ (fmapC sqr :: Unop (Pair R))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fmap-par1-sqr-adf"  $ toCcc $ andDerF (fmap  sqr :: Unop (Par1 R))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fmapC-par1-sqr-adf" $ toCcc $ andDerF (fmapC sqr :: Unop (Par1 R))

  -- -- !! 2018-02-10: compile failed
  -- , runSyn{-Circ "fmapC-pair-sqr-adf"-} $ toCcc $ andDerF (fmapC sqr :: Unop (Pair R))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fmapC-pair-sqr-adf" $ toCcc $ andDerF (fmapC sqr :: Unop (Pair R))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fmapC-pair-sqr-adf" $ toCcc $ andDerF (fmapC sqr :: Unop (Pair R))

  -- -- !! 2018-02-10: compile failed
  -- , runSyn $ toCcc $ andDer @R (fmapC sqr :: Unop (Pair R))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "lsums-pair" $ toCcc $ lsums @Pair      @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "lsums-rb2"  $ toCcc $ lsums @(RBin N2) @Int

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "lsums-rb3"  $ toCcc $ lsums @(RBin N3) @Int

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "lsums-rb4"  $ toCcc $ lsums @(RBin N4) @Int

  -- -- !! 2018-02-10: run failed
  -- , runCirc "fft-rb1"  $ toCcc $ fft @(RBin N1) @Double

  -- -- !! 2018-02-10: compile timeout
  -- , runCirc "fft-rb2"  $ toCcc $ fft @(RBin N2) @Double

  -- -- !! 2018-02-10: compile timeout
  -- , runCirc "fft-rb3"  $ toCcc $ fft @(RBin N3) @Double

  -- -- !! 2018-02-10: compile timeout
  -- , runCirc "fft-rb4"  $ toCcc $ fft @(RBin N4) @Double

  -- -- !! 2018-02-10: compile timeout
  -- , runCirc "foo" $ toCcc $ \ ( fc :: ( (Pair :.: Pair) (Complex Double) )) -> fft fc

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "xp3y-iv"   $ toCcc $ ivFun $ \ ((x,y) :: R2) -> x + 3 * y

  -- -- Automatic differentiation
  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sin-ad"        $ toCcc $ andDer @R @R $ sin    @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-ad"        $ toCcc $ andDer @R @R $ cos    @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "twice-ad"      $ toCcc $ andDer @R @R $ twice  @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sqr-ad"        $ toCcc $ andDer @R $ sqr    @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "magSqr-ad"     $ toCcc $ andDer @R $ magSqr @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-2x-ad"     $ toCcc $ andDer @R $ \ x -> cos (2 * x) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-2xx-ad"    $ toCcc $ andDer @R $ \ x -> cos (2 * x * x) :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "cos-xpy-ad"    $ toCcc $ andDer @R $ \ (x,y) -> cos (x + y) :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "cosSinProd-ad" $ toCcc $ andDer @R $ cosSinProd @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-pair-ad"     $ toCcc $ andDer @R $ sum @Pair @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "product-pair-ad" $ toCcc $ andDer @R $ product @Pair @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sum-2-ad"$ toCcc $ andDer @R $ \ (a,b) -> a+b :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sum-3-ad"$ toCcc $ andDer @R $ \ (a,b,c) -> a+b+c :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "product-3-ad"$ toCcc $ andDer @R $ \ (a,b,c) -> a*b*c :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "product-4-ad"$ toCcc $ andDer @R $ \ (a,b,c,d) -> a*b*c*d :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sum-4-ad"$ toCcc $ andDer @R $ \ (a,b,c,d) -> a+b+c+d :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sum-rb2-ad"$ toCcc $ andDer @R $ sum @(RBin N2) @R

  -- -- !! 2018-02-10: compile failed
  -- , print $ andDer @R sin (1 :: R)

  -- -- Linear
  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "linear-r-r"   $ toCcc $ linear @R @R @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "linear-r2-r"  $ toCcc $ linear @R @(R :* R) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "linear-r-r2"  $ toCcc $ linear @R @R @(R :* R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "linear-r2-r2" $ toCcc $ linear @R @(R :* R) @(R :* R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "diag-2" $ toCcc $ diag @(Par1 :*: Par1) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "tabulate2" $ toCcc $ tabulateC @(->) @(Par1 :*: Par1) @R  -- fail

  -- -- !! 2018-02-10: run failed
  -- , runCirc "equal-v" $ toCcc $ (==) @(Vector 5 Int)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "linear-v-r" $ toCcc $ linear @R @(Vector 4 R) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "distribute-1-4" $ toCcc $ distributeC @(->) @(V R R) @(V R (Vector 4 R)) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "distribute-4-1" $ toCcc $ distributeC @(->) @(V R (Vector 4 R)) @(V R R) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "distribute-1-4" $ toCcc $ (distributeC :: V R R (V R (Vector 4 R) R) -> V R (Vector 4 R) (V R R R))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "foo2" $ toCcc $ derF (\ x -> derF (sin @R) x 1)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sin-d"  $ toCcc $ d (sin @R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-d"  $ toCcc $ d (cos @R)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sin-dd" $ toCcc $ d (d (sin @R))

  -- -- !! 2018-02-10: compile failed
  -- -- Working here
  -- , runSynCirc "dd2" $ toCcc $ d (\x -> d (x +) 2)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "dd-ok" $ toCcc $ \ x -> x * d (x *) 2


  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "dd3" $ toCcc $ d (\x -> x * d (\ y -> y * x) 2)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "twice-adf"      $ toCcc $ andDerF $ twice @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sqr-adf"        $ toCcc $ andDerF $ sqr @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "magSqr-adf"     $ toCcc $ andDerF $ magSqr  @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-2x-adf"     $ toCcc $ andDerF $ \ x -> cos (2 * x) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-2xx-adf"    $ toCcc $ andDerF $ \ x -> cos (2 * x * x) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-xpy-adf"    $ toCcc $ andDerF $ \ (x,y) -> cos (x + y) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cosSinProd-adf" $ toCcc $ andDerF $ cosSinProd @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "product-4-adf"$ toCcc $ andDerF $ \ (a,b,c,d) -> a*b*c*d :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sum-rb3-adf"$ toCcc $ andDerF $ sum @(RBin N3) @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "product-rb3-adf"$ toCcc $ andDerF $ product @(RBin N3) @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sqr-adfl"        $ toCcc $ andDerFL @R $ sqr @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "magSqr-adfl"     $ toCcc $ andDerFL @R $ magSqr @R -- breaks

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "cos-2x-adfl"     $ toCcc $ andDerFL @R $ \ x -> cos (2 * x) :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "cos-2xx-adfl"    $ toCcc $ andDerFL @R $ \ x -> cos (2 * x * x) :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "cos-xpy-adfl"    $ toCcc $ andDerFL @R $ \ (x,y) -> cos (x + y) :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "cosSinProd-adfl" $ toCcc $ andDerFL @R $ cosSinProd @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "product-4-adfl"$ toCcc $ andDerFL @R $ \ (a,b,c,d) -> a*b*c*d :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "product-rb3-adf"$ toCcc $ andDerF $ product @(RBin N3) @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "product-rb3-adfl"$ toCcc $ andDerFL @R $ product @(RBin N3) @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDerFL @R $ product @(RBin N4) @R

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDerF $ product @(RBin N4) @R

  -- -- !! 2018-02-10: run failed
  -- , runSynCirc "zip-dual"   $ toCcc $ toDual $ uncurry $ zip @(Vector 3) @R @Bool

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "ixSum-n-a" $ toCcc $ ixSum @(Finite 5) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "ixSum-n" $ toCcc $ addFun $ ixSum @(Finite 5) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "ixSum-n-b" $ toCcc $ addFun' $ ixSum @(Finite 5) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSyn{-Circ "ixSum-n-c"-} $ toCcc $ ixSum @(Finite 5) @R

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "ixSum-n-d" $ toCcc $ ixSum @(Finite 5) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "ixSum-n-e" $ toCcc $ ixSum @(Finite 5) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "jamPF-n" $ toCcc $ A.jamPF @(Finite 5) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fst-daf" $ toCcc $ dadFun $ fst @R @R

  -- -- Automatic differentiation with RAD:

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "dup-adr"        $ toCcc $ andDerR $ A.dup @(->) @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "twice-adr"      $ toCcc $ andDerR $ twice @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sqr-adr"        $ toCcc $ andDerR $ sqr @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "magSqr-adr"     $ toCcc $ andDerR $ magSqr @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-2x-adr"     $ toCcc $ andDerR $ \ x -> cos (2 * x) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-2xx-adr"    $ toCcc $ andDerR $ \ x -> cos (2 * x * x) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cosSinProd-adr" $ toCcc $ andDerR $ cosSinProd @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "twice-gradr"   $ toCcc $ andGradR $ twice @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sqr-gradr"     $ toCcc $ andGradR $ sqr @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "magSqr-gradr"  $ toCcc $ andGradR $ magSqr  @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-2x-gradr"  $ toCcc $ andGradR $ \ x -> cos (2 * x) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cos-2xx-gradr" $ toCcc $ andGradR $ \ x -> cos (2 * x * x) :: R

  -- -- Yikes! Needs simplification, at least.
  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "cosSinProd-adrl" $ toCcc $ andDerRL @R $ cosSinProd @R

  -- -- Temp hack
  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "cosSinProd-adrl" $ toCcc $ andGrad2R @R $ cosSinProd @R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-fmap-cos-gradr" $ toCcc $ andGradR $ sum . fmap @(Vector 5) @R cos

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-fmap-cos-gradr" $ toCcc $ andGradR $ sum . fmap @(Vector 5) @R cos

  -- -- (0.8414709848078965,[[0.5403023058681398]]), i.e., (sin 1, [[cos 1]]),
  -- -- where the "[[ ]]" is matrix-style presentation of the underlying
  -- -- linear map.
  -- -- !! 2018-02-10: compile failed
  -- , runPrint 1     $ andDer @R $ sin @R

  -- -- !! 2018-02-10: compile failed
  -- , runPrint (1,1) $ andDer @R $ \ (x,y) -> cos (x + y) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runPrint (1,1) $ andDer @R $ cosSinProd @R

  -- -- !! 2018-02-10: compile failed
  -- , runPrint 1     $ gradient' $ toCcc $ sin @R

  -- -- !! 2018-02-10: compile failed
  -- , runPrint (1,1) $ gradient' $ toCcc $ \ (x,y) -> cos (x + y) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runChase 1 $ gradient' $ toCcc $ sin @R -- 1.5707963267948966

  -- -- !! 2018-02-10: compile failed
  -- , runCircChase "sin-grad" 1 $ toCcc $ gradient $ sin @R -- 1.5707963267948966

  -- -- !! 2018-02-10: compile failed
  -- , print (minimizeN 1 (toCcc cos) 5)  -- (3.141592653589793,6)

  -- -- !! 2018-02-10: compile failed
  -- , print (maximizeN 1 (toCcc cos) 5)  -- (6.283185307179586,5)

  -- -- !! 2018-02-10: compile failed
  -- , runCircMin "cos-min" 5 $ toCcc $ cos  -- (3.141592653589793,6)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "gradient-sin" $ toCcc $ gradient $ toCcc (sin @R)

  -- -- Regression tests
  -- -- !! 2018-02-10: compile failed
  -- , runCirc "ss"   $ toCcc $ ss   @Pair

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "rss"  $ toCcc $ rss  @Pair

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "mean" $ toCcc $ mean @Pair @R

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "mse"  $ toCcc $ mse  @Pair

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "r2"   $ toCcc $ r2   @Pair

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "tss"  $ toCcc $ tss  @Pair

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "mse-samples0"  $ toCcc $ mse samples0

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "mse-samples0-ad" $ toCcc $ andDer @R $ mse samples0

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "mse-samples0-der" $ toCcc $ der $ mse samples0

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "mse-samples0-grad" $ toCcc $ gradient $ mse samples0

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "q1" $ toCcc $ \ (a :: R) -> andDer @R (\ y -> y * a)

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "q2" $ toCcc $ \ (a :: R) -> andDer @R (\ y -> a * y)

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "mse-pair-grad" $ toCcc $ \ (samples :: Par1 Sample) -> gradient $ mse samples

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "mse-samples0-grad" $ toCcc $ gradient $ mse samples0

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "mse-samples1-ad" $ toCcc $ andDer @R $ mse samples1

  -- -- !! 2018-02-10: compile failed
  -- , runCircChase "mse-regress0" (0,0) $ toCcc $ gradient $ negate . mse samples0

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "mse-regress1" $ toCcc $ gradient $ negate . mse samples1

  -- -- !! 2018-02-10: compile failed
  -- , runPrint (0,0) $ take 1000 . drop 10000 . minimizeL 0.01 (toCcc (mse samples1))

  -- -- !! 2018-02-10: compile failed
  -- , runCircChase "mse-regress0b" $ toCcc $ regress (0,0) mse samples0

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> x - y :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> 4 - (y + x) :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> sqr (4 - (y + x)) :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> sqr (4 - (y + x * 3)) :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ uncurry ((+) @R)

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ uncurry ((-) @R)

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ \ x -> x - 1 :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ uncurry ((+) @R) . A.second negate

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ \ x -> x + negate 1 :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSyn $ toCcc $ andDer @R $ \ (x,y) -> (y + x) :: R

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "mse-samples1"  $ toCcc $ mse samples1

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "mse-samples1-ad" $ toCcc $ andDer @R $ mse samples1

  -- -- !! 2018-02-10: compile failed
  -- , runCirc "mse-samples1-der"  $ toCcc $ gradient $ mse samples1

  -- -- !! 2018-02-10: compile failed
  -- , print (minimizeN 0.01 (mse samples1) (0,0))

  -- -- !! 2018-02-10: compile failed
  -- , print (regress mse samples1)

  -- -- !! 2018-02-10: compile failed
  -- , print (regress r2 samples1)

  -- -- Incremental evaluation. Partly brooken
  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "negate-andInc" $ toCcc $ andInc $ (negate @R)

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "sop1-andInc"   $ toCcc $ andInc $ \ ((x,y),z) -> x * y + y * z + x * z :: R

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "magSqr-andInc" $ toCcc $ andInc $ magSqr @R

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

  -- -- Recursion experiments
  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fac1" $ toCcc $ fac1  -- bare unboxed var

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fac2" $ toCcc $ fac2 -- infinite compilation loop

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fac3" $ toCcc $ fac3 -- same infinite compilation loop

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fac4" $ toCcc $ fac4 -- same infinite compilation loop

  -- -- !! 2018-02-10: compile timeout
  -- , runSynCirc "fac5" $ toCcc $ -- same infinite compilation loop
  --     \ (n0 :: Int) -> let go n = if n < 1 then 1 else n * go (n-1) in
  --                        go n0

  -- -- !! 2018-02-10: run failed
  -- , runSynCirc "fac6" $ toCcc $ -- unhandled letrec
  --     \ (n0 :: Int, n1) -> let go n = if n < 1 then n1 else n * go (n-1) in
  --                        go n0

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fac7" $ toCcc $ fac7

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fac8" $ toCcc $ fac8 -- compilation loop

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fac9" $ toCcc $ fac9 -- compilation loop

  -- Array experiments

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "map-negate-arr" $ toCcc $ fmap @(Vector Bool) @Int negate

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "map-map-arr" $ toCcc $ fmap (+3) . fmap @(Vector Bool) @Int (+2)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "liftA2-arr-b" $ toCcc $ uncurry $ liftA2 @(Vector Bool) ((+) @Int)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fmap-arr-bool-plus" $ toCcc $ fmap @(Vector Bool) ((+) @Int)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "app-arr-bool" $ toCcc $ (<*>) @(Vector Bool) @Int @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-lb1" $ toCcc $ sum @(Vector (LB N1)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-lb2" $ toCcc $ sum @(Vector (LB N2)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-lb3" $ toCcc $ sum @(Vector (LB N3)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-lb4" $ toCcc $ sum @(Vector (LB N4)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-lb8" $ toCcc $ sum @(Vector (LB N8)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-rb1" $ toCcc $ sum @(Vector (RB N1)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-rb2" $ toCcc $ sum @(Vector (RB N2)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-rb3" $ toCcc $ sum @(Vector (RB N3)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-rb4" $ toCcc $ sum @(Vector (RB N4)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-rb8" $ toCcc $ sum @(Vector (RB N8)) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "inArr2-liftA2-bool"    $ toCcc $
  --      (inNew2 (liftA2 (+)) :: Binop (Vector Bool Int))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "unpack-arr-2" $ toCcc $ (unpack @(Vector Bool Int))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "unpack-arr-4" $ toCcc $ (unpack @(Vector (Bool :* Bool) Int))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-fun-2"    $ toCcc $
  --      (sum . unpack :: Vector Bool Int -> Int)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-fun-4"    $ toCcc $
  --      (sum . unpack :: Vector (Bool :* Bool) Int -> Int)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-fun-8"    $ toCcc $
  --      (sum . unpack :: Vector ((Bool :* Bool) :* Bool) Int -> Int)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fmap-arr-bool" $ toCcc $ fmap @(Vector Bool) (negate @Int)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "liftA2-arr-bool" $ toCcc $ liftA2 @(Vector Bool) ((+) @Int)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "liftArr2-bool" $ toCcc $ liftArr2 @Bool ((+) @Int)

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "liftArr2-bool-unc" $ toCcc $ uncurry (liftArr2 @Bool ((+) @Int))

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "sum-arr-bool" $ toCcc $ sum @(Vector Bool) @Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "multi-if-equal-int" $ toCcc $
  --     \ case
  --         1 -> 3
  --         5 -> 7
  --         7 -> 9
  --         (_ :: Int) -> 0 :: Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "multi-if-equal-int-scrut" $ toCcc $
  --     \ x -> case 13 * x of
  --         1 -> 3
  --         5 -> 7
  --         7 -> 9
  --         (_ :: Int) -> 0 :: Int

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "if-equal-int-x" $ toCcc $
  --     \ x -> case x of
  --         5 -> x `div` 2
  --         (_ :: Int) -> 0 :: Int

  ]

#if 0

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

#endif

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

#if 0

runChase :: (HasV R a, Zip (V R a), Eq a, Show a)
         => a -> (a -> a) -> IO ()
runChase a0 f = print (chase 1 f a0)

runCircChase :: (GO a R, HasV R a, Zip (V R a), Eq a, Show a)
             => String -> a -> ((:>) :**: (->)) a a -> IO ()
runCircChase nm a0 (circ :**: f) = runCirc nm circ >> runChase a0 f

#endif

-- gradient :: HasV R a => (a -> R) -> a -> a

-- gradientD :: HasV R a => D R a R -> a -> a

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

-- type OkLC' = OkLM R &+& GenBuses

-- Experimenting with a rule failure. See 2017-10-20 notes.

-- -- Works ok
-- foo1 :: Choice (Ok (:>)) a b -> Choice GenBuses a b
-- foo1 z = toCcc (unCcc z)

-- foo1 :: Unop R -> Unop (Par1 R)
-- foo1 = toCcc' A.fmapC --

-- foo2 :: Unop R :* Par1 R -> Par1 R
-- foo2 = toCcc' (A.uncurry A.fmapC) --

-- foo3 :: ADFun.D (Vector 5 R) (Vector 5 R)
-- -- foo3 = toCcc' (fmap negate :: Unop (Vector 5 R))
-- foo3 = toCcc (fmap negate :: Unop (Vector 5 R))

-- foo4 :: Vector 5 R -> Vector 5 R :* (Vector 5 R -> Vector 5 R)
-- foo4 = andDerF (fmap negate :: Unop (Vector 5 R))

-- foo4 :: Vector 5 R -> Vector 5 R :* (Vector 5 R -> Vector 5 R)
-- -- foo4 = andDerF (fmap negate :: Unop (Vector 5 R))
-- -- foo4 = unD (toCcc' (fmap negate :: Unop (Vector 5 R)))
-- foo4 = unD (reveal (toCcc' (fmap negate :: Unop (Vector 5 R))))

-- foo5 :: Vector 5 R :> Vector 5 R :* (Vector 5 R -> Vector 5 R)
-- foo5 = toCcc (andDerF (fmap negate :: Unop (Vector 5 R)))

-- bar :: Float
-- bar = fromIntegral (3 :: Int)

-- foo1 :: Foo -> Foo :* (Foo -> Foo)
-- foo1 = andDerF negateFoo

{--------------------------------------------------------------------

--------------------------------------------------------------------}

-- -- fmap negate
-- foo :: ADFun.D (Vector 5 R) (Vector 5 R)
-- foo = toCcc $ fmap @(Vector 5) @R negate

-- -- case fmap negate of { D f -> f }
-- foo :: Vector 5 R -> Vector 5 R :* (Vector 5 R -> Vector 5 R)
-- foo = andDerF $ fmap @(Vector 5) @R negate

-- -- second (curry (fmapC apply) . zipC) . (unzipC . fmap (\ a -> negate a, negate))
-- foo :: Vector 5 R -> Vector 5 R :* (Vector 5 R -> Vector 5 R)
-- foo = toCcc $ andDerF $ fmap @(Vector 5) @R negate

-- -- Vector mess
-- foo :: Vector 5 R -> Vector 5 R :* (Vector 5 R -> Vector 5 R)
-- foo = reveal $ toCcc $ andDerF $ fmap @(Vector 5) @R negate

  -- -- !! 2018-02-10: compile failed
  -- , runSynCirc "fst-dual-af" $ toCcc $ repr $ repr $ toCcc @(Dual (-+>)) $ fst @R @R


-- -- Dual additive
-- dadFun :: (a -> b) -> (b -> a)
-- dadFun f = repr (toDual @(-+>) f)
-- {-# INLINE dadFun #-}

-- -- Define a restricted form of the d operator.
-- d :: Unop (R -> a)
-- d f = \ x -> derF f x 1
-- {-# INLINE d #-}

-- baz :: Vector 5 R -> Vector 5 R -> Vector 5 R
-- baz ab = gradR (dotV ab)

-- baz :: Vector 5 R -> RAD (Vector 5 R) R
-- baz ab = toCcc' @RAD (dotV ab)

-- baz :: Vector 5 R -> RAD (Vector 5 R) R
-- baz ab = toCcc @RAD (dotV ab)

-- baz :: Vector 5 R -> Vector 5 R -> R :* (Vector 5 R -> R
-- baz ab = toCcc' @RAD (dotV ab)

-- baz1 :: Vector 5 R :> Vector 5 R
-- baz1 = toCcc $ gradR sumA --

-- baz2 :: Vector 5 R :> R :* (R -> Vector 5 R)
-- baz2 = toCcc $ andDerR sumA --

-- baz2 :: Vector 5 R -> R :* Dual (-+>) (Vector 5 R) R
-- baz2 = repr (toCcc @RAD sumA)

-- baz3 :: Vector 5 R :> R :* Dual (-+>) (Vector 5 R) R
-- baz3 = toCcc (repr (toCcc @RAD sumA))

-- baz4 :: Vector 5 R :> R :* Dual (-+>) (Vector 5 R) R
-- baz4 = toCcc (repr (A.sumAC @RAD @(Vector 5) @R))

-- baz4 :: R :> R :* Dual (-+>) R R
-- baz4 = toCcc (repr (A.negateC @RAD))

-- baz5 :: Vector 5 R :> R
-- baz5 = toCcc (repr (A.sumAC @(-+>)))

-- baz5 :: R :> R
-- baz5 = toCcc (A.reprC (A.negateC @(-+>)))

-- baz :: R :> R
-- baz = toCcc (repr (C.negateC @(-+>)))

-- baz :: Vector 5 R -> Vector 5 R -> Vector 5 R
-- baz ab = gradR (dotV ab)

-- baz :: Vector 5 R -> (Vector 5 R :> Vector 5 R)
-- baz ab = toCcc' (gradR (dotV ab))

-- baz :: Vector 5 R -> Vector 5 R -> R :* (R -> Vector 5 R)
-- baz ab = andDerR (dotV ab)  -- fine

-- baz :: Vector 5 R -> Vector 5 R :> R :* (R -> Vector 5 R)
-- baz ab = toCcc' (andDerR (dotV ab)) -- breaks

-- baz :: Vector 5 R -> Vector 5 R :> Vector 5 R :* (Vector 5 R -> Vector 5 R)
-- baz ab = toCcc' (andDerR (zipWith (*) ab)) --

-- baz :: Vector 5 R -> Vector 5 R :> Vector 5 R :* (Vector 5 R -> Vector 5 R)
-- baz ab = toCcc' (andDerF (zipWith (*) ab)) --

-- baz :: Vector 5 R -> Vector 5 R -> R :* (R -> Vector 5 R)
-- baz ab = andDerR (dotV ab)

-- baz :: Vector 5 R -> Vector 5 R :> R :* (R -> Vector 5 R)
-- baz ab = toCcc' (andDerR (dotV ab))  -- breaks

-- baz :: Vector 5 R -> Vector 5 R :> R :* (Vector 5 R -> R)
-- baz ab = toCcc' (andDerF (dotV ab))  -- ?
