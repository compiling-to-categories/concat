{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}

-- | Some experiments in formulating constrained linear optimization problems.

module Free.Linear where

import Prelude hiding (id,(.),zipWith)

import Control.Category
import Data.Pointed (Pointed(..))
import Data.Key (Keyed(..),Zip(..),Adjustable(..))
import GHC.Generics ((:*:)(..),(:.:)(..))

import Misc (inNew,inNew2)
import Orphans ()
import Free.VectorSpace

---- Category

-- Identity linear map
idL :: (Adjustable m, Keyed m, Pointed m, Num r)
    => (m :-* m) r
idL = mapWithKey (flip replace 1) zeroL

-- mapWithKey :: Keyed f => (Key f -> a -> b) -> f a -> f b
-- replace :: Adjustable f => Key f -> a -> f a -> f a

-- Compose linear transformations
(@.) :: (Zip o, Zip n, Pointed o, Foldable n, Functor m, Num r)
     => (n :-* o) r -> (m :-* n) r -> (m :-* o) r
no @. mn = linear no <$> mn

-- (@.) = fmap . linear

---- Product

exlL :: (Pointed m, Keyed m, Adjustable m, Pointed n, Num r)
     => (m :*: n :-* m) r
exlL = idL :*: zeroL

exrL :: (Pointed n, Keyed n, Adjustable n, Pointed m, Num r)
     => (m :*: n :-* n) r
exrL = zeroL :*: idL

forkL :: Zip m => (m :-* n) r -> (m :-* o) r -> (m :-* n :*: o) r
forkL = zipWith (:*:)

---- Coproduct as direct sum (represented as Cartesian product)

inlL :: (Pointed m, Keyed m, Adjustable m, Pointed n, Num r)
     => (m :-* m :*: n) r
inlL = (:*: zeroV) <$> idL

inrL :: (Pointed m, Pointed n, Keyed n, Adjustable n, Num r)
     => (n :-* m :*: n) r
inrL = (zeroV :*:) <$> idL

joinL :: (m :-* o) r -> (n :-* o) r -> (m :*: n :-* o) r
joinL = (:*:)

newtype (f :=> g) r = Fun ((f :-* g) r)

-- applyL :: _ => ((f :=> g) :*: f :-* g) r
-- applyL =

-- (f (g r) -> g (g r)) :* f (g r)

{--------------------------------------------------------------------
    Experiment
--------------------------------------------------------------------}

type Linear' = (:.:)

linear' :: (Zip n, Zip m, Pointed n, Foldable m, Num r)
        => Linear' m n r -> m r -> n r
linear' (Comp1 ns) m = sumV (zipWith (*^) m ns)

zeroL' :: (Pointed n, Pointed m, Num r) => Linear' m n r
zeroL' = Comp1 (point zeroV)

idL' :: (Adjustable m, Keyed m, Pointed m, Num r)
     => Linear' m m r
idL' = (inNew . mapWithKey) (flip replace 1) zeroL'

(@@.) :: (Zip o, Zip n, Pointed o, Foldable n, Functor m, Num r)
      => Linear' n o r -> Linear' m n r -> Linear' m o r
(@@.) = inNew . fmap . linear'

-- (@@.) no = inNew (fmap (linear' no))
-- (@@.) no = inNew (linear' no <$>)
-- no @@. Comp1 mn = Comp1 (linear' no <$> mn)

exl' :: (Pointed m, Keyed m, Adjustable m, Pointed n, Num r)
     => Linear' (m :*: n) m r
exl' = inNew (idL :*:) zeroL'

fork' :: Zip m => Linear' m n r -> Linear' m o r -> Linear' m (n :*: o) r
fork' = (inNew2 . zipWith) (:*:)

inl' :: (Pointed m, Keyed m, Adjustable m, Pointed n, Num r)
     => Linear' m (m :*: n) r
inl' = (inNew . fmap) (:*: zeroV) idL'

join' :: Linear' m o r -> Linear' n o r -> Linear' (m :*: n) o r
join' = inNew2 (:*:)

{--------------------------------------------------------------------
    Quantify over Num
--------------------------------------------------------------------}

type U m = forall r. Num r => m r

type Linear'' m n = U (m :.: n)

type NT m n = forall r. Num r => m r -> n r

linear'' :: (Zip n, Zip m, Pointed n, Foldable m)
         => Linear'' m n -> NT m n
linear'' (Comp1 ns) m = sumV (zipWith (*^) m ns)

zeroL'' :: (Pointed n, Pointed m) => Linear'' m n
zeroL'' = Comp1 (point zeroV)

idL'' :: (Adjustable m, Keyed m, Pointed m)
      => Linear'' m m
idL'' = (inNew . mapWithKey) (flip replace 1) zeroL''

exl'' :: (Pointed m, Keyed m, Adjustable m, Pointed n)
      => Linear'' (m :*: n) m
exl'' = inNew (idL :*:) zeroL'

fork'' :: Zip m => Linear'' m n -> Linear'' m o -> Linear'' m (n :*: o)
fork'' = inNew2 (zipWith (:*:))
-- fork'' = (inNew2'' . zipWith) (:*:)

inl'' :: (Pointed m, Keyed m, Adjustable m, Pointed n)
      => Linear'' m (m :*: n)
inl'' = (inNew . fmap) (:*: zeroV) idL''

join'' :: Linear'' m o -> Linear'' n o -> Linear'' (m :*: n) o
join'' = inNew2 (:*:)

{--------------------------------------------------------------------
    Constrained linear optimization
--------------------------------------------------------------------}

-- Affine function and affine constraints. When n == Id and r is
-- ordered, we can solve as a constrained linear optimization problem.
-- The generality over n improves composability.
data LinOpt m n r = forall o. Foldable o => LO (Affine m n r, Affine m o r)

-- TODO: add existentials by wrapping with ExistArg. I'll have to
-- bridge the gap between the Category classes and the
-- almost-instances above.
