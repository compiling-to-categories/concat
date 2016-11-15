{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

-- | Some experiments in formulating constrained linear optimization problems.

module ConCat.Free.LinearCol where

import Prelude hiding (id,(.),zipWith)

import GHC.Generics (Par1(..),(:*:)(..),(:.:)(..))
import Data.Constraint

import Data.Pointed (Pointed(..))
import Data.Key (Keyed(..),Zip(..),Adjustable(..))

import Control.Newtype

import ConCat.Misc (inNew,inNew2)
import ConCat.Orphans ()
import ConCat.Free.VectorSpace
import ConCat.Category

{--------------------------------------------------------------------
    Linear maps
--------------------------------------------------------------------}

-- Linear map from a s to b s
infixr 1 :-*
type (a :-* b) s = a (b s)

-- TODO: consider instead
-- 
--   type Linear = (:.:)
-- 
-- so that Linear itself forms a vector space.

-- Apply a linear map
infixr 9 $*
($*), lapplyL :: (Zip a, Foldable a, Zip b, Pointed b, Num s)
              => (a :-* b) s -> a s -> b s
bs $* a = sumV (zipWith (*^) a bs)

lapplyL = ($*)

zeroL :: (Pointed a, Pointed b, Num s) => (a :-* b) s
zeroL = point zeroV

{--------------------------------------------------------------------
    Other operations
--------------------------------------------------------------------}

---- Category

-- Identity linear map
idL :: (Adjustable m, Keyed m, Pointed m, Num r)
    => (m :-* m) r
idL = mapWithKey (flip replace 1) zeroL

-- mapWithKey :: Keyed f => (Key f -> a -> b) -> f a -> f b
-- replace :: Adjustable f => Key f -> a -> f a -> f a

-- Compose linear transformations
(@.) :: (Functor a, Foldable b, Zip b, Pointed c, Zip c, Num s)
     => (b :-* c) s -> (a :-* b) s -> (a :-* c) s
bc @. ab = (bc $*) <$> ab

-- (@.) = fmap . ($*)

---- Product

exlL :: (Pointed a, Keyed a, Adjustable a, Pointed b, Num s)
     => (a :*: b :-* a) s
exlL = idL :*: zeroL

exrL :: (Pointed b, Keyed b, Adjustable b, Pointed a, Num s)
     => (a :*: b :-* b) s
exrL = zeroL :*: idL

forkL :: Zip a => (a :-* b) s -> (a :-* c) s -> (a :-* b :*: c) s
forkL = zipWith (:*:)

---- Coproduct as direct sum (represented as Cartesian product)

inlL :: (Pointed a, Keyed a, Adjustable a, Pointed b, Num s)
     => (a :-* a :*: b) s
inlL = (:*: zeroV) <$> idL

inrL :: (Pointed a, Pointed b, Keyed b, Adjustable b, Num s)
     => (b :-* a :*: b) s
inrL = (zeroV :*:) <$> idL

joinL :: (a :-* c) s -> (b :-* c) s -> (a :*: b :-* c) s
joinL = (:*:)


{--------------------------------------------------------------------
    Category
--------------------------------------------------------------------}

newtype LM s a b = LM ((V s a :-* V s b) s)

instance Newtype (LM s a b) where
  type O (LM s a b) = (V s a :-* V s b) s
  pack ab = LM ab
  unpack (LM ab) = ab

type OkLF' f = (Foldable f, Pointed f, Zip f, Keyed f, Adjustable f)

type OkLM' s a = (HasV s a, HasL (V s a), Num s)

class    OkLM' s a => OkLM s a
instance OkLM' s a => OkLM s a

instance Category (LM s) where
  type Ok (LM s) = OkLM s
  id = pack idL
  (.) = inNew2 (@.)

instance OpCon (,) (Sat (OkLM s)) where inOp = Entail (Sub Dict)

instance ProductCat (LM s) where
  -- type Prod (LM s) = (,)
  exl = pack exlL
  exr = pack exrL
  (&&&) = inNew2 forkL

-- Can I still have coproducts? Seems problematic without a definable Coprod

-- instance CoproductCat (LM s) where
--   -- type Coprod (LM s) = (,)
--   inl = pack inlL
--   inr = pack inrL
--   (|||) = inNew2 joinL

-- We can't make a ClosedCat instance compatible with the ProductCat instance.
-- We'd have to change the latter to use the tensor product.

-- Conversion to linear map
lapply :: (Num s, Oks (LM s) [a,b]) => LM s a b -> (a -> b)
lapply (LM gfa) = unV . lapplyL gfa . toV

-- lapplyL :: ... => (a :-* b) s -> a s -> b s


class OkLF' f => HasL f where
  -- | Law: @'linear' . 'lapply' == 'id'@ (but not the other way around)
  linear' :: forall s g. (Num s, OkLF' g) => (f s -> g s) -> (f :-* g) s

instance HasL Par1 where
  linear' f = Par1 (f (Par1 1))

--       f           :: Par1 s -> b s
--       f (Par1 1)  :: b s
-- Par1 (f (Par1 1)) :: Par1 (b s)

instance (HasL f, HasL g) => HasL (f :*: g) where
  linear' q = linear' (q . (:*: zeroV)) `joinL` linear' (q . (zeroV :*:))

--          q                :: (f :*: g) s -> h s
--              (:*: zeroV)  :: f s -> (f :*: g) s
--          q . (:*: zeroV)  :: f s -> h s
-- linear' (q . (:*: zeroV)) :: (f :-* h) s

linear :: (OkLM s a, OkLM s b) => (a -> b) -> LM s a b
linear f = LM (linear' (inV f))

-- f :: a -> b
-- inV f :: V s a s -> V s b s

{--------------------------------------------------------------------
    Functors
--------------------------------------------------------------------}

data Lapply s

instance FunctorC (Lapply s) (LM s) (->) where fmapC = lapply

data Linear s

instance FunctorC (Linear s) (->) (LM s) where fmapC = linear
