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

-- | Linear maps as "row-major" functor compositions

module ConCat.Free.LinearRow where

import Prelude hiding (id,(.),zipWith)

import GHC.Generics (Par1(..),(:*:)(..),(:.:)(..))
import Data.Constraint

-- import Data.Pointed (Pointed(..))
import Data.Key (Keyed(..),Zip(..),Adjustable(..))

import Control.Newtype

import ConCat.Misc ((:*),inNew2)  -- inNew,
import ConCat.Orphans ()
import ConCat.Free.VectorSpace
import ConCat.Category

{--------------------------------------------------------------------
    Linear maps
--------------------------------------------------------------------}

-- Linear map from a s to b s
infixr 1 :-*
type (a :-* b) s = b (a s)

-- TODO: consider instead
-- 
--   type Linear = (:.:)
-- 
-- so that Linear itself forms a vector space.

infixr 9 $*
-- Apply a linear map
($*), lapplyL :: (Zip a, Foldable a, Zip b, Num s)
              => (a :-* b) s -> a s -> b s
as $* a = (<.> a) <$> as

lapplyL = ($*)

zeroL :: (Zeroable a, Zeroable b, Num s) => (a :-* b) s
zeroL = unComp1 zeroV
-- zeroL = point zeroV

{--------------------------------------------------------------------
    Other operations
--------------------------------------------------------------------}

scaleL :: (Adjustable a, Keyed a, Zeroable a, Num s)
       => s -> (a :-* a) s
scaleL s = mapWithKey (flip replace s) zeroL

-- mapWithKey :: Keyed f => (Key f -> a -> b) -> f a -> f b
-- replace :: Adjustable f => Key f -> a -> f a -> f a

---- Category

-- Identity linear map
idL :: (Adjustable a, Keyed a, Zeroable a, Num s)
    => (a :-* a) s
idL = scaleL 1

-- Compose linear transformations
(@.) :: (Zip a, Zip b, Zeroable a, Foldable b, Functor c, Num s)
     => (b :-* c) s -> (a :-* b) s -> (a :-* c) s
-- bc @. ab = (bc $*) <$> ab

bc @. ab = (\ b -> sumV (zipWith (*^) b ab)) <$> bc

-- bc :: c (b s)
-- ab :: b (a s)

-- ac :: c (a s)

-- (bc $*) :: b s -> c s

---- Product

exlL :: (Zeroable a, Keyed a, Adjustable a, Zeroable b, Num s)
     => (a :*: b :-* a) s
exlL = (:*: zeroV) <$> idL

exrL :: (Zeroable b, Keyed b, Adjustable b, Zeroable a, Num s)
     => (a :*: b :-* b) s
exrL = (zeroV :*:) <$> idL

forkL :: (a :-* b) s -> (a :-* c) s -> (a :-* b :*: c) s
forkL = (:*:)

---- Coproduct as direct sum (represented as Cartesian product)

inlL :: (Zeroable a, Keyed a, Adjustable a, Zeroable b, Num s)
     => (a :-* a :*: b) s
inlL = idL :*: zeroL

inrL :: (Zeroable a, Zeroable b, Keyed b, Adjustable b, Num s)
     => (b :-* a :*: b) s
inrL = zeroL :*: idL

joinL :: Zip c => (a :-* c) s -> (b :-* c) s -> (a :*: b :-* c) s
joinL = zipWith (:*:)

{--------------------------------------------------------------------
    Category
--------------------------------------------------------------------}

newtype LM s a b = LM ((V s a :-* V s b) s)

instance Newtype (LM s a b) where
  type O (LM s a b) = (V s a :-* V s b) s
  pack ab = LM ab
  unpack (LM ab) = ab

type OkLF' f = (Foldable f, Zeroable f, Zip f, Keyed f, Adjustable f)

type OkLM' s a = (HasV s a, HasL (V s a), Num s)

class    OkLM' s a => OkLM s a
instance OkLM' s a => OkLM s a

instance Category (LM s) where
  type Ok (LM s) = OkLM s
  id = pack idL
  (.) = inNew2 (@.)

instance OpCon (:*) (Sat (OkLM s)) where inOp = Entail (Sub Dict)

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

inlLM :: Ok2 (LM s) a b => LM s a (a :* b)
inlLM = pack inlL

inrLM :: Ok2 (LM s) a b => LM s b (a :* b)
inrLM = pack inrL

joinLM :: Ok3 (LM s) a b c => LM s a c -> LM s b c -> LM s (a :* b) c
joinLM = inNew2 joinL

jamLM :: Ok (LM s) a => LM s (a :* a) a
jamLM = id `joinLM` id

-- We can't make a ClosedCat instance compatible with the ProductCat instance.
-- We'd have to change the latter to use the tensor product.

-- type instance Exp (LM s) = (:.:)

-- Conversion to linear map
lapply :: (Num s, Oks (LM s) [a,b]) => LM s a b -> (a -> b)
lapply (LM gfa) = unV . lapplyL gfa . toV

-- lapplyL :: ... => (a :-* b) s -> a s -> b s


class OkLF' f => HasL f where
  -- | Law: @'linear' . 'lapply' == 'id'@ (but not the other way around)
  linear' :: forall s g. (Num s, OkLF' g) => (f s -> g s) -> (f :-* g) s

instance HasL Par1 where
  linear' f = Par1 <$> f (Par1 1)

--          f          :: Par1 s -> b s
--          f (Par1 1) :: b s
-- Par1 <$> f (Par1 1) :: b (Par1 s)

instance (HasL f, HasL g) => HasL (f :*: g) where
  linear' q = linear' (q . (:*: zeroV)) `joinL` linear' (q . (zeroV :*:))

--          q                :: (f :*: g) s -> h s
--              (:*: zeroV)  :: f s -> (f :*: g) s
--          q . (:*: zeroV)  :: f s -> h s
-- linear' (q . (:*: zeroV)) :: (f :-* h) s

#if 0

instance OpCon (->) (Sat (OkLM s)) where inOp = Entail (Sub Dict)

instance HasL ((->) k) where
  linear' h = ...

h :: (k -> s) -> g s

want :: ((k -> s) :-* g) s
     :: g (k -> s)

#endif

linear :: (OkLM s a, OkLM s b) => (a -> b) -> LM s a b
linear f = LM (linear' (inV f))

-- f :: a -> b
-- inV f :: V s a s -> V s b s

scale :: OkLM s a => s -> LM s a a
scale = LM . scaleL

negateLM :: OkLM s a => LM s a a
negateLM = scale (-1)

{--------------------------------------------------------------------
    Functors
--------------------------------------------------------------------}

data Lapply s

instance FunctorC (Lapply s) (LM s) (->) where fmapC = lapply

data Linear s

instance FunctorC (Linear s) (->) (LM s) where fmapC = linear
