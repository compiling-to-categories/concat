{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}


{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-orphans #-} -- see orphans

-- | Category of polynomials

module ConCat.Polynomial where

import Prelude hiding (id,(.),const,curry,uncurry)

import Data.Pointed
import Data.Key
import Control.Comonad.Cofree

import Control.Newtype.Generics
import ConCat.Category
import ConCat.Free.VectorSpace
-- import ConCat.Orphans

-- Scalar-valued power series from free vector space
type SPower f s = Cofree f s

-- Vector-valued power series between free vector spaces
type Power f g s = g (SPower f s)

-- Semantic function
spower :: (Zip f, Foldable f, Num s) => SPower f s -> (f s -> s)
spower (s :< p) u = s + u <.> vpower p u

-- Semantic function
vpower :: (Zip f, Foldable f, Functor g, Num s) => Power f g s -> (f s -> g s)
vpower ps u = flip spower u <$> ps

-- TODO: finite representations.

-- TODO: exploit Cofree, Comonad, etc.

szero :: (Pointed f, Num s) => SPower f s
szero = sconst 0
-- szero = point 0

vzero :: (Pointed f, Pointed g, Num s) => Power f g s
vzero = point szero

sconst :: (Pointed f, Num s) => s -> SPower f s
sconst s = s :< vzero

memo :: (Pointed f, Keyed f) => (Key f -> v) -> f v
memo h = mapWithKey (const . h) (point ())

keys :: (Pointed f, Keyed f) => f (Key f)
keys = memo id

idP :: (Pointed f, Keyed f, Num s, Eq (Key f)) => Power f f s
idP = memo (\ k -> 0 :< memo (\ k' -> sconst (delta k k')))

delta :: (Eq a, Num n) => a -> a -> n
delta a b = if a == b then 1 else 0

newtype Series s a b = Series (Power (V s a) (V s b) s)

instance Newtype (Series s a b) where
  type O (Series s a b) = Power (V s a) (V s b) s
  pack p = Series p
  unpack (Series p) = p

type OkF f = (Pointed f, Zip f, Foldable f, Keyed f, Eq (Key f))

type OkS' s a = (HasV s a, OkF (V s a), Num s)

class    OkS' s a => OkS s a
instance OkS' s a => OkS s a

mu :: Ok2 (Series s) a b => Series s a b -> (a -> b)
mu = onV . vpower . unpack

-- mu (Series p) = onV (vpower p)
--                 -- unV . vpower p . toV

-- mu (Series p) a = unV (vpower p (toV a))


instance Category (Series s) where
  type Ok (Series s) = OkS s
  id = pack idP
