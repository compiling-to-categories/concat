{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}

#include "ConCat/AbsTy.inc"
AbsTyPragmas

-- | Additive maps

module ConCat.AdditiveMap
  ( Additive1(..),AdditiveMap(..),module ConCat.Additive
  ) where

import Prelude hiding (id,(.),curry,uncurry,zipWith)

import Data.Monoid
import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:.:)(..))
import GHC.TypeLits (KnownNat)

import Data.Constraint (Dict(..),(:-)(..))
import Data.Vector.Sized (Vector)

import ConCat.Orphans ()
import ConCat.AltCat
import ConCat.Rep
import ConCat.Additive
-- -- The following imports allows the instances to type-check. Why?
-- import qualified ConCat.Category  as C

AbsTyImports

-- | Additive homomorphisms
data AdditiveMap a b = AdditiveMap (a -> b)

instance HasRep (AdditiveMap a b) where
  type Rep (AdditiveMap a b) = a -> b
  abst f = AdditiveMap f
  repr (AdditiveMap f) = f

AbsTy(AdditiveMap a b)

instance Category AdditiveMap where
  type Ok AdditiveMap = Additive
  id = abst id
  (.) = inAbst2 (.)

instance ProductCat AdditiveMap where
  exl    = abst exl
  exr    = abst exr
  (&&&)  = inAbst2 (&&&)
  (***)  = inAbst2 (***)
  dup    = abst dup
  swapP  = abst swapP
  first  = inAbst first
  second = inAbst second

instance CoproductCatD AdditiveMap where
  inlD   = abst (,zero)
  inrD   = abst (zero,)
  (||||) = inAbst2 (\ f g (x,y) -> f x ^+^ g y)
  (++++) = inAbst2 (***)
  jamD   = abst (uncurry (^+^))
  swapSD = abst swapP
  -- ...

instance Num s => ScalarCat AdditiveMap s where
  scale s = abst (s *)

instance TerminalCat AdditiveMap where
  it = abst zero

instance CoterminalCat AdditiveMap where
  ti = abst zero

-- Note that zero for functions is point zero, i.e., const zero.

class Additive1 h where additive1 :: Sat Additive a |- Sat Additive (h a)

instance Additive1 ((->) a) where additive1 = Entail (Sub Dict)

instance Additive1 Sum where additive1 = Entail (Sub Dict)
instance Additive1 Product where additive1 = Entail (Sub Dict)
instance Additive1 U1 where additive1 = Entail (Sub Dict)
instance Additive1 Par1 where additive1 = Entail (Sub Dict)
instance (AddF f, AddF g) => Additive1 (f :*: g) where additive1 = Entail (Sub Dict)
instance (AddF f, AddF g) => Additive1 (g :.: f) where additive1 = Entail (Sub Dict)

instance KnownNat n => Additive1 (Vector n) where
  additive1 = Entail (Sub Dict)
