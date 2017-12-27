{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

#include "ConCat/AbsTy.inc"
AbsTyPragmas

-- | Dual category for additive types. Use with GAD for efficient reverse mode AD.

module ConCat.DualAdditive where

import Prelude hiding (id,(.),zip,unzip,const)

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed
import Data.Key
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable)

import ConCat.Misc ((:*),inNew2,unzip)
import ConCat.Rep
import ConCat.Category
import qualified ConCat.AltCat as A
import ConCat.Additive

AbsTyImports

data Dual a b = Dual { unDual :: b -> a }

-- I'd use newtype, but then I run into some coercion challenges.

instance HasRep (Dual a b) where
  type Rep (Dual a b) = b -> a
  abst = Dual
  repr = unDual

AbsTy(Dual a b)

instance Category Dual where
  type Ok Dual = Additive
  id = abst id
  (.) = inAbst2 (flip (.))

instance ProductCat Dual where
  exl = abst (,zero)
  exr = abst (zero,)
  (&&&) = inAbst2 (\ f g (x,y) -> f x ^+^ g y)

-- This ProductCat definition corresponds to the *coproduct* (direct sum) for
-- the Ab category, following duality. TODO: when we have associated products,
-- coproducts, etc, generalize Dual to operate on any category, not just (->).

instance Additive b => ConstCat Dual b where
  const _ = abst (const zero)  -- TODO: justify via specification
  {-# INLINE const #-}

instance TerminalCat Dual where
  it = const ()
  {-# INLINE it #-}

-- Dual (transpose) of addC
addD :: (a :* a) -> Dual (a :* a) a
addD = const (abst dup)

-- Dual of negateC
negateD :: Num a => a -> Dual a a
negateD = const (abst negateC)

-- Dual of mulC at @(u,v)@
mulD :: Num a => (a :* a) -> Dual (a :* a) a
mulD (u,v) = abst (\ s -> (s*v,s*u))

---- Functor-level:

instance Additive1 h => OkFunctor Dual h where
  okFunctor :: forall a. Ok' Dual a |- Ok' Dual (h a)
  okFunctor = Entail (Sub (Dict <+ additive1 @h @a))
  {-# INLINE okFunctor #-}

instance (Functor h, Zip h, Additive1 h) => FunctorCat Dual h where
  fmapC = inAbst fmapC
  unzipC = abst zipC
  {-# INLINE fmapC #-}
  {-# INLINE unzipC #-}

instance (Foldable h, Pointed h, Additive1 h) => SumCat Dual h where
  -- I'd like to use sumC and pointC from Category, but they lead to some sort of failure.
  -- sumC = affine sumC pointC
  -- I'd like to use the following definition, but it triggers a plugin failure.
  -- TODO: track it down.
  -- sumC = affine sum point
  sumC = abst A.pointC
  {-# INLINE sumC #-}

instance (Zip h, Additive1 h) => ZipCat Dual h where
  zipC = abst A.unzipC
  {-# INLINE zipC #-}
  -- {-# INLINE zipWithC #-}

#if 0

-- Change sumC to use Additive, and relate the regular sum method.

instance (Pointed h, Foldable h, Additive1 h) => PointedCat Dual h where
  pointC = abst A.sumC
  {-# INLINE pointC #-}

instance (Zip h, Foldable h, Additive1 h) => Strong Dual h where
  strength = abst (first A.sumC . unzip)  -- maybe eliminate strength as method
  {-# INLINE strength #-}

#endif

instance (Distributive g, Distributive f) => DistributiveCat Dual g f where
  distributeC = abst A.distributeC
  {-# INLINE distributeC #-}

instance Representable g => RepresentableCat Dual g where
  indexC    = abst A.tabulateC
  tabulateC = abst A.indexC
  {-# INLINE indexC #-}
  {-# INLINE tabulateC #-}
