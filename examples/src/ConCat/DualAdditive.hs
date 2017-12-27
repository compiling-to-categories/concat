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

import Prelude hiding (id,(.))

import Data.Constraint (Dict(..),(:-)(..))

import ConCat.Misc ((:*),inNew2)
import ConCat.Rep
import ConCat.Category
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

-- These definitions correspond to the *coproduct* (direct sum) operations.
-- TODO: when we have associated products, coproducts, etc, generalize Dual to
-- operate on any category, not just (->).

instance Additive1 h => OkFunctor Dual h where
  okFunctor :: forall a. Ok' Dual a |- Ok' Dual (h a)
  okFunctor = Entail (Sub (Dict <+ additive1 @h @a))
  {-# INLINE okFunctor #-}
