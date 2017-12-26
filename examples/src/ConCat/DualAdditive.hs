{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Dual category for additive types. Use with GAD for efficient reverse mode AD.

module ConCat.DualAdditive where

import Prelude hiding (id,(.))

import Control.Newtype

import ConCat.Misc ((:*),inNew2)
import ConCat.Category
import ConCat.Additive

newtype Dual a b = Dual {unDual :: b -> a }

instance Newtype (Dual a b) where
  type O (Dual a b) = b -> a
  pack = Dual
  unpack = unDual

instance Category Dual where
  type Ok Dual = Additive
  id = pack id
  (.) = inNew2 (flip (.))

instance ProductCat Dual where
  exl = pack (,zero)
  exr = pack (zero,)
  (&&&) = inNew2 (\ f g (x,y) -> f x ^+^ g y)

-- These definitions correspond to the *coproduct* (direct sum) operations.
-- TODO: when we have associated products, coproducts, etc, generalize Dual to
-- operate on any category, not just (->).
