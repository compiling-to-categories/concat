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

module ConCat.AdditiveMap (AdditiveMap(..),module ConCat.Additive) where

import Prelude hiding (id,(.),curry,uncurry,zipWith)
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
