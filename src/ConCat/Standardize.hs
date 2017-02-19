{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DefaultSignatures #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | A type-standardizing category, as an alternative to the RepCat and CoerceCat classes.

module ConCat.Standardize where

import Prelude hiding (id,(.),curry,uncurry)

import Data.Constraint (Dict(..),(:-)(..))

import ConCat.Misc ((:*),(:+),(:=>))
import ConCat.Category
import ConCat.AltCat (ccc)
import ConCat.Rep

class HasStandard a where
  type Standard a
  toStd :: a -> Standard a
  unStd :: Standard a -> a
  -- defaults
  type Standard a = Standard (Rep a)
  default toStd :: (HasRep a, HasStandard (Rep a)) => a -> Standard (Rep a)
  toStd = toStd . repr
  default unStd :: (HasRep a, HasStandard (Rep a)) => Standard (Rep a) -> a
  unStd = abst . unStd

--     • The type family application ‘Rep a’
--         is no smaller than the instance head
--       (Use UndecidableInstances to permit this)

instance HasStandard Int where { type Standard Int = Int ; toStd = id ; unStd = id }

instance (HasStandard a, HasStandard b) => HasStandard (a :* b) where
  type Standard (a :* b) = Standard a :* Standard b
  toStd = toStd *** toStd
  unStd = unStd *** unStd

instance (HasStandard a, HasStandard b) => HasStandard (a :+ b) where
  type Standard (a :+ b) = Standard a :+ Standard b
  toStd = toStd +++ toStd
  unStd = unStd +++ unStd

instance (HasStandard a, HasStandard b) => HasStandard (a -> b) where
  type Standard (a -> b) = Standard a -> Standard b
  toStd = toStd <~ unStd
  unStd = unStd <~ toStd

newtype StdFun a b = StdFun (Standard a -> Standard b)

instance Category StdFun where
  type Ok StdFun = HasStandard
  id = StdFun id
  StdFun g . StdFun f = StdFun (g . f)

instance OpCon (:*) (Sat HasStandard) where inOp = Entail (Sub Dict)

instance ProductCat StdFun where
  exl = StdFun exl
  exr = StdFun exr
  StdFun f &&& StdFun g = StdFun (f &&& g)

instance OpCon (:+) (Sat HasStandard) where inOp = Entail (Sub Dict)

instance CoproductCat StdFun where
  inl = StdFun inl
  inr = StdFun inr
  StdFun f ||| StdFun g = StdFun (f ||| g)

instance OpCon (:=>) (Sat HasStandard) where inOp = Entail (Sub Dict)

instance ClosedCat StdFun where
  apply = StdFun apply
  curry (StdFun f) = StdFun (curry f)
  uncurry (StdFun f) = StdFun (uncurry f)

standardize :: (a -> b) -> (Standard a -> Standard b)
standardize f = f' where StdFun f' = ccc f

