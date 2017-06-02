{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
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

import Prelude hiding (id,(.),curry,uncurry,const)

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

#define StdPrim(ty) \
instance HasStandard (ty) where { type Standard (ty) = (ty) ; toStd = id ; unStd = id }

StdPrim(())
StdPrim(Bool)
StdPrim(Int)
StdPrim(Float)
StdPrim(Double)

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

instance DistribCat StdFun where
  distl = StdFun distl
  distr = StdFun distr

instance TerminalCat StdFun where it = StdFun it

instance ClosedCat StdFun where
  apply = StdFun apply
  curry (StdFun f) = StdFun (curry f)
  uncurry (StdFun f) = StdFun (uncurry f)


instance HasStandard b => ConstCat StdFun b where
  const b = StdFun (const (toStd b))

instance BoolCat StdFun where
  notC = StdFun notC
  andC = StdFun andC
  orC  = StdFun orC
  xorC = StdFun xorC

instance (HasStandard a, Eq (Standard a)) => EqCat StdFun a where
  equal = StdFun equal
  notEqual = StdFun notEqual

instance (HasStandard a, Ord (Standard a)) => OrdCat StdFun a where
  lessThan           = StdFun lessThan
  greaterThan        = StdFun greaterThan
  lessThanOrEqual    = StdFun lessThanOrEqual
  greaterThanOrEqual = StdFun greaterThanOrEqual

instance (HasStandard a, Num (Standard a)) => NumCat StdFun a where
  negateC = StdFun negateC
  addC    = StdFun addC
  subC    = StdFun subC
  mulC    = StdFun mulC
  powIC   = StdFun powIC

instance (HasStandard a, Fractional (Standard a)) =>  FractionalCat StdFun a where
  recipC  = StdFun recipC
  divideC = StdFun divideC

instance (HasStandard a, Floating (Standard a)) =>  FloatingCat StdFun a where
  expC = StdFun expC
  cosC = StdFun cosC
  sinC = StdFun sinC

instance (HasStandard a, RealFracCat (->) (Standard a) (Standard b))
      => RealFracCat StdFun a b where
  floorC   = StdFun floorC
  ceilingC = StdFun ceilingC

{--------------------------------------------------------------------
    CCC interface
--------------------------------------------------------------------}

standardize :: (HasStandard a, HasStandard b) => (a -> b) -> (Standard a -> Standard b)
standardize = toStd <~ unStd
-- standardize = toStd
-- standardize (ccc -> StdFun f') = f'
-- standardize f = f' where StdFun f' = ccc f

{--------------------------------------------------------------------
    Instances
--------------------------------------------------------------------}

-- TODO: merge into Rep

instance (HasStandard a,HasStandard b,HasStandard c) => HasStandard (a,b,c)

-- ...
