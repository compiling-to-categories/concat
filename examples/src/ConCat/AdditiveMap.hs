{-# LANGUAGE InstanceSigs #-}
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
import Data.Key (Zip)
import Data.Pointed (Pointed)
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
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance ProductCat AdditiveMap where
  exl    = abst exl
  exr    = abst exr
  (&&&)  = inAbst2 (&&&)
  (***)  = inAbst2 (***)
  dup    = abst dup
  swapP  = abst swapP
  first  = inAbst first
  second = inAbst second
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}
  {-# INLINE (***) #-}
  {-# INLINE dup #-}
  {-# INLINE swapP #-}
  {-# INLINE first #-}
  {-# INLINE second #-}

instance CoproductCatD AdditiveMap where
  inlD   = abst (,zero)
  inrD   = abst (zero,)
  (||||) = inAbst2 (\ f g (x,y) -> f x ^+^ g y)
  (++++) = inAbst2 (***)
  jamD   = abst (uncurry (^+^))
  swapSD = abst swapP
  -- ...
  {-# INLINE inlD #-}
  {-# INLINE inrD #-}
  {-# INLINE (||||) #-}
  {-# INLINE (++++) #-}
  {-# INLINE jamD #-}
  {-# INLINE swapSD #-}

instance Num s => ScalarCat AdditiveMap s where
  scale s = abst (s *)
  {-# INLINE scale #-}

instance TerminalCat AdditiveMap where
  it = abst zero
  {-# INLINE it #-}

instance CoterminalCat AdditiveMap where
  ti = abst zero
  {-# INLINE ti #-}

-- Note that zero for functions is point zero, i.e., const zero.

class Additive1 h where additive1 :: Sat Additive a |- Sat Additive (h a)

instance Additive1 ((->) a) where additive1 = Entail (Sub Dict)
instance Additive1 Sum      where additive1 = Entail (Sub Dict)
instance Additive1 Product  where additive1 = Entail (Sub Dict)
instance Additive1 U1       where additive1 = Entail (Sub Dict)
instance Additive1 Par1     where additive1 = Entail (Sub Dict)
instance (AddF f, AddF g) => Additive1 (f :*: g)  where additive1 = Entail (Sub Dict)
instance (AddF f, AddF g) => Additive1 (g :.: f)  where additive1 = Entail (Sub Dict)
instance KnownNat n       => Additive1 (Vector n) where additive1 = Entail (Sub Dict)

{--------------------------------------------------------------------
    Functor-level operations
--------------------------------------------------------------------}

instance Additive1 h => OkFunctor AdditiveMap h where
  okFunctor :: forall a. Sat Additive a |- Sat Additive (h a)
  okFunctor = additive1
  {-# INLINE okFunctor #-}

instance (Functor h, Additive1 h) => FunctorCat AdditiveMap h where
  fmapC = inAbst fmapC
  unzipC = abst unzipC
  {-# INLINE fmapC #-}
  {-# INLINE unzipC #-}

instance (Zip h, Additive1 h) => ZipCat AdditiveMap h where
  zipC = abst zipC
  {-# INLINE zipC #-}

instance (Zip h, OkFunctor AdditiveMap h) => ZapCat AdditiveMap h where
  zapC fs = abst (zapC (repr <$> fs))
  {-# INLINE zapC #-}

--                      fs   :: h (AdditiveMap a b)
--             repr <$> fs   :: h (a -> b)
--       zapC (repr <$> fs)  :: h a -> h b
-- abst (zapC (repr <$> fs)) :: AdditiveMap (h a) (h b)

-- class ({- Pointed h, -} OkFunctor k h, Ok k a) => PointedCat k h a where
--   pointC :: a `k` h a

instance (Pointed h, Additive1 h, Additive a) => PointedCat AdditiveMap h a where
  pointC = abst pointC
  {-# INLINE pointC #-}

instance (Foldable h, Additive a) => AddCat AdditiveMap h a where
  sumAC = abst sumA
  {-# INLINE sumAC #-}
  
