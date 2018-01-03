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

module ConCat.AdditiveFun
  ( Additive1(..),type (-+>)(..),module ConCat.Additive
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

infixr 1 -+>
-- | Additive homomorphisms
newtype a -+> b = AddFun { unDelX :: a -> b }

instance HasRep (a -+> b) where
  type Rep (a -+> b) = a -> b
  abst f = AddFun f
  repr (AddFun f) = f

AbsTy(a -+> b)

instance Category (-+>) where
  type Ok (-+>) = Additive
  id = abst id
  (.) = inAbst2 (.)
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance ProductCat (-+>) where
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

instance CoproductPCat (-+>) where
  inlP   = abst (,zero)
  inrP   = abst (zero,)
  (||||) = inAbst2 (\ f g (x,y) -> f x ^+^ g y)
  (++++) = inAbst2 (***)
  jamD   = abst (uncurry (^+^))
  swapSD = abst swapP
  -- ...
  {-# INLINE inlP #-}
  {-# INLINE inrP #-}
  {-# INLINE (||||) #-}
  {-# INLINE (++++) #-}
  {-# INLINE jamD #-}
  {-# INLINE swapSD #-}

instance Num s => ScalarCat (-+>) s where
  scale s = abst (s *)
  {-# INLINE scale #-}

-- TODO: generalize from (*). Semimodule?

instance TerminalCat (-+>) where
  it = abst zero
  {-# INLINE it #-}

instance CoterminalCat (-+>) where
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

instance Additive1 h => OkFunctor (-+>) h where
  okFunctor :: forall a. Sat Additive a |- Sat Additive (h a)
  okFunctor = additive1
  {-# INLINE okFunctor #-}

instance (Functor h, Additive1 h) => FunctorCat (-+>) h where
  fmapC = inAbst fmapC
  unzipC = abst unzipC
  {-# INLINE fmapC #-}
  {-# INLINE unzipC #-}

instance (Zip h, Additive1 h) => ZipCat (-+>) h where
  zipC = abst zipC
  {-# INLINE zipC #-}

instance (Zip h, OkFunctor (-+>) h) => ZapCat (-+>) h where
  zapC fs = abst (zapC (repr <$> fs))
  {-# INLINE zapC #-}

--                      fs   :: h (a -+> b)
--             repr <$> fs   :: h (a -> b)
--       zapC (repr <$> fs)  :: h a -> h b
-- abst (zapC (repr <$> fs)) :: (-+>) (h a) (h b)

-- class ({- Pointed h, -} OkFunctor k h, Ok k a) => PointedCat k h a where
--   pointC :: a `k` h a

instance (Pointed h, Additive1 h, Additive a) => PointedCat (-+>) h a where
  pointC = abst pointC
  {-# INLINE pointC #-}

instance (Foldable h, Additive a) => AddCat (-+>) h a where
  sumAC = abst sumA
  {-# INLINE sumAC #-}
  
