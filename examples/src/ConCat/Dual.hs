{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

#include "ConCat/AbsTy.inc"
AbsTyPragmas

-- | Dual category for additive types. Use with GAD for efficient reverse mode AD.

module ConCat.Dual where

import Prelude hiding (id,(.),zip,unzip,zipWith,const)

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed
import Data.Key
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable)

import ConCat.Misc ((:*),inNew2,unzip)
import ConCat.Rep
import ConCat.Category
import qualified ConCat.AltCat as A
import ConCat.AdditiveMap

AbsTyImports

-- Category dual
data Dual k a b = Dual (b `k` a)

-- I'd use newtype, but then I run into some coercion challenges.
-- TODO: investigate.

instance HasRep (Dual k a b) where
  type Rep (Dual k a b) = b `k` a
  abst f = Dual f
  repr (Dual f) = f
  {-# INLINE abst #-}
  {-# INLINE repr #-}

AbsTy(Dual k a b)

instance Category k => Category (Dual k) where
  type Ok (Dual k) = Ok k
  id = abst id
  (.) = inAbst2 (flip (.))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance CoproductCatD k => ProductCat (Dual k) where
  exl   = abst inlD
  exr   = abst inrD
  (&&&) = inAbst2 (||||)
  (***) = inAbst2 (++++)
  dup   = abst jamD
  swapP = abst swapSD
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}
  {-# INLINE (***) #-}
  {-# INLINE dup #-}
  {-# INLINE swapP #-}

instance ProductCat k => CoproductCatD (Dual k) where
  inlD   = abst exl
  inrD   = abst exr
  (||||) = inAbst2 (&&&)
  (++++) = inAbst2 (***)
  jamD   = abst dup
  swapSD = abst swapP
  {-# INLINE inlD #-}
  {-# INLINE inrD #-}
  {-# INLINE (||||) #-}
  {-# INLINE (++++) #-}
  {-# INLINE jamD #-}
  {-# INLINE swapSD #-}

instance ScalarCat k s => ScalarCat (Dual k) s where
  scale s = abst (scale s)

#if 1

-- This ProductCat definition corresponds to the *coproduct* (direct sum) for
-- the Ab category, following duality. TODO: when we have associated products,
-- coproducts, etc, generalize Dual to operate on any category, not just (->).

-- instance (ConstCat k b, Ok k b) => ConstCat (Dual k) b where
--   -- const _ = abst (const zero)  -- TODO: justify via specification
--   const _ = abst ()
--   {-# INLINE const #-}

instance TerminalCat k => CoterminalCat (Dual k) where
  ti = abst it

instance CoterminalCat k => TerminalCat (Dual k) where
  it = abst ti

-- const b :: a -> b
-- ?? :: a `k` b

-- it :: a `k` ()
-- ti :: () `k` b
-- ti . it :: a `k` b

-- Is there a standard name for ti . it ?

instance (Category k, TerminalCat k, CoterminalCat k, Ok k b) => ConstCat (Dual k) b where
  const _ = abst (ti . it)
  {-# INLINE const #-}

-- I'm unsure about this ConstCat instance.

#endif

instance CoerceCat k b a => CoerceCat (Dual k) a b where
  coerceC = abst coerceC

#if 0

addD :: forall k a. (ProductCat k, Ok k a) => a :* a -> Dual k (a :* a) a
addD = const (abst dup)
{-# INLINE addD #-}

-- subD :: forall k a. (ProductCat k, NumCat k a, Ok k a) => a :* a -> Dual k (a :* a) a
-- subD = const (abst (second negateC . dup <+ okProd @k @a))
-- {-# INLINE subD #-}

negateD :: NumCat k a => a -> Dual k a a
negateD = const (abst negateC)
{-# INLINE negateD #-}

mulD :: (ProductCat k, ScalarCat k a, Ok k a, Num a)
     => a :* a -> Dual k (a :* a) a
mulD (u,v) = abst (scale v &&& scale u)
{-# INLINE mulD #-}

-- \ s -> (s*v,s*u) = (* v) &&& (* u)

-- scale v, scale u :: a `k` a
-- scale v &&& scale u :: a `k` (a :* a)
-- abst (scale v &&& scale u) :: Dual k (a :* a) a

-- TODO: consider dropping the ignored arguments from the linear ops (addD,
-- subD, negateD, but not mulD).

...

#endif

#if 1

---- Functor-level:

instance OkFunctor k h => OkFunctor (Dual k) h where
  okFunctor :: forall a. Ok' (Dual k) a |- Ok' (Dual k) (h a)
  okFunctor = Entail (Sub (Dict <+ okFunctor @k @h @a))
  {-# INLINE okFunctor #-}

instance (Functor h, ZipCat k h, FunctorCat k h) => FunctorCat (Dual k) h where
  fmapC = inAbst fmapC
  unzipC = abst zipC
  {-# INLINE fmapC #-}
  {-# INLINE unzipC #-}

instance (Foldable h, Pointed h, PointedCat k h, OkFunctor k h) => AddCat (Dual k) h where
  sumAC = abst A.pointC
  {-# INLINE sumAC #-}

instance (Zip h, FunctorCat k h) => ZipCat (Dual k) h where
  zipC = abst A.unzipC
  {-# INLINE zipC #-}
  -- {-# INLINE zipWithC #-}

instance (Zip h, ZapCat k h, OkFunctor k h) => ZapCat (Dual k) h where
  zapC :: Ok2 k a b => h (Dual k a b) -> Dual k (h a) (h b)
  -- zapC = A.abstC . A.zapC . A.fmapC A.reprC
  -- zapC = abst . A.zapC . fmap repr
  zapC = abstC . zapC . fmapC reprC
  {-# INLINE zapC #-}

-- fmap repr :: h (a `Dual` b) -> h (b -> a)
-- zapC      :: h (b -> a) -> (h b -> h a)
-- abst      :: (h b -> h a) -> (h a `Dual` h b)

#if 0

instance (Pointed h, AddCat k h) => PointedCat (Dual k) h where
  pointC = abst A.sumAC
  {-# INLINE pointC #-}

instance (Category k, FunctorCat k h, ZipCat k h, Zip h, AddCat k h) => Strong (Dual k) h where
  -- TODO: maybe eliminate strength as method
  strength :: forall a b. Ok2 k a b => Dual k (a :* h b) (h (a :* b))
  strength = abst (first A.sumAC . unzipC)
  {-# INLINE strength #-}

-- TODO: can I use sumA instead of A.sumAC?

#endif

instance DistributiveCat k f g => DistributiveCat (Dual k) g f where
  distributeC = abst A.distributeC
  {-# INLINE distributeC #-}

instance RepresentableCat k g => RepresentableCat (Dual k) g where
  indexC    = abst A.tabulateC
  tabulateC = abst A.indexC
  {-# INLINE indexC #-}
  {-# INLINE tabulateC #-}

#endif
