{-# LANGUAGE ConstraintKinds #-}
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

{-# OPTIONS_GHC -fprint-potential-instances #-} -- TEMP

#include "ConCat/AbsTy.inc"
AbsTyPragmas

-- | Dual category for additive types. Use with GAD for efficient reverse mode AD.

module ConCat.Dual where

import Prelude hiding (id,(.),zip,unzip,zipWith,const)
import qualified Prelude as P

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed
import Data.Key
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable)

import ConCat.Misc ((:*),(:^),inNew2,unzip,type (&+&))
import ConCat.Rep
import qualified ConCat.Category as C
-- import qualified ConCat.AltCat as A
import ConCat.AltCat
import ConCat.AdditiveFun (Additive,Additive1(..))

AbsTyImports

-- Category dual
data Dual k a b = Dual (b `k` a)

unDual :: Dual k a b -> b `k` a
unDual (Dual f) = f

-- I'd use newtype, but then I run into some coercion challenges.
-- TODO: investigate.

instance HasRep (Dual k a b) where
  type Rep (Dual k a b) = b `k` a
  abst = Dual
  repr = unDual
  {-# INLINE abst #-}
  {-# INLINE repr #-}

AbsTy(Dual k a b)

instance Category k => Category (Dual k) where
  type Ok (Dual k) = Ok k &+& Additive -- for ProductCat instance
  id = abst id
  (.) = inAbst2 (flip (.))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

-- I could define Ok (Dual k) = Ok k, and rely on Ok k and OkAdd k for Additive,
-- but doing do requires a lot of entailments and explicit signatures.

instance CoproductPCat k => ProductCat (Dual k) where
  exl   = abst inlP
  exr   = abst inrP
  (&&&) = inAbst2 (||||)
  (***) = inAbst2 (++++)
  dup   = abst jamP
  swapP = abst swapPS
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}
  {-# INLINE (***) #-}
  {-# INLINE dup #-}
  {-# INLINE swapP #-}

instance ProductCat k => CoproductPCat (Dual k) where
  inlP   = abst exl
  inrP   = abst exr
  (||||) = inAbst2 (&&&)
  (++++) = inAbst2 (***)
  jamP   = abst dup
  swapPS = abst swapP
  {-# INLINE inlP #-}
  {-# INLINE inrP #-}
  {-# INLINE (||||) #-}
  {-# INLINE (++++) #-}
  {-# INLINE jamP #-}
  {-# INLINE swapPS #-}

instance ScalarCat k s => ScalarCat (Dual k) s where
  scale s = abst (scale s)

instance (OkIxProd k h, Additive1 h) => OkIxProd (Dual k) h where
  okIxProd :: forall a. Ok' (Dual k) a |- Ok' (Dual k) (h a)
  okIxProd = Entail (Sub (Dict <+ okIxProd @k @h @a <+ additive1 @h @a))

instance (IxCoproductPCat k h, Functor h, Additive1 h) => IxProductCat (Dual k) h where
  exF    = abst <$> inPF
  forkF  = inAbstF1 joinPF
  crossF = inAbstF1 plusPF
  replF  = abst jamPF
  {-# INLINE exF #-}
  {-# INLINE forkF #-}
  {-# INLINE crossF #-}
  {-# INLINE replF #-}

instance (IxProductCat k h, Functor h, Additive1 h) => IxCoproductPCat (Dual k) h where
  inPF   = abst <$> exF
  joinPF = inAbstF1 forkF
  plusPF = inAbstF1 crossF
  jamPF  = abst replF
  {-# INLINE inPF #-}
  {-# INLINE joinPF #-}
  {-# INLINE plusPF #-}
  {-# INLINE jamPF #-}

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

instance (Category k, TerminalCat k, CoterminalCat k, Ok (Dual k) b) => ConstCat (Dual k) b where
  const _ = abst (ti . it)
  {-# INLINE const #-}

-- I'm unsure about this ConstCat instance.

#endif

instance CoerceCat k b a => CoerceCat (Dual k) a b where
  coerceC = abst coerceC

instance RepCat k a r => RepCat (Dual k) a r where
  abstC = Dual (reprC @k @a @r)
  reprC = Dual (abstC @k @a @r)
  {-# INLINE abstC #-}
  {-# INLINE reprC #-}

-- abstC :: a `k` r
-- Dual abstC :: Dual k r a
-- 
-- reprC :: r `k` a
-- Dual reprC :: Dual k a r

---- Functor-level:

type OkF k h = (Additive1 h, OkFunctor k h)

instance (OkFunctor k h, Additive1 h) => OkFunctor (Dual k) h where
  okFunctor :: forall a. Ok' (Dual k) a |- Ok' (Dual k) (h a)
  okFunctor = Entail (Sub (Dict <+ okFunctor @k @h @a <+ additive1 @h @a))
  {-# INLINE okFunctor #-}

instance (Functor h, ZipCat k h, Additive1 h, FunctorCat k h) => FunctorCat (Dual k) h where
  fmapC  = inAbst fmapC
  unzipC = abst zipC
  {-# INLINE fmapC #-}
  {-# INLINE unzipC #-}

instance (Zip h, Additive1 h, FunctorCat k h) => ZipCat (Dual k) h where
  zipC = abst unzipC
  {-# INLINE zipC #-}
  -- {-# INLINE zipWithC #-}

instance (Zip h, ZapCat k h, OkF k h) => ZapCat (Dual k) h where
  zapC :: Ok2 k a b => h (Dual k a b) -> Dual k (h a) (h b)
  -- zapC = A.abstC . A.zapC . A.fmapC A.reprC
  -- zapC = abst . A.zapC . fmap repr
  zapC = abst . zapC . fmapC repr
  {-# INLINE zapC #-}

-- fmap repr :: h (a `Dual` b) -> h (b -> a)
-- zapC      :: h (b -> a) -> (h b -> h a)
-- abst      :: (h b -> h a) -> (h a `Dual` h b)

instance (PointedCat k h a, Additive a) => AddCat (Dual k) h a where
  sumAC = abst pointC
  {-# INLINE sumAC #-}

instance (AddCat k h a, OkF k h) => PointedCat (Dual k) h a where
  pointC = abst sumAC
  {-# INLINE pointC #-}

-- instance (Category k, FunctorCat k h, ZipCat k h, Zip h, AddCat k h) => Strong (Dual k) h where
--   -- TODO: maybe eliminate strength as method
--   strength :: forall a b. Ok2 k a b => Dual k (a :* h b) (h (a :* b))
--   strength = abst (first sumAC . unzipC)
--   {-# INLINE strength #-}

-- -- TODO: can I use sumA instead of A.sumAC?

instance DistributiveCat k f g => DistributiveCat (Dual k) g f where
  distributeC = abst distributeC
  {-# INLINE distributeC #-}

instance RepresentableCat k g => RepresentableCat (Dual k) g where
  indexC    = abst tabulateC
  tabulateC = abst indexC
  {-# INLINE indexC #-}
  {-# INLINE tabulateC #-}

{--------------------------------------------------------------------
    CCC interface
--------------------------------------------------------------------}

toDual :: forall k a b. (a -> b) -> (b `k` a)
toDual f = unDual (toCcc f)
{-# INLINE toDual #-}
