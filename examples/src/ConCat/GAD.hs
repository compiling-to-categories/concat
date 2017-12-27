{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

#include "ConCat/AbsTy.inc"

-- | Generalized automatic differentiation

module ConCat.GAD where

import Prelude hiding (id,(.),curry,uncurry,const)
-- import qualified Prelude as P
-- import GHC.Exts (Coercible,coerce)
import GHC.Exts (Constraint)

import Data.Constraint (Dict(..),(:-)(..))

-- import GHC.Generics (Par1(..),(:.:)(..),(:*:)())
-- import Control.Newtype
-- import Data.Key (Zip(..))

import Data.Pointed
import Data.Key
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable)
import qualified Data.Functor.Rep

import ConCat.Misc ((:*),type (&+&)) -- ,PseudoFun(..),oops
-- import ConCat.Free.VectorSpace
-- import ConCat.Free.LinearRow
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Rep

AbsTyImports

-- newtype GD k a b = D { unD :: a -> b :* (a `k` b) }
data GD k a b = D { unD :: a -> (b :* (a `k` b)) }

-- Differentiable linear function, given the function and its constant derivative
linearD :: (a -> b) -> (a `k` b) -> GD k a b
-- linearD f f' = D (f &&& const f')
linearD f f' = D (\ a -> (f a, f'))
{-# INLINE linearD #-}

-- -- Differentiable linear function
-- linear :: (a -> b) -> GD k a b
-- linear f = linearD f (toCcc' f)
-- {-# INLINE linear #-}

-- Use of linear leads to an plugin error. TODO: track down. linear also has the
-- unfortunate effect of hiding the requirements on k, resulting in run-time
-- errors instead of compile-time errors.

-- instance Newtype (D s a b) where
--   type O (D s a b) = (a -> b :* L s a b)
--   pack f = D f
--   unpack (D f) = f

instance HasRep (GD k a b) where
  type Rep (GD k a b) = (a -> b :* (a `k` b))
  abst f = D f
  repr (D f) = f

AbsTy(GD k a b)

-- type family GDOk (k :: * -> * -> *) :: * -> Constraint

instance Category k => Category (GD k) where
  -- type Ok (GD k) = Ok k &+& GDOk k
  type Ok (GD k) = Ok k
  id = linearD id id
  D g . D f = D (\ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f'))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

--   (.) = inNew2 $ \ g f -> \ a ->
--     let (b,f') = f a
--         (c,g') = g b
--     in
--       (c, g' . f')

--   (.) = inNew2 $ \ g f -> second (uncurry (.)) . rassocP . first g . f

--   D g . D f = D $ \ a ->
--     let (b,f') = f a
--         (c,g') = g b
--     in
--       (c, g' . f')

type GDOk k = Ok k

instance ProductCat k => ProductCat (GD k) where
  exl = linearD exl exl
  exr = linearD exr exr
  D f &&& D g = D (\ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b,c), f' &&& g'))
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

-- OpCon (Prod k) (Sat (GDOk k))

--   (&&&) = inNew2 $ \ f g -> \ a ->
--     let (b,f') = f a
--         (c,g') = g a
--     in
--       ((b,c), f' &&& g')

--   (&&&) = inNew2 $ \ f g -> second (uncurry (&&&)) . transposeP . (f &&& g)

--   D f &&& D g = D $ \ a ->
--     let (b,f') = f a
--         (c,g') = g a
--     in
--       ((b,c), f' &&& g')

-- -- Don't define methods yet. I think I can optimize away the ClosedCat
-- -- operations in most cases. Once I'm happy with the results, define these methods and turn off the optimizations.
-- instance ClosedCat (GD k)

--     • No instance for (OpCon (Exp (GD k)) (Sat (Ok k)))
--         arising from the superclasses of an instance declaration
--     • In the instance declaration for ‘ClosedCat (GD k)’

{--------------------------------------------------------------------
    Functor-level
--------------------------------------------------------------------}

instance OkFunctor k h => OkFunctor (GD k) h where
  okFunctor :: forall a. Ok' (GD k) a |- Ok' (GD k) (h a)
  okFunctor = Entail (Sub (Dict <+ okFunctor @k @h @a))
  -- okFunctor = Entail (Sub Dict)
  -- okFunctor = inForkCon (yes1 *** okFunctor @k @h @a)
  {-# INLINE okFunctor #-}

-- TODO: FunctorCat. See RAD

instance (SumCat (->) h, SumCat k h, OkFunctor (GD k) h)
      => SumCat (GD k) h where
  sumC = linearD sumC sumC
  {-# INLINE sumC #-}

instance (ZipCat k h, OkFunctor (GD k) h) => ZipCat (GD k) h where
  zipC = linearD zipC zipC
  {-# INLINE zipC #-}
  -- zipWithC = ??
  -- {-# INLINE zipWithC #-}

-- TODO: Move OkFunctor and FunctorCat instances to GAD.

#if 0

-- Change sumC to use Additive, and relate the regular sum method.

instance (OkFunctor (GD k) h) => PointedCat (GD k) h where
  pointC = linearD pointC pointC
  {-# INLINE pointC #-}

instance (OkFunctor (GD k) h) => Strong (GD k) h where
  strength = linearD strength strength
  {-# INLINE strength #-}

#endif

instance (DistributiveCat (->) g f, DistributiveCat k g f)
      => DistributiveCat (GD k) g f where
  distributeC = linearD distributeC distributeC
  {-# INLINE distributeC #-}

instance (RepresentableCat (->) g, RepresentableCat k g)
      => RepresentableCat (GD k) g where
  indexC    = linearD indexC    indexC
  tabulateC = linearD tabulateC tabulateC
  {-# INLINE indexC #-}
  {-# INLINE tabulateC #-}


{--------------------------------------------------------------------
    Other instances
--------------------------------------------------------------------}

notDef :: String -> a
notDef meth = error (meth ++ " on D not defined")

instance (RepCat (->) a r, RepCat k a r) => RepCat (GD k) a r where
  reprC = linearD reprC reprC
  abstC = linearD abstC abstC

#if 0
instance (Coercible a b, V s a ~ V s b, Ok2 k a b) => CoerceCat (GD k) a b where
  coerceC = linearD coerceC coerceC
#else
instance ( CoerceCat (->) a b
         , CoerceCat k a b
         ) => CoerceCat (GD k) a b where
  coerceC = linearD coerceC coerceC
#endif

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

-- | A function combined with its derivative
andDeriv :: forall k a b . (a -> b) -> (a -> b :* (a `k` b))
andDeriv h = unD (toCcc h)
{-# INLINE andDeriv #-}

-- | The derivative of a given function
deriv :: forall k a b . (a -> b) -> (a -> (a `k` b))
deriv h = snd . andDeriv h
{-# INLINE deriv #-}
