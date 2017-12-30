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

import Prelude hiding (id,(.),curry,uncurry,const,zip,unzip,zipWith)
import qualified Prelude as P
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

import ConCat.Misc ((:*),type (&+&),cond,result,unzip,sqr) -- ,PseudoFun(..),oops
-- import ConCat.Free.VectorSpace
-- import ConCat.Free.LinearRow
-- The following import allows the instances to type-check. Why?
import ConCat.Category
import qualified ConCat.AltCat as A
import ConCat.Rep

AbsTyImports

-- newtype GD k a b = D { unD :: a -> b :* (a `k` b) }
data GD k a b = D { unD :: a -> (b :* (a `k` b)) }

mkD :: HasRep (a `k` b) => (a -> b :* Rep (a `k` b)) -> GD k a b
mkD = D . (result.second) abst
{-# INLINE mkD #-}

unMkD :: HasRep (a `k` b) => GD k a b -> (a -> b :* Rep (a `k` b))
unMkD = (result.second) repr . unD
{-# INLINE unMkD #-}

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

-- Common pattern for linear functions
#define Linear(nm) nm = linearD A.nm A.nm

instance (TerminalCat k, CoterminalCat k, ConstCat k b) => ConstCat (GD k) b where
  const b = linearD (const b) (const b)
  {-# INLINE const #-}

-- What if we went further, and defined nonlinear arrows like mulC as if linear?
-- Probably wouldn't work, since the linear approximations depend on input. On
-- the other hand, maybe approximations of function shiftings at zero.

instance Category k => Category (GD k) where
  type Ok (GD k) = Ok k
  Linear(id)
  D g . D f = D (\ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f'))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance ProductCat k => ProductCat (GD k) where
  Linear(exl)
  Linear(exr)
  D f &&& D g = D (\ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b,c), f' &&& g'))
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

--   (&&&) = inNew2 $ \ f g -> second (uncurry (&&&)) . transposeP . (f &&& g)

{--------------------------------------------------------------------
    NumCat etc
--------------------------------------------------------------------}

instance (LinearCat k s, Num s) => NumCat (GD k) s where
  addC    = linearD addC jamD
  negateC = linearD negateC (scale (-1))
  mulC    = D (mulC &&& \ (u,v) -> scale v |||| scale u) -- \ (du,dv) -> u*dv + v*du
  powIC   = notDef "powIC"       -- TODO
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

scalarD :: (ScalarCat k s) => (s -> s) -> (s -> s -> s) -> GD k s s
scalarD f d = D (\ x             -> let r = f x in (r, scale (d x r)))
{-# INLINE scalarD #-}

-- Use scalarD with const f when only r matters and with const' . g when only x
-- matters.

scalarR :: LinearCat k s => (s -> s) -> (s -> s) -> GD k s s
scalarR f x = scalarD f (const x)
{-# INLINE scalarR #-}

scalarX :: LinearCat k s => (s -> s) -> (s -> s) -> GD k s s
scalarX f f' = scalarD f (const . f')
{-# INLINE scalarX #-}

instance (LinearCat k s, Fractional s) => FractionalCat (GD k) s where
  recipC = scalarR recip (negate . sqr)
  {-# INLINE recipC #-}

instance (LinearCat k s, Floating s) => FloatingCat (GD k) s where
  expC = scalarR exp id
  logC = scalarX log recip
  sinC = scalarX sin cos
  cosC = scalarX cos (negate . sin)
  {-# INLINE expC #-}
  {-# INLINE sinC #-}
  {-# INLINE cosC #-}
  {-# INLINE logC #-}

-- TODO: experiment with moving some of these dual derivatives to DualAdditive,
-- in the style of addD, mulD, etc.

instance (ProductCat k, Ord a) => MinMaxCat (GD k) a where
  minC = D (minC &&& cond exl exr . lessThanOrEqual)
  maxC = D (maxC &&& cond exr exl . lessThanOrEqual)
  {-# INLINE minC #-} 
  {-# INLINE maxC #-} 

-- Equivalently,
-- 
-- minC = D (\ (x,y) -> (minC (x,y), if x <= y then exl else exr))
-- maxC = D (\ (x,y) -> (maxC (x,y), if x <= y then exr else exl))

-- Functor-level operations:

-- TODO: IfCat. Maybe make ifC :: (a :* a) `k` (Bool -> a), which is linear.

{--------------------------------------------------------------------
    Functor-level operations
--------------------------------------------------------------------}

instance (FunctorCat k h, ZapCat k h) => FunctorCat (GD k) h where
  fmapC = inAbst (\ q -> second A.zapC . A.unzipC . A.fmapC q)
  Linear(unzipC)
  {-# INLINE fmapC #-}
  {-# INLINE unzipC #-}

-- See 2017-12-27 notes
-- 
--      q :: a -> b :* (a `k` b)
-- fmap q :: h a -> h (b :* (a `k` b))
-- unzip  :: h (b :* (a `k` b)) -> h b :* h (a `k` b)
-- zapC   :: h (a `k` b) -> (h a `k` h b)

instance OkFunctor k h => OkFunctor (GD k) h where
  okFunctor :: forall a. Ok' (GD k) a |- Ok' (GD k) (h a)
  okFunctor = Entail (Sub (Dict <+ okFunctor @k @h @a))
  -- okFunctor = Entail (Sub Dict)
  -- okFunctor = inForkCon (yes1 *** okFunctor @k @h @a)
  {-# INLINE okFunctor #-}

-- TODO: FunctorCat. See RAD

instance (SumCat (->) h, SumCat k h, OkFunctor (GD k) h)
      => SumCat (GD k) h where
  Linear(sumC)
  {-# INLINE sumC #-}

instance (ZipCat k h, OkFunctor (GD k) h) => ZipCat (GD k) h where
  Linear(zipC)
  {-# INLINE zipC #-}
  -- zipWithC = ??
  -- {-# INLINE zipWithC #-}

instance (ZapCat k h, OkFunctor k h, Zip h) => ZapCat (GD k) h where
  zapC = abst . result (second zapC . unzip) . zapC . fmap repr

-- fmap repr            :: h (GD k a b) -> h (a -> b :* k a b)
-- zapC                 :: h (a -> b :* k a b) -> (h a -> h (b :* k a b))
-- result unzip         :: (h a -> h (b :* k a b)) -> (h a -> h b :* h (k a b))
-- (result.second) zapC :: (h a -> h b :* h (k a b)) -> (h a -> h b :* k (h a) (h b))
-- abst                 :: (h a -> h b :* k (h a) (h b)) -> GD k (h a) (h b)

-- TODO: What use can we make of the ZapCat instance? Maybe repeated differentiation.

#if 0

-- Change sumC to use Additive, and relate the regular sum method.

instance (OkFunctor (GD k) h) => PointedCat (GD k) h where
  Linear(pointC)
  {-# INLINE pointC #-}

instance (OkFunctor (GD k) h) => Strong (GD k) h where
  Linear(strength)
  {-# INLINE strength #-}

#endif

instance (DistributiveCat (->) g f, DistributiveCat k g f)
      => DistributiveCat (GD k) g f where
  Linear(distributeC)
  {-# INLINE distributeC #-}

instance (RepresentableCat (->) g, RepresentableCat k g)
      => RepresentableCat (GD k) g where
  Linear(indexC)
  Linear(tabulateC)
  {-# INLINE indexC #-}
  {-# INLINE tabulateC #-}


{--------------------------------------------------------------------
    Other instances
--------------------------------------------------------------------}

notDef :: String -> a
notDef meth = error (meth ++ " on D not defined")

instance (RepCat (->) a r, RepCat k a r) => RepCat (GD k) a r where
  Linear(reprC)
  Linear(abstC)

#if 0
instance (Coercible a b, V s a ~ V s b, Ok2 k a b) => CoerceCat (GD k) a b where
  Linear(coerceC)
#else
instance ( CoerceCat (->) a b
         , CoerceCat k a b
         ) => CoerceCat (GD k) a b where
  Linear(coerceC)
#endif

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

-- | A function combined with its derivative
andDeriv :: forall k a b . (a -> b) -> (a -> b :* (a `k` b))
andDeriv h = unD (A.toCcc h)
{-# INLINE andDeriv #-}

-- | The derivative of a given function
deriv :: forall k a b . (a -> b) -> (a -> (a `k` b))
deriv h = snd . andDeriv h
{-# INLINE deriv #-}
