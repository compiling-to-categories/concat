{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- Catify
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

-- | Late-inlining counterparts to ConCat.Aggregate

module ConCat.AltAggregate (module ConCat.AltAggregate, module C) where

import Prelude hiding (id,(.),curry,uncurry,const,zip,zipWith)
import qualified Prelude as P

import GHC.TypeLits (KnownNat)

import Data.Pointed (Pointed(..))
import Data.Key (Zip(..))
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(..))
import Data.Finite (Finite)
import Data.Vector.Sized (Vector)

import ConCat.Misc ((:*))
import ConCat.Aggregate ( OkFunctor(..),FunctorCat,ZipCat,PointedCat,SumCat,Strong
                        , DistributiveCat,RepresentableCat 
                        , fmap', liftA2' )
import qualified ConCat.Aggregate as C
import ConCat.AltCat

-- TODO: Do we really need AltCat now?

-- Catify etc
#include "ConCat/Ops.inc"

Op1(fmapC , (FunctorCat k h, Ok2 k a b)     => (a `k` b) -> (h a `k` h b))
Op0(zipC  , (ZipCat k h    , Ok2 k a b)     => (h a :* h b) `k` h (a :* b))
Op0(pointC, (PointedCat k h, Ok k a)        => a `k` h a)
Op0(sumC  , (SumCat k h    , Ok k a, Num a) => h a `k` a)

Catify(fmap , fmapC)
Catify(zip  , curry zipC)
Catify(point, pointC)
Catify(sum  , sumC)

zipWithC :: Zip h => (a -> b -> c) -> (h a -> h b -> h c)
zipWithC f as bs = fmapC (uncurry f) (zipC (as,bs))
{-# INLINE zipWithC #-}

Catify(zipWith, zipWithC)

unzipC :: forall k h a b. (FunctorCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
       => h (a :* b) `k` (h a :* h b)
unzipC = fmapC exl &&& fmapC exr
           <+ okFunctor @k @h @(a :* b)
           <+ okFunctor @k @h @a
           <+ okFunctor @k @h @b
           <+ okProd    @k @a @b
{-# INLINE unzipC #-}

Catify(unzip,unzipC)  -- Not firing. Why? (Unnecessary.)

zapC :: forall k h a b.
        (FunctorCat k h, ZipCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
     => (h (a -> b) :* h a) `k` h b
zapC = fmapC apply . zipC
         <+ okFunctor @k @h @((a -> b) :* a)
         <+ okProd    @k    @(h (a -> b)) @(h a)
         <+ okFunctor @k @h @(a -> b)
         <+ okFunctor @k @h @a
         <+ okFunctor @k @h @b
         <+ okProd    @k    @(a -> b) @a
         <+ okExp     @k    @a @b
{-# INLINE zapC #-}

Catify(zap, curry zapC)

-- TODO: Is there any value to defining utility functions like unzipC and zapC
-- in categorical generality? Maybe define only for functions, but still using
-- the categorical building blocks. Later extend to other categories by
-- translation, at which point the Ok constraints will be checked anyway.

-- TODO: Try merging Catify into Op0: Op0 (fmapC,fmap,...).

fmapId :: forall k h a. (Category k, FunctorCat k h, Ok k a) => h a `k` h a
fmapId = id <+ okFunctor @k @h @a

{-# RULES
"fmapC id" fmapC id = fmapId
"fmapC compose" forall g f. fmapC g . fmapC f = fmapC (g . f)
 #-}

Op0(strength, (Strong k h, OkFunctor k h, Ok2 k a b) => (a :* h b) `k` h (a :* b))

Op0(distributeC, (DistributiveCat k g f, Ok k a) => f (g a) `k` g (f a))
Op0(tabulateC  , (RepresentableCat k f , Ok k a) => (Rep f -> a) `k` f a)
Op0(indexC     , (RepresentableCat k f , Ok k a) => f a `k` (Rep f -> a))

Catify(distribute, distributeC)
Catify(tabulate  , tabulateC)
Catify(index     , indexC)

collectC :: (Distributive g, Functor f) => (a -> g b) -> f a -> g (f b)
collectC f = distribute . fmap f
-- collectC f = distributeC . fmapC f
{-# INLINE collectC #-}

Catify(collect, collectC)

{-# RULES

"fmap id" uncurry fmapC . (curry exr &&& id) = id

 #-}

-- -- Names are in transition

-- tabulateC :: ArrayCat k n b => Exp k (Finite n) b `k` Arr n b
-- tabulateC = array

-- indexC :: ArrayCat k n b => Arr n b `k` Exp k (Finite n) b
-- indexC = curry arrAt


-- Variant of 'distributeRep' from Data.Functor.Rep
-- TODO: Generalize from Vector.

-- distributeRepC :: ( -- Representable f, Functor w,
--                     f ~ Vector n, KnownNat n, Representable w
--                   )
--                => w (f a) -> f (w a)

-- distributeRepC :: ( -- Representable f, Functor w,
--                     w ~ Vector n, KnownNat n -- , Representable w
--                   )
--                => w (f a) -> f (w a)

-- distributeRepC wf = tabulateC (\k -> fmapC (`indexC` k) wf)

type Diagonal h = (Representable h, Eq (Rep h))

diag :: Diagonal h => a -> a -> h (h a)
diag z o =
  -- tabulateC (\ i -> tabulateC (\ j -> if i == j then o else z))
  -- tabulateC (\ i -> tabulateC (\ j -> if equal (i,j) then o else z))
  tabulate (\ i -> tabulate (\ j -> if i == j then o else z))
{-# INLINE diag #-}

-- TODO: retry diag as a single tabulateC on h :.: h.

-- HACK: the equal here is to postpone dealing with equality on sum types just yet.
-- See notes from 2017-10-15.
-- TODO: remove and test, now that we're translating (==) early (via Catify).

fmapTrans :: forall k a b c h. (ClosedCat k, Strong k h, Ok3 k a b c)
          => (a `k` (b -> c)) -> (a `k` h b) -> (a `k` h c)
fmapTrans f g = fmapC (uncurry f) . strength . (id &&& g)
                <+ okFunctor @k @h @(a :* b)
                <+ okProd @k @a @(h b)
                <+ okFunctor @k @h @c
                <+ okFunctor @k @h @b
                <+ okProd @k @a @b

#if 0
-- Types:

f :: a `k` (b -> c)
g :: a `k` h b

strength :: (a :* h b) `k` h (a :* b)

       uncurry f  :: a :* b `k` c
fmapC (uncurry f) :: h (a :* b) `k` h c

                                id &&& g  :: a `k` (a :* h b)
                    strength . (id &&& g) :: a `k` h (a :* b)
fmapC (uncurry f) . strength . (id &&& g) :: a `k` h c

#endif

-- TODO: Maybe use the following function-only definition instead, and wrap
-- toCcc' around it in the plugin.

fmapTrans' :: Functor h => (a -> (b -> c)) -> (a -> h b) -> (a -> h c)
fmapTrans' f g = fmapC (uncurry f) . strength . (id &&& g)

-- To make it easier yet on the plugin, move the `toCcc'` call into `fmapTrans`:

fmapTrans'' :: Functor h => (a -> (b -> c)) -> (a -> h b) -> (a `k` h c)
fmapTrans'' f g = toCcc' (fmapC (uncurry f) . strength . (id &&& g))

-- Simpler
fmapT :: Functor h => (a -> b -> c) -> (a -> h b -> h c)
fmapT f = curry (fmap (uncurry f) . strength)


-- I could use this style to simplify the plugin, e.g.,

app' :: (a -> b -> c) -> (a -> b) -> (a `k` c)
app' f a = toCcc' (apply . (f &&& a))

-- The plugin would then turn `\ x -> U V` into `app (\ x -> U) (\ x -> V)`.
-- Or leave the `toCcc'` call in the plugin for separation of concerns.

-- One drawback of using these function-only definitions is that the plugin
-- cannot first check whether the target category has the required properties,
-- such as `ClosedCat`.

-- For `\ x -> fmap U`
fmapTrans1 :: forall k a b c h. (ClosedCat k, Strong k h, Ok3 k a b c)
           => (a `k` (b -> c)) -> (a `k` (h b -> h c))
fmapTrans1 g = curry (fmapTrans (g . exl) exr)
               <+ okProd @k @a @(h b)
               <+ okFunctor @k @h @b
               <+ okFunctor @k @h @c
               <+ okExp @k @b @c

#if 0
-- Types:

                               exl       :: a :* h b `k` a
                                    exr  :: a :* h b `k` h b
                  (\ a -> U)             :: a `k` (b -> c)
                  (\ a -> U) . exl       :: (a :* h b) `k` (b -> c)
       fmapTrans ((\ a -> U) . exl) exr  :: (a :* h b) `k` h c
curry (fmapTrans ((\ a -> U) . exl) exr) :: a `k` (h b -> h c)

#endif

{-# RULES

-- "toCcc'/fmap" forall u v.
--   toCcc' (\ x -> fmap u v) = fmapTrans (toCcc' (\ x -> u)) (toCcc' (\ x -> v))

-- "toCcc''/fmap" forall (_k :: _kproxy k) (_a :: _aproxy a) (u :: b -> c) (v :: h b).
--   toCcc'' _k _a (\ x -> fmap u v) =
--      satisfy @(ClosedCat k, Strong k h, Ok3 k a b c)
--      (fmapTrans (toCcc' (\ x -> u)) (toCcc' (\ x -> v)))

-- "toCcc''/fmap" forall (_p :: _proxy (a `k` h c)) (u :: b -> c) (v :: h b).
--   toCcc'' _p (\ x -> fmap u v) =
--      satisfy @(ClosedCat k, Strong k h, Ok3 k a b c)
--      (fmapTrans (toCcc' (\ x -> u)) (toCcc' (\ x -> v)))

 #-}
