{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Reverse mode AD

module ConCat.RAD (andDerR,derR,andGradR,gradR) where

import Prelude hiding (id,(.),const,unzip)

import Data.Constraint (Dict(..),(:-)(..))

import Data.Pointed
import Data.Key
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(..))

import ConCat.Misc ((:*),Yes1,result,sqr,unzip,cond)
import ConCat.Category
import ConCat.AltCat (toCcc)
import qualified ConCat.AltCat as A
import ConCat.Additive
import ConCat.DualAdditive
import ConCat.GAD

-- Differentiable functions
type RAD = GD Dual

type instance GDOk Dual = Yes1

mkD :: (a -> b :* (b -> a)) -> RAD a b
mkD = D . (result.second) Dual
{-# INLINE mkD #-}
-- mkD h = D (second Dual . h)

unMkD :: RAD a b -> (a -> b :* (b -> a))
unMkD = (result.second) unDual . unD
{-# INLINE unMkD #-}
-- unMkD (D h) = second unDual . h

-- mkD f f' = D (\ a -> (f a, Dual (f' a)))

instance Additive b => ConstCat RAD b where
  const b = linear (const b)
  {-# INLINE const #-}

instance TerminalCat RAD where
  it = const ()
  {-# INLINE it #-}

instance (Num s, Additive s) => NumCat RAD s where
  addC    = D (addC &&& addD)
  negateC = D (negateC &&& negateD)
  mulC    = D (mulC &&& mulD)
  powIC   = notDef "powIC"       -- TODO
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

-- Variable ‘s’ occurs more often
--   in the constraint ‘Additive s’ than in the instance head
-- (Use UndecidableInstances to permit this)

-- Orphan instance:
--   instance forall s. (Num s, Additive s) => NumCat RAD s

-- I think I could remove the 'Additive s' superclass constraint from
-- 'NumCat RAD s' if I remove the 'Ok s' superclass constraint from the
-- NumCat class definition.

scalarD :: Num s => (s -> s) -> (s -> s -> s) -> RAD s s
scalarD f d = D (\ x -> let r = f x in (r, Dual (* d x r)))
{-# INLINE scalarD #-}

-- Use scalarD with const f when only r matters and with const' . g when only x
-- matters.

scalarR :: Num s => (s -> s) -> (s -> s) -> RAD s s
scalarR f x = scalarD f (const x)
{-# INLINE scalarR #-}

scalarX :: Num s => (s -> s) -> (s -> s) -> RAD s s
scalarX f f' = scalarD f (const . f')
{-# INLINE scalarX #-}

instance (Fractional s, Additive s) => FractionalCat RAD s where
  recipC = scalarR recip (negate . sqr)
  {-# INLINE recipC #-}

instance (Floating s, Additive s) => FloatingCat RAD s where
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

instance Ord a => MinMaxCat RAD a where
  minC = D (minC &&& cond exl exr . lessThanOrEqual)
  maxC = D (maxC &&& cond exr exl . lessThanOrEqual)
  {-# INLINE minC #-} 
  {-# INLINE maxC #-} 

-- Equivalently,

  -- minC = D (\ (x,y) -> (minC (x,y), if x <= y then exl else exr))
  -- maxC = D (\ (x,y) -> (maxC (x,y), if x <= y then exr else exl))

  -- minC = D (\ xy -> (minC xy, if lessThanOrEqual xy then exl else exr))
  -- maxC = D (\ xy -> (maxC xy, if lessThanOrEqual xy then exr else exl))

  -- minC = D (\ xy -> (minC xy, cond exl exr (lessThanOrEqual xy)))
  -- maxC = D (\ xy -> (maxC xy, cond exr exl (lessThanOrEqual xy)))

-- Functor-level operations:

-- TODO: IfCat. Maybe make ifC :: (a :* a) `k` (Bool -> a), which is linear.

instance Additive1 h => OkFunctor RAD h where
  okFunctor :: forall a. Ok' RAD a |- Ok' RAD (h a)
  okFunctor = Entail (Sub (Dict <+ okFunctor @Dual @h @a))
  -- okFunctor = inForkCon (yes1 *** additive1 @h @a)
  {-# INLINE okFunctor #-}

instance (Functor h, Zip h, Additive1 h) => FunctorCat RAD h where
  fmapC (unMkD -> q) = mkD (second zap . unzip . fmap q)
  -- fmapC (D q) = D (second zap . unzip . fmap q)
  unzipC = linear unzipC
  {-# INLINE fmapC #-}
  {-# INLINE unzipC #-}

-- q :: a -> b :* Dual a b
-- fmap q :: h a -> h (b :* Dual a b)
-- unzip . fmap q :: h a -> h b :* h (Dual a b)
-- second zap . unzip . fmap q :: h a -> h b :* Dual (h a) (h b)

-- Nope, since zap :: h (a -> b) -> (h a -> h b), and
-- zapC :: (h (a -> b) :* h a) `k` h b.
-- I think there's something here, so keep probing.

instance (Foldable h, Pointed h) => SumCat RAD h where
  -- I'd like to use sumC and pointC from Category, but they lead to some sort of failure.
  -- sumC = affine sumC pointC
  -- I'd like to use the following definition, but it triggers a plugin failure.
  -- TODO: track it down.
  -- sumC = affine sum point
  sumC = linear A.sumC
  {-# INLINE sumC #-}

instance (Zip h, Additive1 h) => ZipCat RAD h where
  zipC = linear A.zipC
  {-# INLINE zipC #-}
  -- zipWithC = ??
  -- {-# INLINE zipWithC #-}

-- TODO: Move OkFunctor and FunctorCat instances to GAD.

#if 0

-- Change sumC to use Additive, and relate the regular sum method.

instance (Pointed h, Foldable h, Additive1 h) => PointedCat RAD h where
  pointC = linear A.pointC
  {-# INLINE pointC #-}

instance (Zip h, Foldable h, Additive1 h) => Strong RAD h where
  strength = linear A.strength
  {-# INLINE strength #-}

#endif

instance (Distributive g, Distributive f) => DistributiveCat RAD g f where
  distributeC = linear A.distributeC
  {-# INLINE distributeC #-}

instance Representable g => RepresentableCat RAD g where
  indexC    = linear A.indexC
  tabulateC = linear A.tabulateC
  {-# INLINE indexC #-}
  {-# INLINE tabulateC #-}

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

-- | Add a dual/reverse derivative
andDerR :: (a -> b) -> (a -> b :* (b -> a))
andDerR f = unMkD (toCcc f)
-- andDerR = (result.result.second) unDual andDeriv
{-# INLINE andDerR #-}

-- | Dual/reverse derivative
derR :: (a -> b) -> (a -> (b -> a))
derR = (result.result) snd andDerR
-- derR = (result.result) unDual deriv
{-# INLINE derR #-}

andGradR :: Num s => (a -> s) -> (a -> s :* a)
andGradR = (result.result.second) ($ 1) andDerR
{-# INLINE andGradR #-}

gradR :: Num s => (a -> s) -> (a -> a)
gradR = (result.result) snd andGradR
{-# INLINE gradR #-}

-- andGradR :: Num s => (a -> s) -> (a -> s :* a)
-- andGradR = (result.result.second) (($ 1) . unDual) andDeriv
-- {-# INLINE andGradR #-}

-- gradR :: Num s => (a -> s) -> (a -> a)
-- gradR = (result.result) snd andGradR
-- {-# INLINE gradR #-}
