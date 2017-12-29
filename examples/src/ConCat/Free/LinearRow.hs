{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
-- {-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

-- | Linear maps as "row-major" functor compositions

module ConCat.Free.LinearRow where

import Prelude hiding (id,(.),zipWith)
import GHC.Exts (Coercible,coerce)
import Data.Foldable (toList)
import GHC.Generics (U1(..),(:*:)(..),(:.:)(..)) -- ,Par1(..)
-- import GHC.TypeLits (KnownNat)

import Data.Constraint
import Data.Key (Zip(..))
import Data.Distributive (collect)
import Data.Functor.Rep (Representable)
-- import qualified Data.Functor.Rep as R
import Text.PrettyPrint.HughesPJClass hiding (render)
import Control.Newtype
-- import Data.Vector.Sized (Vector)

import ConCat.Misc ((:*),PseudoFun(..),oops,R,Binop,inNew2)
import ConCat.Orphans ()
import ConCat.Free.VectorSpace
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat hiding (const)
import ConCat.Rep
-- import ConCat.Free.Diagonal
import qualified ConCat.Additive as Ad

-- TODO: generalize from Num to Semiring

{--------------------------------------------------------------------
    Linear maps
--------------------------------------------------------------------}

-- Linear map from a s to b s
infixr 1 :-*
type (a :-* b) s = b (a s)

-- TODO: consider instead
-- 
--   type Linear = (:.:)
-- 
-- so that Linear itself forms a vector space.

infixr 9 $*
-- Apply a linear map
($*), lapplyL :: forall s a b. (Zip a, Foldable a, Zip b, Num s)
              => (a :-* b) s -> a s -> b s
as $* a = (<.> a) <$> as
lapplyL = ($*)
{-# INLINE ($*) #-}
{-# INLINE lapplyL #-}

zeroL :: (Zeroable a, Zeroable b, Num s) => (a :-* b) s
zeroL = unComp1 zeroV
-- zeroL = point zeroV

scaleL :: (Diagonal a, Num s) => s -> (a :-* a) s
scaleL = diag 0

{--------------------------------------------------------------------
    Other operations
--------------------------------------------------------------------}

---- Category

-- Identity linear map
idL :: (Diagonal a, Num s) => (a :-* a) s
idL = scaleL 1
{-# INLINE idL #-}

-- Compose linear transformations
compL :: (Zip a, Zip b, Zeroable a, Foldable b, Functor c, Num s)
     => (b :-* c) s -> (a :-* b) s -> (a :-* c) s
bc `compL` ab = (\ b -> sumV (zipWith (*^) b ab)) <$> bc
{-# INLINE compL #-}

#if 0
bc :: c (b s)
ab :: b (a s)
b  :: b s
zipWith (*^) b ab :: b (a s)
sumV (zipWith (*^) b ab) :: a s
\ b -> sumV (zipWith (*^) b ab) :: b -> a s
(\ b -> sumV (zipWith (*^) b ab)) <$> bc :: c (a s)
#endif

---- Product

exlL :: (Zeroable a, Diagonal a, Zeroable b, Num s)
     => (a :*: b :-* a) s
exlL = (:*: zeroV) <$> idL
{-# INLINE exlL #-}

exrL :: (Zeroable b, Diagonal b, Zeroable a, Num s)
     => (a :*: b :-* b) s
exrL = (zeroV :*:) <$> idL
{-# INLINE exrL #-}

forkL :: (a :-* b) s -> (a :-* c) s -> (a :-* b :*: c) s
forkL = (:*:)

itL :: (a :-* U1) s
itL = U1

---- Coproduct as direct sum (represented as Cartesian product)

inlL :: (Zeroable a, Diagonal a, Zeroable b, Num s)
     => (a :-* a :*: b) s
inlL = idL :*: zeroL
{-# INLINE inlL #-}

inrL :: (Zeroable a, Zeroable b, Diagonal b, Num s)
     => (b :-* a :*: b) s
inrL = zeroL :*: idL
{-# INLINE inrL #-}

joinL :: Zip c => (a :-* c) s -> (b :-* c) s -> (a :*: b :-* c) s
joinL = zipWith (:*:)
{-# INLINE joinL #-}

{--------------------------------------------------------------------
    Category
--------------------------------------------------------------------}

newtype L s a b = L ((V s a :-* V s b) s)
-- data L s a b = L ((V s a :-* V s b) s)

type LR = L R

-- Using data is a workaround for
-- <https://ghc.haskell.org/trac/ghc/ticket/13083#ticket> when I need it. See
-- notes from 2016-01-07.

-- deriving instance Show ((V s a :-* V s b) s) => Show (L s a b)

flatten :: (Foldable (V s a), Foldable (V s b)) => L s a b -> [[s]]
flatten = fmap toList . toList . unpack

instance (Foldable (V s a), Foldable (V s b), Show s) => Show (L s a b) where
  show = show . flatten

instance (Foldable (V s a), Foldable (V s b), Pretty s) => Pretty (L s a b) where
  pPrint = pPrint . flatten

-- TODO: maybe 2D matrix form.

-- Just for AbsTy in ConCat.Circuit
instance Newtype (L s a b) where
  type O (L s a b) = (V s a :-* V s b) s
  pack ab = L ab
  unpack (L ab) = ab

instance HasRep (L s a b) where
  type Rep (L s a b) = (V s a :-* V s b) s
  abst ab = L ab
  repr (L ab) = ab
  {-# INLINE abst #-}
  {-# INLINE repr #-}

-- instance HasV s (L s a b) where
--   type V s (L s a b) = V s b :.: V s a
--   toV = abst . repr
--   unV = abst . repr

instance HasV s (Rep (L s a b)) => HasV s (L s a b)

type OkLF f = (Foldable f, Zeroable f, Zip f, Diagonal f)

type OkLM' s a = (Num s, HasV s a, OkLF (V s a))

class    (Num s, HasV s a, OkLF (V s a)) => OkLM s a
instance (Num s, HasV s a, OkLF (V s a)) => OkLM s a

zeroLM :: (Num s, Zeroable (V s a), Zeroable (V s b)) => L s a b
zeroLM = L zeroL
{-# INLINE zeroLM #-}

addLM :: Ok2 (L s) a b => Binop (L s a b)
addLM = (inNew2.zipWith.zipWith) (+)

instance Ok2 (L s) a b => Ad.Additive (L s a b) where
  zero  = zeroLM
  (^+^) = addLM

instance Category (L s) where
  type Ok (L s) = OkLM s
  id = abst idL
  (.) = inAbst2 compL
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance OpCon (:*) (Sat (OkLM s)) where inOp = Entail (Sub Dict)
-- instance OpCon (->) (Sat (OkLM s)) where inOp = Entail (Sub Dict)

instance ProductCat (L s) where
  -- type Prod (L s) = (,)
  exl = abst exlL
  exr = abst exrL
  (&&&) = inAbst2 forkL
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

instance CoproductCatD (L s) where
  inlD = abst inlL
  inrD = abst inrL
  (||||) = inAbst2 joinL
  {-# INLINE inlD #-}
  {-# INLINE inrD #-}
  {-# INLINE (||||) #-}

instance (r ~ Rep a, V s r ~ V s a, Ok (L s) a) => RepCat (L s) a r where
  reprC = L idL
  abstC = L idL

-- idL :: (a :-* a) s
--     ~  V s (V s a s)
-- L id  :: V s (V s a s)
--       ~  V s (V s r s)

#if 0
instance (Ok2 (L s) a b, Coercible (V s a) (V s b)) => CoerceCat (L s) a b where
  coerceC = coerce (id :: L s a a)
#else
instance ( -- Ok2 (L s) a b
           Num s, Diagonal (V s a)
         -- , Coercible (V s a) (V s b)
         , Coercible (Rep (L s a a)) (Rep (L s a b))
         -- , Coercible (V s a (V s a s)) (V s b (V s a s))
         ) => CoerceCat (L s) a b where
  -- coerceC = coerce (id :: L s a a)
  coerceC = L (coerce (idL :: Rep (L s a a)))
#endif

-- -- Okay:
-- foo :: L Float (L Float Float Float) (Par1 (V Float Float Float))
-- foo = coerceC
-- -- foo = L (coerce (idL :: Rep (L Float Float Float)))

-- -- -- Fail
-- foo :: L Float (L Float Float (Float, Float)) ((Par1 :*: Par1) (V Float Float Float))
-- foo = coerceC
-- -- foo = L (coerce (idL :: Rep (L Float Float Float)))

-- -- 
-- foo :: Rep (L Float (L Float Float (Float, Float)) ((Par1 :*: Par1) (V Float Float Float)))
-- foo = coerce (idL :: Rep (L Float Float Float))


-- We can't make a ClosedCat instance compatible with the ProductCat instance.
-- We'd have to change the latter to use the tensor product.

-- type instance Exp (L s) = (:.:)

-- Conversion to linear function
lapply :: (Num s, Ok2 (L s) a b) => L s a b -> (a -> b)
lapply (L gfa) = unV . lapplyL gfa . toV
{-# INLINE lapply #-}

type HasL s a = (HasV s a, Diagonal (V s a), Num s)  

type HasLin s a b =
  (HasV s a, HasV s b, Diagonal (V s a), Representable (V s b), Num s)  

linear :: forall s a b. HasLin s a b => (a -> b) -> L s a b
linear f = L (linearF (inV f))
{-# INLINE linear #-}

linearF :: forall s f g. (Diagonal f, Representable g, Num s)
        => (f s -> g s) -> (f :-* g) s
-- linearF q = undual <$> distribute q
-- linearF q = distribute (q <$> idL)
-- linearF q = distribute (fmap q idL)
-- linearF q = collect q idL
linearF = flip collect idL
{-# INLINE linearF #-}

-- q :: f s -> g s
--   :: (->) (f s) (g s)
-- distribute q :: g (f s -> s)
-- undual <$> distribute q :: g (f s)
--                         == (f :-* g) s

-- undual :: (Diagonal f, Num s) => (f s -> s) -> f s
-- undual p = p <$> idL

-- q :: f s -> g s
-- idL :: f (f s)
-- fmap q idL :: f (g s)
-- distribute (fmap q idL) :: g (f s)

-- collect :: (Distributive g, Functor f) => (a -> g b) -> f a -> g (f b)
-- collect f = distribute . fmap f

scalarMul :: OkLM s a => s -> L s a a
scalarMul = L . scaleL

negateLM :: OkLM s a => L s a a
negateLM = scalarMul (-1)

#if 0

{--------------------------------------------------------------------
    Functors
--------------------------------------------------------------------}

data Lapply s

instance FunctorC (Lapply s) (L s) (->) where fmapC = lapply

data Linear s

instance FunctorC (Linear s) (->) (L s) where fmapC = linear

#endif

{--------------------------------------------------------------------
    CCC conversion
--------------------------------------------------------------------}

lmap :: forall s a b. (a -> b) -> L s a b
lmap _ = oops "lmap called"
{-# NOINLINE lmap #-}
{-# RULES "lmap" forall h. lmap h = toCcc h #-}
{-# ANN lmap (PseudoFun 1) #-}

{--------------------------------------------------------------------
   Some specializations 
--------------------------------------------------------------------}

#if 0

type One = Par1
type Two = One :*: One

-- Becomes (*) (and casts)
{-# SPECIALIZE compL :: Num s =>
  (One :-* One) s -> (One :-* One) s -> (One :-* One) s #-}

-- Becomes timesFloat
{-# SPECIALIZE compL ::
  (One :-* One) Float -> (One :-* One) Float -> (One :-* One) Float #-}

-- Becomes + (* ww1 ww4) (* ww2 ww5)
{-# SPECIALIZE compL :: Num s =>
  (Two :-* One) s -> (One :-* Two) s -> (One :-* One) s #-}

-- Becomes plusFloat# (timesFloat# x y) (timesFloat# x1 y1)
{-# SPECIALIZE compL ::
  (Two :-* One) Float -> (One :-* Two) Float -> (One :-* One) Float #-}

type LRRR = L Float Float Float

-- Becomes timesFloat (and casts)
{-# SPECIALIZE (.) :: LRRR -> LRRR -> LRRR #-}

#endif

-- Experiment

{-# RULES

-- "assoc L (.) right" forall (f :: L s a b) g h. (h . g) . f = h . (g . f)

-- Alternatively (but not both!),

-- "assoc L (.) left"  forall (f :: L s a b) g h. h . (g . f) = (h . g) . f

 #-}

