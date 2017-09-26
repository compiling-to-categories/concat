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

-- | Linear maps as "column-major" functor compositions

module ConCat.Free.LinearCol where

import Prelude hiding (id,(.),zipWith)
import GHC.Exts (Coercible,coerce)
import Data.Foldable (toList)
import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:.:)(..))
import Data.Constraint

import Data.Key (Zip(..))
import Text.PrettyPrint.HughesPJClass hiding (render)
import Control.Newtype

import ConCat.Misc ((:*),PseudoFun(..),oops,R)
import ConCat.Orphans ()
import ConCat.Free.VectorSpace
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Rep
import ConCat.Free.Diagonal

{--------------------------------------------------------------------
    Linear maps
--------------------------------------------------------------------}

-- Linear map from a s to b s
infixr 1 :-*
type (a :-* b) s = a (b s)

-- TODO: consider instead
-- 
--   type Linear = (:.:)
-- 
-- so that Linear itself forms a vector space.

-- Apply a linear map
infixr 9 $*
($*), lapplyL :: (Zip a, Foldable a, Zip b, Zeroable b, Num s)
              => (a :-* b) s -> a s -> b s
bs $* a = sumV (zipWith (*^) a bs)

lapplyL = ($*)

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
idL :: (Diagonal a, Num s)
    => (a :-* a) s
idL = scaleL 1

-- Compose linear transformations
compL :: (Functor a, Foldable b, Zip b, Zeroable c, Zip c, Num s)
      => (b :-* c) s -> (a :-* b) s -> (a :-* c) s
bc `compL` ab = (bc $*) <$> ab
-- compL = fmap . ($*)

---- Product

exlL :: (Zeroable a, Diagonal a, Zeroable b, Num s)
     => (a :*: b :-* a) s
exlL = idL :*: zeroL

exrL :: (Zeroable b, Diagonal b, Zeroable a, Num s)
     => (a :*: b :-* b) s
exrL = zeroL :*: idL

forkL :: Zip a => (a :-* b) s -> (a :-* c) s -> (a :-* b :*: c) s
forkL = zipWith (:*:)

-- itL :: (a :-* U1) s
-- itL = point U1

---- Coproduct as direct sum (represented as Cartesian product)

inlL :: (Zeroable a, Diagonal a, Zeroable b, Num s)
     => (a :-* a :*: b) s
inlL = (:*: zeroV) <$> idL

inrL :: (Zeroable a, Zeroable b, Diagonal b, Num s)
     => (b :-* a :*: b) s
inrL = (zeroV :*:) <$> idL

joinL :: (a :-* c) s -> (b :-* c) s -> (a :*: b :-* c) s
joinL = (:*:)

{--------------------------------------------------------------------
    Category
--------------------------------------------------------------------}

newtype L s a b = L ((V s a :-* V s b) s)

type LR = L R

-- deriving instance Show ((V s a :-* V s b) s) => Show (L s a b)

flatten :: (Foldable (V s a), Foldable (V s b)) => L s a b -> [[s]]
flatten = fmap toList . toList . unpack

instance (Foldable (V s a), Foldable (V s b), Show s) => Show (L s a b) where
  show = show . flatten

instance (Foldable (V s a), Foldable (V s b), Pretty s) => Pretty (L s a b) where
  pPrint = pPrint . flatten

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

instance HasV s (L s a b) where
  type V s (L s a b) = V s a :.: V s b
  toV = abst . repr
  unV = abst . repr

type OkLF' f = (Foldable f, Zeroable f, Zip f, Diagonal f)

type OkLM' s a = (Num s, HasV s a, HasL (V s a)) -- , OkLF' (V s a)

-- I'd like to use OkLF' in place of HasL, but the plugin isn't able to find Ok
-- (L Float) Float. I suspect that the problem is due to orphan instances.

class    OkLM' s a => OkLM s a
instance OkLM' s a => OkLM s a

-- instance Zeroable (L s a) where zeroV = L zeroV

zeroLM :: (Num s, Zeroable (V s a), Zeroable (V s b)) => L s a b
zeroLM = L zeroL

instance Category (L s) where
  type Ok (L s) = OkLM s
  id = abst idL
  (.) = inAbst2 compL
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance OpCon (:*) (Sat (OkLM s)) where inOp = Entail (Sub Dict)

instance ProductCat (L s) where
  -- type Prod (L s) = (,)
  exl = abst exlL
  exr = abst exrL
  (&&&) = inAbst2 forkL
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

-- Can I still have coproducts? Seems problematic without a definable Coprod

-- instance CoproductCat (L s) where
--   -- type Coprod (L s) = (,)
--   inl = abst inlL
--   inr = abst inrL
--   (|||) = inAbst2 joinL

inlLM :: Ok2 (L s) a b => L s a (a :* b)
inlLM = abst inlL

inrLM :: Ok2 (L s) a b => L s b (a :* b)
inrLM = abst inrL

joinLM :: L s a c -> L s b c -> L s (a :* b) c
joinLM = inAbst2 joinL

jamLM :: Ok (L s) a => L s (a :* a) a
jamLM = id `joinLM` id

instance (r ~ Rep a, V s r ~ V s a, Ok (L s) a) => RepCat (L s) a r where
  reprC = L idL
  abstC = L idL

-- idL :: (a :-* a) s
--     ~  V s (V s a s)
-- L id  :: V s (V s a s)
--       ~  V s (V s r s)

#if 0
instance (Ok2 (L s) a b
         -- , Coercible (V s a) (V s b)
         , V s a ~ V s b
         ) => CoerceCat (L s) a b where
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

-- With Coercible instead of ~, we get a type error:
--
--     • Could not deduce: Coercible ((:-*) (V s b) (V s b) s)
--                                   ((:-*) (V s b) (V s a) s)
--         arising from a use of ‘coerce’
--       from the context: (Ok (L s) a, Coercible (V s a) (V s b))
--         bound by the instance declaration
--         at /Users/conal/Haskell/concat/src/ConCat/Free/LinearCol.hs:(209,10)-(212,33)
--       NB: We cannot know what roles the parameters to ‘V s b’ have;
--         we must assume that the role is nominal
--       NB: ‘V’ is a type function, and may not be injective
--     • In the expression: coerce (id :: L s a a)
--       In an equation for ‘coerceC’: coerceC = coerce (id :: L s a a)
--       In the instance declaration for ‘CoerceCat (L s) a b’
--     • Relevant bindings include
--         coerceC :: L s a b
--           (bound at /Users/conal/Haskell/concat/src/ConCat/Free/LinearCol.hs:213:3)
--
-- Why does the Coercible constraint suffice for LinearRow but not LinearCol?

-- We can't make a ClosedCat instance compatible with the ProductCat instance.
-- We'd have to change the latter to use the tensor product.

-- type instance Exp (L s) = (:.:)

-- Conversion to linear map
lapply :: (Num s, Ok2 (L s) a b) => L s a b -> (a -> b)
-- lapply :: (Num s, HasV s a, HasV s b, Foldable (V s a), Zip (V s a), Zip (V s b)) => L s a b -> (a -> b)
lapply (L gfa) = unV . lapplyL gfa . toV

-- lapplyL :: ... => (a :-* b) s -> a s -> b s

class OkLF' f => HasL f where
  -- | Law: @'linearL . 'lapply' == 'id'@ (but not the other way around)
  linearL :: forall s g. (Num s, OkLF' g) => (f s -> g s) -> (f :-* g) s

instance HasL U1 where
  -- linearL :: forall s g. (Num s, OkLF' g) => (U1 s -> g s) -> (U1 :-* g) s
  linearL _ = U1

instance HasL Par1 where
  linearL f = Par1 (f (Par1 1))

--       f           :: Par1 s -> b s
--       f (Par1 1)  :: b s
-- Par1 (f (Par1 1)) :: Par1 (b s)

instance (HasL f, HasL g) => HasL (f :*: g) where
  linearL q = linearL (q . (:*: zeroV)) `joinL` linearL (q . (zeroV :*:))

--          q                :: (f :*: g) s -> h s
--              (:*: zeroV)  :: f s -> (f :*: g) s
--          q . (:*: zeroV)  :: f s -> h s
-- linearL (q . (:*: zeroV)) :: (f :-* h) s

linear :: (OkLM s a, OkLM s b) => (a -> b) -> L s a b
linear f = L (linearL (inV f))

-- f :: a -> b
-- inV f :: V s a s -> V s b s

scale :: OkLM s a => s -> L s a a
scale = L . scaleL

negateLM :: OkLM s a => L s a a
negateLM = scale (-1)

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
{-# ANN lmap PseudoFun #-}
