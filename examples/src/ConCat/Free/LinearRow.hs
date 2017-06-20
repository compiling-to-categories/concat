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
import ConCat.AltCat hiding (const)
import ConCat.Rep
import ConCat.Free.Diagonal

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
($*), lapplyL :: (Zip a, Foldable a, Zip b, Num s)
              => (a :-* b) s -> a s -> b s
as $* a = (<.> a) <$> as

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
compL :: (Zip a, Zip b, Zeroable a, Foldable b, Functor c, Num s)
     => (b :-* c) s -> (a :-* b) s -> (a :-* c) s
bc `compL` ab = (\ b -> sumV (zipWith (*^) b ab)) <$> bc

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

exrL :: (Zeroable b, Diagonal b, Zeroable a, Num s)
     => (a :*: b :-* b) s
exrL = (zeroV :*:) <$> idL

forkL :: (a :-* b) s -> (a :-* c) s -> (a :-* b :*: c) s
forkL = (:*:)

itL :: (a :-* U1) s
itL = U1

---- Coproduct as direct sum (represented as Cartesian product)

inlL :: (Zeroable a, Diagonal a, Zeroable b, Num s)
     => (a :-* a :*: b) s
inlL = idL :*: zeroL

inrL :: (Zeroable a, Zeroable b, Diagonal b, Num s)
     => (b :-* a :*: b) s
inrL = zeroL :*: idL

joinL :: Zip c => (a :-* c) s -> (b :-* c) s -> (a :*: b :-* c) s
joinL = zipWith (:*:)

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

#if 0
-- Convenient but lots of constraint solving work & volume
type OkLF f = (Foldable f, Zeroable f, Zip f, Diagonal f)
#else
-- Less convenient but perhaps easier on the compiler
class (Foldable f, Zeroable f, Zip f, Diagonal f) => OkLF f

instance OkLF U1
instance OkLF Par1
-- instance Eq k => OkLF ((->) k)
instance (OkLF f, OkLF g) => OkLF (f :*: g)
instance (OkLF f, OkLF g, Applicative f, Traversable g) => OkLF (g :.: f)
#endif

type OkLM' s a = (Num s, HasV s a, OkLF (V s a))

-- type OkLM' s a = (Num s, HasV s a, HasL (V s a))

class    OkLM' s a => OkLM s a
#if 1
-- Convenient but lots of constraint solving work & volume
instance OkLM' s a => OkLM s a
#else
-- Less convenient and perhaps less work for the compiler
instance OkLM Float Float
instance OkLM Double Double
instance (Num s) => OkLM s ()
instance (OkLM s a, OkLM s b) => OkLM s (a,b)
instance (Num s) => OkLM s (U1 a)
instance (Num s, HasV s a, OkLF (V s a)) => OkLM s (Par1 a)
instance (Num s, OkLM s (f a), OkLM s (g a)) => OkLM s ((f :*: g) a)
instance (Num s, OkLM s (g (f a))) => OkLM s ((g :.: f) a)
instance (Num s, OkLM s ((V s a :-* V s b) s)) => OkLM s (L s a b)
#endif

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
-- instance OpCon (->) (Sat (OkLM s)) where inOp = Entail (Sub Dict)

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

joinLM :: Ok3 (L s) a b c => L s a c -> L s b c -> L s (a :* b) c
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

-- lapplyL :: ... => (a :-* b) s -> a s -> b s

class OkLF f => HasL f where
  -- | Law: @'linearL . 'lapply' == 'id'@ (but not the other way around)
  linearL :: forall s g. (Num s, OkLF g) => (f s -> g s) -> (f :-* g) s

instance HasL U1 where
  -- linearL :: forall s g. (Num s, OkLF g) => (U1 s -> g s) -> (U1 :-* g) s
  -- linearL h = U1 <$ h U1
  linearL h = const U1 <$> h U1

--       h    :: U1 s -> g s
--       h U1 :: g s
-- U1 <$ h U1 :: g (U1 s)

instance HasL Par1 where
  linearL h = Par1 <$> h (Par1 1)

--          h          :: Par1 s -> b s
--          h (Par1 1) :: b s
-- Par1 <$> h (Par1 1) :: b (Par1 s)

instance (HasL f, HasL g) => HasL (f :*: g) where
  -- linearL h = linearL (h . (:*: zeroV)) `joinL` linearL (h . (zeroV :*:))
  linearL h = zipWith (:*:) (linearL (h . (:*: zeroV))) (linearL (h . (zeroV :*:)))

--          q                :: (f :*: g) s -> h s
--              (:*: zeroV)  :: f s -> (f :*: g) s
--          q . (:*: zeroV)  :: f s -> h s
-- linearL (q . (:*: zeroV)) :: (f :-* h) s

#if 0
instance (HasL f, HasL g) => HasL (g :.: f) where
  linearL q = ...

q :: ((g :.: f) s -> h s) -> ((g :.: f) :-* h) s
  =~ (g (f s) -> h s) -> h ((g :.: f) s)
  =~ (g (f s) -> h s) -> h (g (f s))
#endif

#if 0

instance HasL ((->) k) where
  linearL h = ...

h :: (k -> s) -> g s

want :: ((k -> s) :-* g) s
     :: g (k -> s)

#endif

linear :: (OkLM s a, OkLM s b, HasL (V s a)) => (a -> b) -> L s a b
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
-- lmap _ = error "lmap called"
lmap _ = oops "lmap"
{-# NOINLINE lmap #-}
{-# RULES "lmap" forall h. lmap h = ccc h #-}
{-# ANN lmap PseudoFun #-}

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

