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

{-# OPTIONS_GHC -Wall #-}

-- | Linear maps as "row-major" functor compositions

module ConCat.Free.LinearRow where

import Prelude hiding (id,(.),zipWith)

import GHC.Generics (Par1(..),(:*:)(..),(:.:)(..))
import Data.Constraint

import Data.Pointed (Pointed(..))
import Data.Key (Keyed(..),Zip(..),Adjustable(..))

import Control.Newtype

import ConCat.Misc (inNew,inNew2)
import ConCat.Orphans ()
import ConCat.Free.VectorSpace
import ConCat.Category

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

zeroL :: (Pointed a, Pointed b, Num s) => (a :-* b) s
zeroL = point zeroV

#if 0
{--------------------------------------------------------------------
    Affine maps
--------------------------------------------------------------------}

-- Affine map from a s to b s
type Affine a b s = (a :*: Par1 :-* b) s

-- Apply an affine map
affine :: (Zip a, Foldable a, Zip b, Pointed b, Num s)
       => Affine a b s -> a s -> b s
affine bs' a = bs' $* (a :*: Par1 1)

-- Compose affine transformations
(@..) :: (Zip b, Zip c, Pointed c, Foldable b, Num s, Functor a)
      => Affine b c s -> Affine a b s -> Affine a c s
bc @.. ab = affine bc <$> ab
#endif

{--------------------------------------------------------------------
    Other operations
--------------------------------------------------------------------}

---- Category

-- Identity linear map
idL :: (Adjustable m, Keyed m, Pointed m, Num r)
    => (m :-* m) r
idL = mapWithKey (flip replace 1) zeroL

-- mapWithKey :: Keyed f => (Key f -> a -> b) -> f a -> f b
-- replace :: Adjustable f => Key f -> a -> f a -> f a

-- Compose linear transformations
(@.) :: (Zip a, Zip b, Pointed a, Foldable b, Functor c, Num s)
     => (b :-* c) s -> (a :-* b) s -> (a :-* c) s
-- bc @. ab = (bc $*) <$> ab

bc @. ab = (\ b -> sumV (zipWith (*^) b ab)) <$> bc

-- bc :: c (b s)
-- ab :: b (a s)

-- ac :: c (a s)

-- (bc $*) :: b s -> c s



-- (@.) = fmap . linear

#if 1
---- Product

exlL :: (Pointed a, Keyed a, Adjustable a, Pointed b, Num s)
     => (a :*: b :-* a) s
exlL = (:*: zeroV) <$> idL

exrL :: (Pointed b, Keyed b, Adjustable b, Pointed a, Num s)
     => (a :*: b :-* b) s
exrL = (zeroV :*:) <$> idL

forkL :: (a :-* b) s -> (a :-* c) s -> (a :-* b :*: c) s
forkL = (:*:)

---- Coproduct as direct sum (represented as Cartesian product)

inlL :: (Pointed a, Keyed a, Adjustable a, Pointed b, Num s)
     => (a :-* a :*: b) s
inlL = idL :*: zeroL

inrL :: (Pointed a, Pointed b, Keyed b, Adjustable b, Num s)
     => (b :-* a :*: b) s
inrL = zeroL :*: idL

joinL :: Zip c => (a :-* c) s -> (b :-* c) s -> (a :*: b :-* c) s
joinL = zipWith (:*:)

newtype (f :=> g) s = Fun ((f :-* g) s)

-- applyL :: _ => ((f :=> g) :*: f :-* g) s
-- applyL =

-- (f (g s) -> g (g s)) :* f (g s)

#if 1

{--------------------------------------------------------------------
    Experiment
--------------------------------------------------------------------}

type Linear' = (:.:)

linear' :: (Zip b, Zip a, Pointed b, Foldable a, Num s)
        => Linear' a b s -> a s -> b s
linear' (Comp1 ns) a = sumV (zipWith (*^) a ns)

zeroL' :: (Pointed b, Pointed a, Num s) => Linear' a b s
zeroL' = Comp1 (point zeroV)

idL' :: (Adjustable a, Keyed a, Pointed a, Num s)
     => Linear' a a s
idL' = (inNew . mapWithKey) (flip replace 1) zeroL'

(@@.) :: (Zip c, Zip b, Pointed c, Foldable b, Functor a, Num s)
      => Linear' b c s -> Linear' a b s -> Linear' a c s
(@@.) = inNew . fmap . linear'

-- (@@.) no = inNew (fmap (linear' no))
-- (@@.) no = inNew (linear' no <$>)
-- no @@. Comp1 mn = Comp1 (linear' no <$> mn)

exl' :: (Pointed a, Keyed a, Adjustable a, Pointed b, Num s)
     => Linear' (a :*: b) a s
-- exl' = inNew (idL :*:) zeroL'
exl' = inNew2 (:*:) idL' zeroL'

-- exlL = idL :*: zeroL

fork' :: Zip a => Linear' a b s -> Linear' a c s -> Linear' a (b :*: c) s
fork' = (inNew2 . zipWith) (:*:)

inl' :: (Pointed a, Keyed a, Adjustable a, Pointed b, Num s)
     => Linear' a (a :*: b) s
inl' = (inNew . fmap) (:*: zeroV) idL'

join' :: Linear' a c s -> Linear' b c s -> Linear' (a :*: b) c s
join' = inNew2 (:*:)

{--------------------------------------------------------------------
    Quantify over Num
--------------------------------------------------------------------}

type U a = forall s. Num s => a s

type Linear'' a b = U (a :.: b)

-- data Linear'' a b = forall s. L (Num s => (a :.: b) s)

type NT a b = forall s. Num s => a s -> b s

linear'' :: (Zip b, Zip a, Pointed b, Foldable a)
         => Linear'' a b -> NT a b
linear'' (Comp1 ns) a = sumV (zipWith (*^) a ns)

zeroL'' :: (Pointed b, Pointed a) => Linear'' a b
zeroL'' = Comp1 (point zeroV)

idL'' :: (Adjustable a, Keyed a, Pointed a)
      => Linear'' a a
idL'' = (inNew . mapWithKey) (flip replace 1) zeroL''

exl'' :: (Pointed a, Keyed a, Adjustable a, Pointed b)
      => Linear'' (a :*: b) a
exl'' = inNew (idL :*:) zeroL'

fork'' :: Zip a => Linear'' a b -> Linear'' a c -> Linear'' a (b :*: c)
fork'' = inNew2 (zipWith (:*:))
-- fork'' = (inNew2'' . zipWith) (:*:)

inl'' :: (Pointed a, Keyed a, Adjustable a, Pointed b)
      => Linear'' a (a :*: b)
inl'' = (inNew . fmap) (:*: zeroV) idL''

join'' :: Linear'' a c -> Linear'' b c -> Linear'' (a :*: b) c
join'' = inNew2 (:*:)

#endif

#if 0
{--------------------------------------------------------------------
    Constrained linear optimization
--------------------------------------------------------------------}

-- Affine function and affine constraints. When b == Id and s is
-- ordered, we can solve as a constrained linear optimization problem.
-- The generality over b improves composability.
data LinOpt a b s = forall c. Foldable c => LO (Affine a b s, Affine a c s)

-- TODO: add existentials by wrapping with ExistArg. I'll have to
-- bridge the gap between the Category classes and the
-- almost-instances above.

#endif

{--------------------------------------------------------------------
    Categorical instances
--------------------------------------------------------------------}

newtype LMapF s a b = LMapF ((a :-* b) s)

instance Newtype (LMapF s a b) where
  type O (LMapF s a b) = (a :-* b) s
  pack ab = LMapF ab
  unpack (LMapF ab) = ab

type OkLF a = (Foldable a, Pointed a, Zip a, Keyed a, Adjustable a)

class    (OkLF a, Num s) => OkLMapF s a
instance (OkLF a, Num s) => OkLMapF s a

instance Category (LMapF s) where
  type Ok (LMapF s) = OkLMapF s
  id = pack idL
  (.) = inNew2 (@.)

instance OpCon (:*:) (OkLMapF s) where inOp = Sub Dict

instance ProductCat (LMapF s) where
  type Prod (LMapF s) = (:*:)
  exl = pack exlL
  exr = pack exrL
  (&&&) = inNew2 forkL

instance CoproductCat (LMapF s) where
  type Coprod (LMapF s) = (:*:)
  inl = pack inlL
  inr = pack inrL
  (|||) = inNew2 joinL

-- We can't make a ClosedCat instance compatible with the ProductCat instance.
-- We'd have to change the latter to use the tensor product.

-- type instance Exp (LMapF s) = (:.:)

toExp :: LMapF s a b -> (b :.: a) s
toExp = pack . unpack
-- toExp (LMapF ab) = pack ab


#if 0
newtype LMapF' s a b = LMapF' ((a :.: b) s)
 deriving (Foldable, Pointed, Zip, Keyed, Adjustable)

-- • Cannot derive well-kinded instance of form ‘Foldable (LMapF' ...)’
--     Class ‘Foldable’ expects an argument of kind ‘* -> *’

instance Newtype (LMapF' s a b) where
  type O (LMapF' s a b) = (a :.: b) s
  pack ab = LMapF' ab
  unpack (LMapF' ab) = ab
#endif

#endif

#if 1

{--------------------------------------------------------------------
    Experiment: use value types instead of functors for domain & range
--------------------------------------------------------------------}

newtype LM s a b = LM ((V s a :-* V s b) s)

instance Newtype (LM s a b) where
  type O (LM s a b) = (V s a :-* V s b) s
  pack ab = LM ab
  unpack (LM ab) = ab

type OkLF' f = (Foldable f, Pointed f, Zip f, Keyed f, Adjustable f)

type OkLM' s a = (OkLF' (V s a), Num s)

class    OkLM' s a => OkLM s a
instance OkLM' s a => OkLM s a

instance Category (LM s) where
  type Ok (LM s) = OkLM s
  id = pack idL
  (.) = inNew2 (@.)

instance OpCon (,) (OkLM s) where inOp = Sub Dict

instance ProductCat (LM s) where
  type Prod (LM s) = (,)
  exl = pack exlL
  exr = pack exrL
  (&&&) = inNew2 forkL

instance CoproductCat (LM s) where
  type Coprod (LM s) = (,)
  inl = pack inlL
  inr = pack inrL
  (|||) = inNew2 joinL

-- We can't make a ClosedCat instance compatible with the ProductCat instance.
-- We'd have to change the latter to use the tensor product.

-- type instance Exp (LM s) = (:.:)

#endif

#if 0

-- Another experiment

-- data Vec s a = V (forall f. (V s a ~ f, OkLF' f, Num s) => f s)
data Vec s a = V (forall f. (V s a ~ f, OkLF' f, Num s) => f s)

data LMV s a b =
  LMV (forall g f. (V s a ~ f, V s b ~ g, OkLF' f, OkLF' g, Num s) => g (f s))

-- data LMV s a b =
--   LMV ((OkLM' s a, OkLM' s b, Num s, Foldable (V s b)) => V s b (V s a s))

-- data LMV s a b =
--   LMV (Dict (OkLM' s a, OkLM' s b, Num s, Foldable (V s b))) (V s b (V s a s))

instance Category (LMV s) where
  id = LMV idL
--  LMV gs . LMV fs = LMV (gs @. fs)

-- compV :: LMV s b c -> LMV s a b -> LMV s a c
-- LMV gs `compV` LMV fs = LMV (gs @. fs)

#endif

{--------------------------------------------------------------------
    Conversion to linear map
--------------------------------------------------------------------}

lapply :: (Num s, OkLF a, OkLF b) => LMapF s a b -> UT s a b
lapply = inNew lapplyL

#if 0

class (OkLMapF s a, OkLMapF s b) => HasL s a b where
  -- | Law: @'linear' . 'lapply' == 'id'@ (but not the other way around)
  linear :: UT s a b -> LMapF s a b

instance OkLMapF s a => HasL s Par1 a where
  linear (UT f) = LMapF (Par1 <$> f (Par1 1))

--                 f          :: Par1 s -> b s
--                 f (Par1 1) :: b s
--        Par1 <$> f (Par1 1) :: b (Par1 s)
-- LMapF (Par1 <$> f (Par1 1) :: LMapF s Par1 b

instance (HasL s a c, HasL s b c) => HasL s (a :*: b) c where
  linear f = linear (f . lapply inl) ||| linear (f . lapply inr)

-- lapply as functor

data Lapply s

instance FunctorC (Lapply s) (LMapF s) (UT s) where
  -- type OkF (Lapply s) = OkLMapF s
  type OkF (Lapply s) a b = (OkLMapF s a, OkLMapF s b)
  type Lapply s % a = a
  (%) = lapply

-- linear as functor

data Linear s

instance FunctorC (Linear s) (UT s) (LMapF s) where
  type OkF (Linear s) a b = HasL s a b
  type Linear s % a = a
  (%) = linear

#elif 0

class OkLMapF s a => HasL s a where
  -- | Law: @'linear' . 'lapply' == 'id'@ (but not the other way around)
  linear :: forall b. OkLMapF s b => UT s a b -> LMapF s a b

instance Num s => HasL s Par1 where
  linear (UT f) = LMapF (Par1 <$> f (Par1 1))

--                 f          :: Par1 s -> b s
--                 f (Par1 1) :: b s
--        Par1 <$> f (Par1 1) :: b (Par1 s)
-- LMapF (Par1 <$> f (Par1 1) :: LMapF s Par1 b

instance (HasL s a, HasL s b) => HasL s (a :*: b) where
  linear f = linear (f . lapply inl) ||| linear (f . lapply inr)

-- lapply as functor

data Lapply s

instance FunctorC (Lapply s) (LMapF s) (UT s) where
  -- type OkF (Lapply s) = OkLMapF s
  type OkF (Lapply s) a b = (OkLMapF s a, OkLMapF s b)
  type Lapply s % a = a
  (%) = lapply

-- linear as functor

data Linear s

instance FunctorC (Linear s) (UT s) (LMapF s) where
  -- type OkF (Linear s) = HasL s
  type OkF (Linear s) a b = (HasL s a, OkLF b)
  type Linear s % a = a
  (%) = linear

#else

class OkLF a => HasL a where
  -- | Law: @'linear' . 'lapply' == 'id'@ (but not the other way around)
  linear :: forall s b. (Num s, OkLF b) => UT s a b -> LMapF s a b

instance HasL Par1 where
  linear (UT f) = LMapF (Par1 <$> f (Par1 1))

--                 f          :: Par1 s -> b s
--                 f (Par1 1) :: b s
--        Par1 <$> f (Par1 1) :: b (Par1 s)
-- LMapF (Par1 <$> f (Par1 1) :: LMapF s Par1 b

instance (HasL a, HasL b) => HasL (a :*: b) where
  linear f = linear (f . lapply inl) ||| linear (f . lapply inr)

{--------------------------------------------------------------------
    Functors
--------------------------------------------------------------------}

-- lapply as functor
data Lapply s

instance FunctorC (Lapply s) (LMapF s) (UT s) where
  -- type OkF (Lapply s) = OkLMapF s
  -- type OkF (Lapply s) a = OkLMapF s a
  -- type OkF (Lapply s) a b = (Num s, OkLF a, OkLF b)
  type Lapply s % a = a
  fmapC = lapply

-- linear as functor
data Linear s

-- class    (Num s, HasL a) => OkLin s a
-- instance (Num s, HasL a) => OkLin s a

-- instance FunctorC (Linear s) (UT s) (LMapF s) where
--   -- type OkF (Linear s) = OkLin s
--   -- type OkF (Linear s) a = OkLin s a
--   -- type OkF (Linear s) a = (Num s, HasL a)
--   type OkF (Linear s) a b = (Num s, HasL a, OkLF b)
--   type Linear s % a = a
--   fmapC = linear

instance FunctorC (Linear s) (Constrained HasL (UT s)) (LMapF s) where
  -- type OkF (Linear s) a b = (Num s, HasL a, OkLF b)
  type Linear s % a = a
  fmapC (Constrained f) = linear f

#endif
