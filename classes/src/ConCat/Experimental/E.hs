{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
-- {-# LANGUAGE ExplicitForAll #-}

-- TODO: trim pragmas

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Like D, but with Arr as newtype

module ConCat.Experimental.E where

import Prelude hiding (id,(.),curry,uncurry,const)
import qualified Prelude as P

import Data.Kind (Type,Constraint)

#ifdef DefaultCat
import qualified Control.Category as C
#endif
import Control.Arrow (Kleisli(..),arr)
import qualified Control.Arrow as A
import Control.Applicative (liftA2)
import Control.Monad ((<=<))
-- import Data.Proxy (Proxy)
import Data.Typeable (Typeable)
import GHC.Exts (Coercible,coerce)
import Data.Type.Equality ((:~:)(..))
import qualified Data.Type.Equality as Eq
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Coercion as Co
import GHC.Types (Constraint)
import Data.Constraint hiding ((&&&),(***),(:=>))
import qualified Data.Constraint as K
-- import GHC.Types (type (*))  -- experiment with TypeInType
import GHC.TypeLits
import Data.Array (Array,(!))
import qualified Data.Array as Arr
import Data.Proxy (Proxy(..))
import GHC.Generics ((:*:)(..),(:.:)(..))

import Control.Newtype.Generics (Newtype(..))
#ifdef VectorSized
import Data.Finite (Finite)
import Data.Vector.Sized (Vector)
import qualified Data.Vector.Sized as VS
#endif

-- import Data.MemoTrie

import ConCat.Misc hiding ((<~),(~>),type (&&))
import qualified ConCat.Misc as M
import ConCat.Rep
-- import ConCat.Orphans ()
-- import ConCat.Additive (Additive)

#define PINLINER(nm) {-# INLINE nm #-}
-- #define PINLINER(nm)

--------------------------------------------------
-- * Constraints

type Ok2 k a b         = (Ok k a, Ok k b)
type Ok3 k a b c       = (Ok k a, Ok k b, Ok k c)
type Ok4 k a b c d     = (Ok k a, Ok k b, Ok k c, Ok k d)

infixl 1 <+
-- | Wrapper
(<+) :: (b => r) -> (a :- b) -> (a => r)
(<+) = (\\)
-- r <+ Sub Dict = r
{-# INLINE (<+) #-}

--------------------------------------------------
-- * Categories

type Arr' k a b = F k a `k` F k b
newtype Arr k a b = Arr (Arr' k a b)

instance Newtype (Arr k a b) where
  type O (Arr k a b) = Arr' k a b
  pack f = Arr f
  unpack (Arr f) = f

class Category k where
  type F k (t :: Type) :: u
  type Ok k (t :: Type) :: Constraint
  type Ok k t = ()
  id :: Ok k a => Arr k a a
  infixr 9 .
  (.) :: forall a b c. Ok3 k a b c => Arr k b c -> Arr k a b -> Arr k a c

-- Experiment: unwrapped version.
infixr 9 @.
(@.) :: forall k a b c. (Category k, Ok3 k a b c)
     => Arr' k b c -> Arr' k a b -> Arr' k a c
g @. f = unpack ((pack g :: Arr k b c) . (pack f :: Arr k a b))

infixl 1 <~
-- | Add post- and pre-processing
(<~) :: forall k a b a' b'. (Category k, Ok4 k a b a' b')
     => Arr k b b' -> Arr k a' a -> (Arr k a b -> Arr k a' b')
-- (h <~ f) g = (.) @k @a' @b @b' h ((.) @k @a' @a @b g f)
(h <~ f) g = h . g . f

-- h :: Arr k b b'
-- f :: Arr k a' a
-- g :: Arr k a b

-- g . f :: Arr k a' b

-- h . (g . f) :: Arr k a' b'

infixr 1 ~>
-- | Add pre- and post-processing
(~>) :: forall k a b a' b'. (Category k, Ok4 k a b a' b')
     => Arr k a' a -> Arr k b b' -> (Arr k a b -> Arr k a' b')
(~>) = flip (<~)
-- f ~> h = (<~) @k @a @b @a' @b' h f

class OkProd k where okProd :: Ok2 k a b :- Ok k (a :* b)

class (Category k, OkProd k) => Cartesian k where
  exl :: forall a b. Ok2 k a b => Arr k (a :* b) a
  exr :: forall a b. Ok2 k a b => Arr k (a :* b) b
  infixr 3 &&&
  (&&&) :: forall a c d. Ok3 k a c d
        => Arr k a c -> Arr k a d -> Arr k a (c :* d)

infixr 3 ***
(***) :: forall k a b c d. (Cartesian k, Ok4 k a b c d)
      => Arr k a c -> Arr k b d -> Arr k (a :* b) (c :* d)
f *** g = f . exl &&& g . exr
-- f *** g = (&&&) @k @(a :* b) @c @d
--             (((.) @k @(a :* b) @a @c) f (exl @k @a @b))
--             (((.) @k @(a :* b) @b @d) g (exr @k @a @b))
  <+ okProd @k @a @b

first :: forall k a b c. (Cartesian k, Ok3 k a b c)
      => Arr k a c -> Arr k (a :* b) (c :* b)
first f = f *** id
-- first f = (***) @k @a @b @c @b f (id @k @b)

second :: forall k a b d. (Cartesian k, Ok3 k a b d)
       => Arr k b d -> Arr k (a :* b) (a :* d)
second g = id *** g
-- second g = (***) @k @a @b @a @d (id @k @a) g

class OkCoprod k where okCoprod :: Ok2 k a b :- Ok k (a :+ b)

-- | Category with coproduct.
class (Category k, OkCoprod k) => Cocartesian k where
  inl :: Ok2 k a b => Arr k a (a :+ b)
  inr :: Ok2 k a b => Arr k b (a :+ b)
  infixr 2 |||
  (|||) :: Ok3 k a c d => Arr k c a -> Arr k d a -> Arr k (c :+ d) a

infixr 3 +++
(+++) :: forall k a b c d. (Cocartesian k, Ok4 k a b c d)
      => Arr k c a -> Arr k d b -> Arr k (c :+ d) (a :+ b)
-- f +++ g = (|||) @k @(a :+ b) @c @d
--             (((.) @k @c @a @(a :+ b)) (inl @k @a @b) f)
--             (((.) @k @d @b @(a :+ b)) (inr @k @a @b) g)
--   <+ okCoprod @k @a @b

f +++ g = inl . f ||| inr . g <+ okCoprod @k @a @b

-- f :: c `k` a
-- g :: d `k` b

-- inl :: a `k` (a :+ b)
-- inr :: b `k` (a :+ b)

-- inl . f :: c `k` (a :+ b)
-- inr . g :: d `k` (a :+ b)

left :: forall k a b c. (Cocartesian k, Ok3 k a b c)
     => Arr k c a -> Arr k (c :+ b) (a :+ b)
left f = f +++ id
-- left f = (+++) @k @a @b @c @b f (id @k @b)

right :: forall k a b d. (Cocartesian k, Ok3 k a b d)
      => Arr k d b -> Arr k (a :+ d) (a :+ b)
right g = id +++ g
-- right g = (+++) @k @a @b @a @d (id @k @a) g

class (Cartesian k, Cocartesian k) => Distributive k where
  distl :: Ok3 k a u v => Arr k (a :* (u :+ v)) (a :* u :+ a :* v)

class OkExp k where okExp :: Ok2 k a b :- Ok k (a -> b)

class (Cartesian k, OkExp k) => CartesianClosed k where
  apply :: forall a b. Ok2 k a b => Arr k ((a -> b) :* a) b
  -- apply = uncurry id
  apply = uncurry id
          -- uncurry @k @(a -> b) @a @b (id @k @(a -> b))
            <+ okExp @k @a @b
  curry   :: forall a b c. Ok3 k a b c => Arr k (a :* b) c -> Arr k a (b -> c)
  uncurry :: forall a b c. Ok3 k a b c
          => Arr k a (b -> c) -> Arr k (a :* b) c
  uncurry g = apply . first g
  -- uncurry g = (.) @k @(a :* b) @((b -> c) :* b) @c
  --               (apply @k @b @c)
  --               (first @k @a @b @(b -> c) g)
             <+ okProd @k @(b -> c) @b
             <+ okProd @k @a @b
             <+ okExp  @k @b @c
  {-# MINIMAL curry, (apply | uncurry) #-}

--         id :: Arr k (a -> b) (a -> b)
--            :: F (a -> b) `k` F (a -> b)
-- uncurry id :: F ((a -> b) :* a) -> b

--       g :: Arr k a (b -> c)
-- first g :: Arr k (a :* b) ((b -> c) :* b)
-- apply   :: Arr k ((b -> c) :* b) c

--------------------------------------------------
-- * Category of functions

instance Category (->) where
  type F (->) t = t
  id  = pack P.id
  (.) = inNew2 (P..)

instance OkProd (->) where okProd = Sub Dict

instance Cartesian (->) where
  exl = pack fst
  exr = pack snd
  (&&&) = inNew2 (A.&&&)

instance OkCoprod (->) where okCoprod = Sub Dict

instance Cocartesian (->) where
  inl = pack Left
  inr = pack Right
  (|||) = inNew2 (A.|||)

instance Distributive (->) where
  distl = pack (\ (a,uv) -> ((a,) A.+++ (a,)) uv)

instance OkExp (->) where okExp = Sub Dict

instance CartesianClosed (->) where
  apply = pack (P.uncurry ($))
  curry = inNew P.curry
  uncurry = inNew P.uncurry

-- ccc :: (a -> b) -> Arr k a b

--------------------------------------------------
-- * Category of constraints with entailment

type family AsCon (a :: Type) :: Constraint

type instance AsCon (Dict c) = c
type instance AsCon (a :* b) = (AsCon a, AsCon b)

instance Category (:-) where
  type F (:-) c = AsCon c
  -- id :: forall a. AsCon a :- AsCon a
  id = pack refl
  (.) = inNew2 trans

-- We could move AsCon into a type family used to define Ok (:-)

instance OkProd (:-) where okProd = Sub Dict

instance Cartesian (:-) where
  exl = pack weaken1
  exr = pack weaken2
  (&&&) = inNew2 (K.&&&)

-- No Cocartesian or CartesianClosed

--------------------------------------------------
-- * Non-standard types via standard types

#if 0

class HasStd a where
  type Standard a
  toStd :: a -> Standard a
  unStd :: Standard a -> a
  default toStd :: (HasRep a, HasStd (Rep a), Standard a ~ Standard (Rep a)) => a -> Standard a
  default unStd :: (HasRep a, HasStd (Rep a), Standard a ~ Standard (Rep a)) => Standard a -> a
  toStd = toStd . repr
  unStd = abst . unStd

instance (HasStd a, HasStd b) => HasStd (a :* b) where
  type Standard (a :* b) = Standard a :* Standard b
  toStd = toStd *** toStd
  unStd = unStd *** unStd

instance (HasStd a, HasStd b) => HasStd (a :+ b) where
  type Standard (a :+ b) = Standard a :+ Standard b
  toStd = toStd +++ toStd
  unStd = unStd +++ unStd

instance (HasStd a, HasStd b) => HasStd (a -> b) where
  type Standard (a -> b) = Standard a -> Standard b
  toStd = toStd <~ unStd
  unStd = unStd <~ toStd

newtype StdFun a b = StdFun (Standard a -> Standard b)

instance Newtype (StdFun a b) where
  type O (StdFun a b) = Standard a -> Standard b
  pack f = StdFun f
  unpack (StdFun f) = f

instance Category StdFun where
  type F StdFun a = Standard a
  id :: StdFun a a
  id = pack id
  (.) :: StdFun b c -> StdFun a b -> StdFun a c
  (.) = inNew2 (.)

instance OkProd StdFun where okProd = Sub Dict

instance Cartesian StdFun where
  exl = pack exl
  exr = pack exr
  (&&&) = inNew2 (&&&)

instance OkCoprod StdFun where okCoprod = Sub Dict

instance Cocartesian StdFun where
  inl = pack inl
  inr = pack inr
  (|||) = inNew2 (|||)

instance OkExp StdFun where okExp = Sub Dict

instance CartesianClosed StdFun where
  apply = pack apply
  curry (StdFun f) = StdFun (curry f)
  uncurry (StdFun g) = StdFun (uncurry g)

#else

-- Generalize from (->) to arbitrary category

-- The specialized and generalized catgories both work. I don't know what value the
-- more general version (StdArr) adds, since we could start by converting to StdFun.

class (Category k) => RepCat k a r | a -> r where
  reprC :: Ok2 k a r => Arr k a r
  abstC :: Ok2 k a r => Arr k r a

instance (HasRep a, r ~ Rep a) => RepCat (->) a r where
  reprC = pack repr
  abstC = pack abst

class {- Ok2 k a (Standard k a) => -} HasStd k a where
  type Standard k a
  toStd :: Ok2 k a (Standard k a) => Arr k a (Standard k a)
  unStd :: Ok2 k a (Standard k a) => Arr k (Standard k a) a
  default toStd :: forall r. (RepCat k a r, HasStd k r, Standard k a ~ Standard k r, Ok3 k a r (Standard k r))
                => Arr k a (Standard k a)
  toStd = (.) @k @a @r @(Standard k r) (toStd @k @r) (reprC @k @a @r)
  default unStd :: forall r. (RepCat k a r, HasStd k r, Standard k a ~ Standard k r, Ok3 k a r (Standard k r))
                => Arr k (Standard k a) a
  unStd = (.) @k @(Standard k r) @r @a (abstC @k @a @r) (unStd @k @r)

-- instance (Cartesian k, HasStd k a, HasStd k b) =>
--          HasStd k (a :* b) where
--   type Standard k (a :* b) = Standard k a :* Standard k b
--   -- toStd = toStd *** toStd
--   -- unStd = unStd *** unStd

-- instance (HasStd k a, HasStd k b) => HasStd k (a :+ b) where
--   type Standard k (a :+ b) = Standard k a :+ Standard k b
--   toStd = toStd +++ toStd
--   unStd = unStd +++ unStd

-- instance (HasStd k a, HasStd k b) => HasStd k (a -> b) where
--   type Standard k (a -> b) = Standard k a -> Standard k b
--   toStd = toStd <~ unStd
--   unStd = unStd <~ toStd

newtype StdArr k a b = StdArr (Arr k (Standard k a) (Standard k b))

instance Newtype (StdArr k a b) where
  type O (StdArr k a b) = Arr k (Standard k a) (Standard k b)
  pack f = StdArr f
  unpack (StdArr f) = f

class    Ok k (Standard k a) => OkStd k a
instance Ok k (Standard k a) => OkStd k a

instance Category k => Category (StdArr k) where
  type Ok (StdArr k) a = OkStd k a
  type F (StdArr k) a = a
  id :: forall a. Ok (StdArr k) a => Arr (StdArr k) a a
  id = pack (pack (id @k @(Standard k a)))
  (.) :: forall a b c. Ok3 (StdArr k) a b c
      => Arr (StdArr k) b c -> Arr (StdArr k) a b -> Arr (StdArr k) a c
  (.) = inNew2 (inNew2 ((.) @k @(Standard k a) @(Standard k b) @(Standard k c)))

-- Continue here when the HasStd instances are in place.

-- instance OkProd (StdArr k) where okProd = Sub Dict

-- instance Cartesian (StdArr k) where
--   exl = pack exl
--   exr = pack exr
--   (&&&) = inNew2 (&&&)

-- instance OkCoprod (StdArr k) where okCoprod = Sub Dict

-- instance Cocartesian (StdArr k) where
--   inl = pack inl
--   inr = pack inr
--   (|||) = inNew2 (|||)

-- instance OkExp (StdArr k) where okExp = Sub Dict

-- instance CartesianClosed (StdArr k) where
--   apply = pack apply
--   curry ((StdArr k) f) = (StdArr k) (curry f)
--   uncurry ((StdArr k) g) = (StdArr k) (uncurry g)

#endif

-- TODO: Cartesian, Cocartesian, Closed

--------------------------------------------------
-- * Linear maps

type RepHasV s a = (HasRep a, HasV s (Rep a), V s a ~ V s (Rep a))

class HasV s a where
  type V s a :: Type -> Type
  toV :: a -> V s a s
  unV :: V s a s -> a
  -- Default via Rep.
  type V s a = V s (Rep a)
  default toV :: RepHasV s a => a -> V s a s
  default unV :: RepHasV s a => V s a s -> a
  toV = toV P.. repr
  unV = abst P.. unV

inV :: (HasV s a, HasV s b) => (a -> b) -> (V s a s -> V s b s)
-- inV = toV <~ unV
inV = toV M.<~ unV

onV :: (HasV s a, HasV s b) => (V s a s -> V s b s) -> (a -> b)
onV = unV M.<~ toV

onV2 :: (HasV s a, HasV s b, HasV s c) => (V s a s -> V s b s -> V s c s) -> (a -> b -> c)
onV2 = onV M.<~ toV

newtype LMap (s :: Type) (f :: Type -> Type) (g :: Type -> Type) = LMap (g (f s))

instance Newtype (LMap s f g) where
  type O (LMap s f g) = g (f s)
  pack gf = LMap gf
  unpack (LMap gf) = gf

type OkLF (f :: Type -> Type) = (() :: Constraint) -- we'll see

idLM :: forall s f. OkLF f => LMap s f f
idLM = undefined

compLM :: OkLF f => LMap s g h -> LMap s f g -> LMap s f h
compLM = undefined

instance Category (LMap s) where
  type Ok (LMap s) a = (Num s, OkLF (V s a))
  type F (LMap s) a = V s a
  id = pack idLM
  (.) = inNew2 compLM

-- exlLM :: forall s a b. (OkLF a, OkLF b) => LMap s (a :*: b) a
-- exrLM :: forall s a b. (OkLF a, OkLF b) => LMap s (a :*: b) b
-- forkLM :: forall s a c d. (OkLF a, OkLF c, OkLF d)
--        => LMap s a c -> LMap s a d -> LMap s a (c :*: d)

-- instance Cartesian (LMap s) where

--------------------------------------------------
-- * Product categories


infixr 7 :**:
-- | Category of products
data (k :**: k') a b = Arr k a b :**: Arr k' a b

instance (Category k, Category k') => Category (k :**: k') where
  type Ok (k :**: k') a = (Ok k a, Ok k' a)
  type F (k :**: k') a = a  -- guess, since rep has Fs
  id :: forall a. Ok (k :**: k') a => Arr (k :**: k') a a
  id = pack (id :**: id)
  -- id = id @k @a :**: id @k' @a
  (.) :: forall a b c. Ok3 (k :**: k') a b c
      => Arr (k :**: k') b c -> Arr (k :**: k') a b -> Arr (k :**: k') a c
  -- Arr (g :**: g') . Arr (f :**: f') = Arr ((g . f) :**: (g' . f'))
  (.) = inNew2 (\ (g :**: g') (f :**: f') -> ((g . f) :**: (g' . f')))
  -- Arr (g :**: g') . Arr (f :**: f') = Arr ((g . f) :**: (g' . f'))
  -- (g :**: g') . (f :**: f') = (.) @k @a @b @c g f :**: (.) @k' @a @b @c g' f'
