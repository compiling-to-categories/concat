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

-- | Poly-kinded and type function F for something like general functors.

module ConCat.Experimental.C where

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
import ConCat.Rep
-- import ConCat.Orphans ()
-- import ConCat.Additive (Additive)

#define PINLINER(nm) {-# INLINE nm #-}
-- #define PINLINER(nm)

{--------------------------------------------------------------------
    Constraints
--------------------------------------------------------------------}

#if 0

type C1 (con :: u -> Constraint) a = con a
type C2 (con :: u -> Constraint) a b = (con a, con b)
type C3 (con :: u -> Constraint) a b c = (con a, con b, con c)
type C4 (con :: u -> Constraint) a b c d = (con a, con b, con c, con d)
type C5 (con :: u -> Constraint) a b c d e = (con a, con b, con c, con d, con e)
type C6 (con :: u -> Constraint) a b c d e f = (con a, con b, con c, con d, con e, con f)

type Ok2 k a b         = C2 (Ok k) a b
type Ok3 k a b c       = C3 (Ok k) a b c
type Ok4 k a b c d     = C4 (Ok k) a b c d
type Ok5 k a b c d e   = C5 (Ok k) a b c d e
type Ok6 k a b c d e f = C6 (Ok k) a b c d e f

#else

type Ok2 k a b         = (Ok k a, Ok k b)
type Ok3 k a b c       = (Ok k a, Ok k b, Ok k c)
type Ok4 k a b c d     = (Ok k a, Ok k b, Ok k c, Ok k d)

#endif

{--------------------------------------------------------------------
    Categories
--------------------------------------------------------------------}

type Arr k a b = F k a `k` F k b

type B u = u -> u -> Type

class Category (k :: B u) where
  type F k (t :: Type) :: u
  type Ok k :: Type -> Constraint
  type Ok k = Yes1
  id :: Ok k a => Arr k a a
  infixr 9 .
  (.) :: forall a b c. Ok3 k a b c => Arr k b c -> Arr k a b -> Arr k a c


infixl 1 <~
-- | Add post- and pre-processing
(<~) :: forall u (k :: B u) a b a' b'. (Category k, Ok4 k a b a' b')
     => Arr k b b' -> Arr k a' a -> (Arr k a b -> Arr k a' b')
(h <~ f) g = (.) @u @k @a' @b @b' h ((.) @u @k @a' @a @b g f)
-- (h <~ f) g = h . g . f

-- h :: Arr k b b'
-- f :: Arr k a' a
-- g :: Arr k a b

-- g . f :: Arr k a' b

-- h . (g . f) :: Arr k a' b'

infixr 1 ~>
-- | Add pre- and post-processing
(~>) :: forall u (k :: B u) a b a' b'. (Category k, Ok4 k a b a' b')
     => Arr k a' a -> Arr k b b' -> (Arr k a b -> Arr k a' b')
f ~> h = (<~) @u @k @a @b @a' @b' h f


class OkProd (k :: B u) where okProd :: Ok2 k a b :- Ok k (a :* b)

class (Category k, OkProd k) => Cartesian (k :: B u) where
  exl :: forall a b. Ok2 k a b => Arr k (a :* b) a
  exr :: forall a b. Ok2 k a b => Arr k (a :* b) b
  infixr 3 &&&
  (&&&) :: forall a c d. Ok3 k a c d
        => Arr k a c -> Arr k a d -> Arr k a (c :* d)

infixr 3 ***
(***) :: forall u (k :: B u) a b c d. (Cartesian k, Ok4 k a b c d)
      => Arr k a c -> Arr k b d -> Arr k (a :* b) (c :* d)
f *** g = (&&&) @u @k @(a :* b) @c @d
            (((.) @u @k @(a :* b) @a @c) f (exl @u @k @a @b))
            (((.) @u @k @(a :* b) @b @d) g (exr @u @k @a @b))
  \\ okProd @u @k @a @b

#if 1

-- infixr 3 ***
-- (***) :: forall u k a b c d. Ok4 k a b c d
--       => Arr k a c -> Arr k b d -> Arr k (a :* b) (c :* d)
-- f *** g = -- f . exl &&& g . exr -- Type errors to sort out
--   (&&&) @u @k f . exl &&& 

-- f :: Arr k a c
-- g :: Arr k b d

-- exl :: Arr k (a :* b) a

-- f . exl

bar0 :: forall u (k :: B u) a b. (Cartesian k, Ok2 k a b)
     => Arr k (a :* b) a
bar0 = exl @u @k @a @b

bar1 :: forall u (k :: B u) a b c. (Cartesian k, (Ok k a, Ok k b, Ok k c, Ok k (a :* b)))
     => Arr k a c -> Arr k (a :* b) c
bar1 f = ((.) @u @k @(a :* b) @a @c) f (exl @u @k @a @b)

bar1' :: forall u (k :: B u) a b c. (Cartesian k, (Ok k a, Ok k b, Ok k c, Ok k (a :* b)))
      => Arr k a c -> Arr k (a :* b) c
bar1' f = bar1 @u @k @a @b @c f

bar2 :: forall u (k :: B u) a b d. (Cartesian k, (Ok k a, Ok k b, Ok k d, Ok k (a :* b)))
     => Arr k b d -> Arr k (a :* b) d
bar2 g = ((.) @u @k @(a :* b) @b @d) g (exr @u @k @a @b)

bar3 :: forall u (k :: B u) a b c d. (Cartesian k, (Ok k a, Ok k b, Ok k c, Ok k d, Ok k (a :* b)))
     => Arr k a c -> Arr k b d -> Arr k (a :* b) (c :* d)
bar3 = undefined (bar1 @u @k @a @b @c) (bar2 @u @k @a @b @d)

bar4 :: forall u (k :: B u) a b c d.
        (Cartesian k, (Ok k a, Ok k b, Ok k c, Ok k d, Ok k (a :* b)))
     => Arr k a c -> Arr k b d -> Arr k (a :* b) (c :* d)

-- bar4 f g = (&&&) @u @k @(a :* b) @c @d (undefined f :: Arr k (a :* b) c) (undefined g :: Arr k (a :* b) d) -- ok

-- bar4 f g = (&&&) @u @k @(a :* b) @c @d (bar1 @u @k @a @b @c f :: Arr k (a :* b) c) (bar2 @u @k @a @b @d g :: Arr k (a :* b) d)

bar4 f g = (&&&) @u @k @(a :* b) @c @d (((.) @u @k @(a :* b) @a @c) f (exl @u @k @a @b)) (((.) @u @k @(a :* b) @b @d) g (exr @u @k @a @b))

-- bar4 f g = baz' @u @k @a @b @c @d (bar1 f :: Arr k (a :* b) c) (bar2 g :: Arr k (a :* b) d)

-- baz :: forall u (k :: B u) a c d. (Cartesian k, Ok3 k a c d)
--     => Arr k a c -> Arr k a d -> Arr k a (c :* d)
-- baz = (&&&) @u @k @a @c @d

baz' :: forall u (k :: B u) a b c d.
        (Cartesian k, Ok4 k a b c d, Ok k (a :* b))
     => Arr k (a :* b) c -> Arr k (a :* b) d -> Arr k (a :* b) (c :* d)
baz' = (&&&) @u @k @(a :* b) @c @d

-- entailment

#endif

#if 1

-- foo0 :: Arr k a c -> Arr k a c
-- foo0 q = q

-- foo1 :: Arr k (a :* b) a -> Arr k (a :* b) a
-- foo1 q = q

foo2 :: forall k a b c. (Category k, Ok3 k a b c) => Arr k b c -> Arr k a b -> Arr k a c
foo2 = (.) @_ @k @a @b @c

-- The @_ is for the kind argument u. Explicitly,

foo2' :: forall u k a b c. (Category (k :: B u), Ok3 k a b c)
      => Arr k b c -> Arr k a b -> Arr k a c
foo2' = (.) @u @k @a @b @c

foo3 :: forall k a b c. (Category k, Ok3 k (a :* b) a c) => Arr k a c -> Arr k (a :* b) a -> Arr k (a :* b) c
foo3 = (.) @_ @k @(a :* b) @a @c

foo3' :: forall u k a b c. (Category (k :: B u), Ok3 k (a :* b) a c)
       => Arr k a c -> Arr k (a :* b) a -> Arr k (a :* b) c
foo3' = (.) @u @k @(a :* b) @a @c

foo3'' :: forall u k a b c. (Category (k :: B u), Ok3 k (a :* b) a c)
        => Arr k a c -> Arr k (a :* b) a -> Arr k (a :* b) c
foo3'' = (.) @u @k @(a :* b) @a @c

-- Next, add something like OkProd to help entail Ok k (a :* b) from Ok2 k a b.

#endif


-- | Category with coproduct.
class Category k => Cocartesian k where
  inl :: Ok2 k a b => Arr k a (a :+ b)
  inr :: Ok2 k a b => Arr k b (a :+ b)
  infixr 2 |||
  (|||) :: Ok3 k a c d => Arr k c a -> Arr k d a -> Arr k (c :+ d) a


class (Cartesian k, Cocartesian k) => Distributive k where
  distl :: Ok3 k a u v => Arr k (a :* (u :+ v)) (a :* u :+ a :* v)

{--------------------------------------------------------------------
    Category of functions
--------------------------------------------------------------------}

instance Category (->) where
  type F (->) t = t
  id  = P.id
  (.) = (P..)

instance OkProd (->) where okProd = Sub Dict

instance Cartesian (->) where
  exl = fst
  exr = snd
  (&&&) = (A.&&&)

instance Cocartesian (->) where
  inl = Left
  inr = Right
  (|||) = (A.|||)

instance Distributive (->) where
  distl (a,uv) = ((a,) A.+++ (a,)) uv

-- ccc :: (a -> b) -> Arr k a b

{--------------------------------------------------------------------
    Category of constraints with entailment
--------------------------------------------------------------------}

type family AsCon (a :: Type) :: Constraint

type instance AsCon (Dict c) = c
type instance AsCon (a :* b) = (AsCon a, AsCon b)

instance Category (:-) where
  type F (:-) c = AsCon c
  -- id :: forall a. AsCon a :- AsCon a
  id = refl
  (.) = trans

-- We could move AsCon into a type family used to define Ok (:-)

instance OkProd (:-) where okProd = Sub Dict

instance Cartesian (:-) where
  exl = weaken1
  exr = weaken2
  (&&&) = (K.&&&)

{--------------------------------------------------------------------
    Non-standard types via standard types
--------------------------------------------------------------------}

#if 0

class HasStd a where
  type Standard a
  toStd :: a -> Standard a
  unStd :: Standard a -> a
  default toStd :: (HasRep a, HasStd (Rep a), Standard a ~ Standard (Rep a)) => a -> Standard a
  default unStd :: (HasRep a, HasStd (Rep a), Standard a ~ Standard (Rep a)) => Standard a -> a
  toStd = toStd . repr
  unStd = abst . unStd

newtype StdFun a b = StdFun (Standard a -> Standard b)

instance Newtype (StdFun a b) where
  type O (StdFun a b) = Standard a -> Standard b
  pack f = StdFun f
  unpack (StdFun f) = f

instance Category StdFun where
  type Ok StdFun = Yes1
  type F StdFun a = Standard a
  id :: StdFun a a
  id = pack id
  (.) :: StdFun b c -> StdFun a b -> StdFun a c
  (.) = inNew2 (.)

#else

-- Generalize from (->) to arbitrary category

-- The specialized and generalized catgories both work. I don't know what value the
-- more general version (StdArr) adds, since we could start by converting to StdFun.

class (Category k, Ok2 k a r) => RepCat (k :: B u) a r | a -> r where
  reprC :: Arr k a r
  abstC :: Arr k r a

instance (HasRep a, r ~ Rep a) => RepCat (->) a r where
  reprC = repr
  abstC = abst

class Ok2 k a (Standard k a) => HasStd (k :: B u) a where
  type Standard k a
  toStd :: Arr k a (Standard k a)
  unStd :: Arr k (Standard k a) a
  default toStd :: forall r. (RepCat k a r, HasStd k r, Standard k a ~ Standard k r)
                => Arr k a (Standard k a)
  toStd = (.) @u @k @a @r @(Standard k r) (toStd @k @r) (reprC @k @a @r)
  default unStd :: forall r. (RepCat k a r, HasStd k r, Standard k a ~ Standard k r)
                => Arr k (Standard k a) a
  unStd = (.) @u @k @(Standard k r) @r @a (abstC @k @a @r) (unStd @k @r)

newtype StdArr (k :: B u) a b = StdArr (Arr k (Standard k a) (Standard k b))

instance Newtype (StdArr k a b) where
  type O (StdArr k a b) = Arr k (Standard k a) (Standard k b)
  pack f = StdArr f
  unpack (StdArr f) = f

class    Ok k (Standard k a) => OkStd k a
instance Ok k (Standard k a) => OkStd k a

instance Category (k :: B u) => Category (StdArr (k :: B u)) where
  type Ok (StdArr k) = OkStd k
  type F (StdArr k) a = a
  id :: forall a. Ok (StdArr k) a => Arr (StdArr k) a a
  id = pack (id @u @k @(Standard k a))
  (.) :: forall a b c. Ok3 (StdArr k) a b c
      => Arr (StdArr k) b c -> Arr (StdArr k) a b -> Arr (StdArr k) a c
  (.) = inNew2 ((.) @u @k @(Standard k a) @(Standard k b) @(Standard k c))

#endif

-- TODO: Cartesian, Cocartesian, Closed

{--------------------------------------------------------------------
    Linear maps
--------------------------------------------------------------------}

type RepHasV s a = (HasRep a, HasV s (Rep a), V s a ~ V s (Rep a))

class HasV s a where
  type V s a :: Type -> Type
  toV :: a -> V s a s
  unV :: V s a s -> a
  -- Default via Rep.
  type V s a = V s (Rep a)
  default toV :: RepHasV s a => a -> V s a s
  default unV :: RepHasV s a => V s a s -> a
  toV = toV . repr
  unV = abst . unV

inV :: (HasV s a, HasV s b) => (a -> b) -> (V s a s -> V s b s)
inV = toV <~ unV

onV :: (HasV s a, HasV s b) => (V s a s -> V s b s) -> (a -> b)
onV = unV <~ toV

onV2 :: (HasV s a, HasV s b, HasV s c) => (V s a s -> V s b s -> V s c s) -> (a -> b -> c)
onV2 = onV <~ toV

newtype LMap (s :: Type) (f :: Type -> Type) (g :: Type -> Type) = LMap (g (f s))

instance Newtype (LMap s f g) where
  type O (LMap s f g) = g (f s)
  pack gf = LMap gf
  unpack (LMap gf) = gf

type OkLs (s :: Type) = Num s  -- for now
class OkLF (f :: Type -> Type)
type OkLM' s a = (OkLs s, OkLF (V s a))

class    (OkLM' s a) => OkLM s a
instance (OkLM' s a) => OkLM s a

-- class OkLF (V s a) => OkLM (s :: Type) (a :: Type)

idLM :: forall s f. OkLF f => LMap s f f
idLM = undefined

compLM :: OkLF f => LMap s g h -> LMap s f g -> LMap s f h
compLM = undefined

instance Category (LMap s) where
  type Ok (LMap s) = OkLM s
  type F (LMap s) a = V s a
  id = idLM
  (.) = compLM
