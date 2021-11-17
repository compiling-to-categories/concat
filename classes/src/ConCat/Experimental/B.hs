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

-- TODO: trim pragmas

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Back off from poly-kinded for now, and focus on associated products etc.

module ConCat.Experimental.B where

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
-- import GHC.Types (type (*))  -- experiment with TypeInType
-- import qualified Data.Constraint as K
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

--------------------------------------------------
-- * Unit and pairing for binary type constructors


-- Unit for binary type constructors
data U2 a b = U2 deriving (Show)

--------------------------------------------------
-- * Constraints


class HasCon a where
  type Con a :: Constraint
  toDict :: a -> Dict (Con a)
  unDict :: Con a => a

newtype Sat kon a = Sat (Dict (kon a))

instance HasCon (Sat kon a) where
  type Con (Sat kon a) = kon a
  toDict (Sat d) = d
  unDict = Sat Dict

instance (HasCon a, HasCon b) => HasCon (a :* b) where
  type Con (a :* b) = (Con a,Con b)
  toDict (toDict -> Dict, toDict -> Dict) = Dict
  unDict = (unDict,unDict)

infixr 1 |-
newtype a |- b = Entail (Con a :- Con b)

instance Newtype (a |- b) where
  type O (a |- b) = Con a :- Con b
  pack e = Entail e
  unpack (Entail e) = e

instance Category (|-) where
  -- type Ok (|-) = HasCon
  id = pack refl
  (.) = inNew2 (\ g f -> Sub $ Dict \\ g \\ f)

instance OpCon (:*) (Sat HasCon) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

instance ProductCat (|-) where
  -- type Prod (|-) = (:*)
  exl = pack (Sub Dict)
  exr = pack (Sub Dict)
  dup = pack (Sub Dict)
  (&&&) = inNew2 $ \ f g -> Sub $ Dict \\ f \\ g
  (***) = inNew2 $ \ f g -> Sub $ Dict \\ f \\ g

infixl 1 <+

-- | Wrapper
(<+) :: Con a => (Con b => r) -> (a |- b) -> r
r <+ Entail (Sub Dict) = r
-- f <+ Entail e = f \\ e
{-# INLINE (<+) #-}

infixr 3 &&
-- (&&) = Prod (|-)
type (&&) = (:*)

class OpCon op con where
  inOp :: con a && con b |- con (a `op` b)

-- class    OpCon op (Dict (kon a)) => OpCon' op kon a
-- instance OpCon op (Dict (kon a)) => OpCon' op kon a

-- class    kon a => Sat kon a
-- instance kon a => Sat kon a

type Yes1' = Sat Yes1

type Ok' k = Sat (Ok k)

type OpSat op kon = OpCon op (Sat kon)

inSat :: OpCon op (Sat con) => Sat con a && Sat con b |- Sat con (a `op` b)
inSat = inOp

inOpL :: OpCon op con => (con a && con b) && con c |- con ((a `op` b) `op` c)
inOpL = inOp . first  inOp

inOpR :: OpCon op con => con a && (con b && con c) |- con (a `op` (b `op` c))
inOpR = inOp . second inOp

inOpL' :: OpCon op con
       => (con a && con b) && con c |- con (a `op` b) && con ((a `op` b) `op` c)
inOpL' = inOp . exl &&& inOpL
-- inOpL' = second inOp . rassocP . first (dup . inOp)

-- (con a && con b) && con c
-- con (a `op` b) && con c
-- (con (a `op` b) && con (a `op` b)) && con c
-- con (a `op` b) && (con (a `op` b) && con c)
-- con (a `op` b) && con ((a `op` b) `op` c)

inOpR' :: OpCon op con => con a && (con b && con c) |- con (a `op` (b `op` c)) &&  con (b `op` c)
inOpR' = inOpR &&& inOp . exr
-- inOpR' = first inOp . lassocP . second (dup . inOp)

-- There were mutual recursions between (a) inOpL' & rassocP, and (b) inOpR' & lassocP

inOpLR :: forall op con a b c. OpCon op con =>
  ((con a && con b) && con c) && (con a && (con b && con c))
  |- con ((a `op` b) `op` c) && con (a `op` (b `op` c))
inOpLR = inOpL *** inOpR

instance OpCon op Yes1' where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

instance Typeable op => OpCon op (Sat Typeable) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

-- instance OpCon (:*) (Sat Additive) where
--   inOp = Entail (Sub Dict)
--   {-# INLINE inOp #-}

-- instance OpCon (->) (Sat Additive) where
--   inOp = Entail (Sub Dict)
--   {-# INLINE inOp #-}

#if 1
-- Experiment. Smaller Core?
type C1 (con :: u -> Constraint) a = con a
type C2 (con :: u -> Constraint) a b = (con a, con b)
type C3 (con :: u -> Constraint) a b c = (con a, con b, con c)
type C4 (con :: u -> Constraint) a b c d = (con a, con b, con c, con d)
type C5 (con :: u -> Constraint) a b c d e = (con a, con b, con c, con d, con e)
type C6 (con :: u -> Constraint) a b c d e f = (con a, con b, con c, con d, con e, con f)
#else
type C1 (con :: u -> Constraint) a = con a
type C2 con a b         = (C1 con a, con b)
type C3 con a b c       = (C2 con a b, con c)
type C4 con a b c d     = (C2 con a b, C2 con c d)
type C5 con a b c d e   = (C3 con a b c, C2 con d e)
type C6 con a b c d e f = (C3 con a b c, C3 con d e f)
#endif

type Ok2 k a b         = C2 (Ok k) a b
type Ok3 k a b c       = C3 (Ok k) a b c
type Ok4 k a b c d     = C4 (Ok k) a b c d
type Ok5 k a b c d e   = C5 (Ok k) a b c d e
type Ok6 k a b c d e f = C6 (Ok k) a b c d e f

type Oks k as = AllC (Ok k) as

-- I like the elegance of Oks, but it leads to complex dictionary expressions.
-- For now, use Okn for the operations introduced by lambda-to-ccc conversion.

--------------------------------------------------
-- * Categories


class Category (k :: Type -> Type -> Type) where
  type Ok k :: Type -> Constraint
  type Ok k = Yes1
  id  :: Ok k a => a `k` a
  infixr 9 .
  (.) :: forall b c a. Ok3 k a b c => (b `k` c) -> (a `k` b) -> (a `k` c)

infixl 1 <~
infixr 1 ~>
-- | Add post- and pre-processing
(<~) :: (Category k, Oks k [a,b,a',b'])
     => (b `k` b') -> (a' `k` a) -> ((a `k` b) -> (a' `k` b'))
(h <~ f) g = h . g . f

-- | Add pre- and post-processing
(~>) :: (Category k, Oks k [a,b,a',b'])
     => (a' `k` a) -> (b `k` b') -> ((a `k` b) -> (a' `k` b'))
f ~> h = h <~ f

instance Category (->) where
#ifndef DefaultCat
  id  = P.id
  (.) = (P..)
#endif

instance Monad m => Category (Kleisli m) where
#ifndef DefaultCat
  id  = pack return
  (.) = inNew2 (<=<)
#endif

instance Category (:~:) where
  id  = Refl
  (.) = flip Eq.trans

instance Category Coercion where
  id  = Coercion
  (.) = flip Co.trans

instance Category U2 where
  id = U2
  U2 . U2 = U2

-- instance Monoid m => Category (Monoid2 m) where
--   id = Monoid2 mempty
--   Monoid2 m . Monoid2 n = Monoid2 (m `mappend` n)

-- instance (Category k, Category k') => Category (k :**: k') where
--   type Ok (k :**: k') = Ok k &+& Ok k'
--   id = id :**: id
--   (g :**: g') . (f :**: f') = g.f :**: g'.f'
--   PINLINER(id)
--   PINLINER((.))

--------------------------------------------------
-- * Products


okProd :: forall k a b. OpCon (Prod k) (Ok' k)
       => Ok' k a && Ok' k b |- Ok' k (Prod k a b)
okProd = inOp
{-# INLINE okProd #-}

infixr 3 ***, &&&

type OkProd k = OpCon (Prod k) (Ok' k)

-- | Category with product.
class (OkProd k, Category k) => ProductCat k where
  type Prod k :: Type -> Type -> Type
  type Prod k = (:*)            -- default
  exl :: Ok2 k a b => Prod k a b `k` a
  exr :: Ok2 k a b => Prod k a b `k` b
  dup :: Ok  k a => a `k` Prod k a a
  dup = id &&& id
  swapP :: forall a b. Ok2 k a b => Prod k a b `k` Prod k b a
  swapP = exr &&& exl
          <+ okProd @k @a @b
  (***) :: forall a b c d. Ok4 k a b c d
        => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
  f *** g = f . exl &&& g . exr
            <+ okProd @k @a @b
  (&&&) :: forall a c d. Ok3 k a c d
        => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)
#ifndef DefaultCat
  -- We can't give two default definitions for (&&&).
  f &&& g = (f *** g) . dup
    <+ okProd @k @a @a
    <+ okProd @k @c @d
#endif
  first :: forall a a' b. Ok3 k a b a'
        => (a `k` a') -> (Prod k a b `k` Prod k a' b)
  first = (*** id)
  second :: forall a b b'. Ok3 k a b b'
         => (b `k` b') -> (Prod k a b `k` Prod k a b')
  second = (id ***)
  lassocP :: forall a b c. Ok3 k a b c
          => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c
  lassocP = second exl &&& (exr . exr)
            <+ okProd @k @a @b
            <+ inOpR' @(Prod k) @(Ok' k) @a @b @c
  rassocP :: forall a b c. Ok3 k a b c
          => Prod k (Prod k a b) c `k` Prod k a (Prod k b c)
  rassocP = (exl . exl) &&& first  exr
            <+ okProd @k    @b @c
            <+ inOpL' @(Prod k) @(Ok' k) @a @b @c
#ifdef DefaultCat
  -- These defaults are not kicking in for (->). Why not?
  -- default exl :: A.Arrow k => Prod k a b `k` a
  default exl :: (A.Arrow k, Ok k ~ Yes1, Oks k [a,b]) => (a :* b) `k` a
  exl = arr exl
  default exr :: A.Arrow k => Prod k a b `k` b
  exr = arr exr
  default (&&&) :: A.Arrow k => a `k` c -> a `k` d -> a `k` (c :* d)
  (&&&) = (A.&&&)
#endif
  {-# MINIMAL exl, exr, ((&&&) | ((***), dup)) #-}

instance ProductCat (->) where
#ifndef DefaultCat
  -- type Prod (->) = (:*)
  exl     = fst
  exr     = snd
  (&&&)   = (A.&&&)
  (***)   = (A.***)
  first   = A.first
  second  = A.second
  lassocP = \ (a,(b,c)) -> ((a,b),c)
  rassocP = \ ((a,b),c) -> (a,(b,c))
#endif

instance ProductCat U2 where
  exl = U2
  exr = U2
  U2 &&& U2 = U2

-- | Apply to both parts of a product
twiceP :: (ProductCat k, Oks k [a,c])
       => (a `k` c) -> Prod k a a `k` (Prod k c c)
twiceP f = f *** f

-- | Operate on left-associated form
inLassocP :: forall k a b c a' b' c'.
             -- (ProductCat k, Ok6 k a b c a' b' c')
             -- Needs :set -fconstraint-solver-iterations=5 or greater:
             (ProductCat k, Oks k [a,b,c,a',b',c'])
          => Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
          -> Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))
inLassocP = rassocP <~ lassocP
              <+ (inOpLR @(Prod k) @(Ok' k) @a  @b  @c ***
                  inOpLR @(Prod k) @(Ok' k) @a' @b' @c')

-- | Operate on right-associated form
inRassocP :: forall a b c a' b' c' k.
--              (ProductCat k, Ok6 k a b c a' b' c')
             (ProductCat k, Oks k [a,b,c,a',b',c'])
          => Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))
          -> Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
inRassocP = lassocP <~ rassocP
              <+ (inOpLR @(Prod k) @(Ok' k) @a  @b  @c ***
                  inOpLR @(Prod k) @(Ok' k) @a' @b' @c')

transposeP :: forall k a b c d. (ProductCat k, Oks k [a,b,c,d])
           => Prod k (Prod k a b) (Prod k c d) `k` Prod k (Prod k a c) (Prod k b d)
transposeP = (exl.exl &&& exl.exr) &&& (exr.exl &&& exr.exr)
  <+ okProd @k @(Prod k a b) @(Prod k c d)
  <+ okProd @k @c @d
  <+ okProd @k @a @b
  <+ okProd @k @b @d
  <+ okProd @k @a @c

-- | Inverse to '(&&&)'
unfork :: forall k a c d. (ProductCat k, Ok3 k a c d)
       => (a `k` Prod k c d) -> (a `k` c, a `k` d)
unfork f = (exl . f, exr . f)  <+ okProd @k @c @d

instance Monad m => ProductCat (Kleisli m) where
  -- type Prod (Kleisli m) = (:*)
  exl   = arr exl
  exr   = arr exr
  dup   = arr dup
  (&&&) = (A.&&&)
          -- inNew2 forkK
  (***) = (A.***)
          -- inNew2 crossK

#if 0
-- Underlies '(&&&)' on Kleisli arrows
forkK :: Applicative m => (a -> m c) -> (a -> m d) -> (a -> m (c :* d))
(f `forkK` g) a = liftA2 (,) (f a) (g a)

-- Underlies '(***)' on Kleisli arrows
crossK :: Applicative m => (a -> m c) -> (b -> m d) -> (a :* b -> m (c :* d))
(f `crossK` g) (a,b) = liftA2 (,) (f a) (g b)
#endif

--------------------------------------------------
-- * Exponentials



--------------------------------------------------
-- * Product category


data P a b

type family Fst t where Fst (P a b) = a
type family Snd t where Snd (P a b) = b

-- Product of categories
infixl 1 :**:
data (k :**: k') a b = (Fst a `k` Fst b) :**: (Snd a `k'` Snd b)

instance HasRep ((k :**: k') a b) where
  type Rep ((k :**: k') a b) = (Fst a `k` Fst b) :* (Snd a `k'` Snd b)
  abst (f,g) = f :**: g
  repr (f :**: g) = (f,g)

class    (Ok k (Fst ab), Ok k' (Snd ab)) => OkCProd k k' ab
instance (Ok k (Fst ab), Ok k' (Snd ab)) => OkCProd k k' ab

instance (Category k, Category k') => Category (k :**: k') where
  type Ok (k :**: k') = OkCProd k k'
  id = id :**: id
  (g :**: g') . (f :**: f') = (g . f) :**: (g' . f')

data ProdProd k k' ab cd =
  P (Prod k (Fst ab) (Fst cd)) (Prod k' (Snd ab) (Snd cd))

-- type OkCProd (k :**: k') a = Ok k (Fst a) &+& Ok k' (Snd a)

instance OpCon (ProdProd k k') (Sat (OkCProd k k')) where
  inOp = Entail (Sub Dict)

instance (ProductCat k, ProductCat k') => ProductCat (k :**: k') where
  type Prod (k :**: k') = ProdProd k k'

-- instance (ProductCat k, ProductCat k') => ProductCat (k :**: k') where
--   type Ok (k :**: k') a = Ok k (Fst a) &+& Ok k' (Snd a)

-- instance (ProductCat k, ProductCat k') => ProductCat (k :**: k') where
--   exl = exl :**: exl
--   exr = exr :**: exr
--   (f :**: f') &&& (g :**: g') = (f &&& g) :**: (f' &&& g')
--   (f :**: f') *** (g :**: g') = (f *** g) :**: (f' *** g')
--   dup   = dup   :**: dup
--   swapP = swapP :**: swapP
--   first (f :**: f') = first f :**: first f'
--   second (f :**: f') = second f :**: second f'
--   lassocP = lassocP :**: lassocP
--   rassocP = rassocP :**: rassocP
--   PINLINER(exl)
--   PINLINER(exr)
--   PINLINER((&&&))
--   PINLINER((***))
--   PINLINER(swapP)
--   PINLINER(first)
--   PINLINER(second)
--   PINLINER(lassocP)
--   PINLINER(rassocP)
