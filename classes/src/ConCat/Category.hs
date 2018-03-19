{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
-- {-# LANGUAGE TypeInType #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP
{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-} -- for Oks

-- For ConCat.Inline.ClassOp
{-# OPTIONS_GHC -fplugin=ConCat.Inline.Plugin #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}

-- | Another go at constrained categories. This time without Prod, Coprod, Exp.

-- #define DefaultCat

module ConCat.Category where

import Prelude hiding (id,(.),curry,uncurry,const,zip,unzip,zipWith)
import qualified Prelude as P
#ifdef DefaultCat
import qualified Control.Category as C
#endif
import Control.Arrow (Kleisli(..),arr)
import qualified Control.Arrow as A
-- import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import Data.Typeable (Typeable)
import GHC.Exts (Coercible,coerce)
import qualified GHC.Exts as X
import Data.Type.Equality ((:~:)(..))
import qualified Data.Type.Equality as Eq
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Coercion as Co
import GHC.Types (Constraint)
-- import qualified Data.Constraint as Con
import Data.Constraint hiding ((&&&),(***),(:=>))
-- import Debug.Trace
import Data.Monoid
import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:.:)(..))
import GHC.TypeLits (KnownNat)

-- import GHC.Types (type (*))  -- experiment with TypeInType
-- import qualified Data.Constraint as K
-- import GHC.TypeLits
-- import Data.Array (Array,(!),bounds,Ix)
-- import qualified Data.Array as Arr
-- import GHC.Generics ((:*:)(..),(:.:)(..))
-- import qualified Data.Vector.Sized as VS

import Data.Pointed (Pointed(..))
import Data.Key (Zip(..))
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(..))
-- import qualified Data.Functor.Rep as DFR
import Control.Newtype (Newtype(..))
import Data.Vector.Sized (Vector)
#ifdef VectorSized
-- import Data.Finite (Finite)
-- import Data.Vector.Sized (Vector)
-- import qualified Data.Vector.Sized as VS
#endif

-- import Data.MemoTrie

import ConCat.Misc hiding ((<~),(~>),type (&&))
-- import ConCat.Free.Diagonal (Diagonal(..),diag)
import ConCat.Rep hiding (Rep)
import qualified ConCat.Rep as R
import ConCat.Additive
-- import ConCat.Orphans ()
import qualified ConCat.Inline.ClassOp as IC

#define PINLINER(nm) {-# INLINE nm #-}
-- #define PINLINER(nm)

-- Prevents some subtle non-termination errors. See 2017-12-27 journal notes.
-- #define OPINLINE INLINE [0]

-- Changed to NOINLINE [0]. See 2017-12-29 journal notes.
#define OPINLINE NOINLINE [0]

{--------------------------------------------------------------------
    Unit and pairing for binary type constructors
--------------------------------------------------------------------}

-- Unit for binary type constructors
data U2 a b = U2 deriving (Show)

infixr 7 :**:
-- | Product for binary type constructors
data (p :**: q) a b = p a b :**: q a b

prod :: p a b :* q a b -> (p :**: q) a b
prod (p,q) = (p :**: q)

unProd :: (p :**: q) a b -> p a b :* q a b
unProd (p :**: q) = (p,q)

exl2 :: (p :**: q) a b -> p a b
exl2 = exl . unProd

exr2 :: (p :**: q) a b -> q a b
exr2 = exr . unProd

instance HasRep ((k :**: k') a b) where
  type Rep ((k :**: k') a b) = k a b :* k' a b
  abst (f,g) = f :**: g
  repr (f :**: g) = (f,g)

{--------------------------------------------------------------------
    Monoid wrapper
--------------------------------------------------------------------}

newtype Monoid2 m a b = Monoid2 m

{--------------------------------------------------------------------
    Constraints
--------------------------------------------------------------------}

class HasCon a where
  type Con a :: Constraint
  toDict :: a -> Dict (Con a)
  unDict :: Con a => a

newtype Sat kon a = Sat (Dict (kon a))

instance HasCon (Sat kon a) where
  type Con (Sat kon a) = kon a
  toDict (Sat d) = d
  unDict = Sat Dict

instance HasCon () where
  type Con () = ()
  toDict () = Dict
  unDict = ()

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

instance MonoidalPCat (|-) where
  (***) = inNew2 $ \ f g -> Sub $ Dict \\ f \\ g

instance ProductCat (|-) where
  -- type Prod (|-) = (:*)
  exl = pack (Sub Dict)
  exr = pack (Sub Dict)
  dup = pack (Sub Dict)
  (&&&) = inNew2 $ \ f g -> Sub $ Dict \\ f \\ g

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

yes1 :: c |- Sat Yes1 a
yes1 = Entail (Sub Dict)  -- Move to AltCat

forkCon :: forall con con' a. Sat (con &+& con') a |- Sat con a :* Sat con' a
forkCon = Entail (Sub Dict)

joinCon :: forall con con' a. Sat con a :* Sat con' a |- Sat (con &+& con') a
joinCon = Entail (Sub Dict)

inForkCon :: (Sat con1 a :* Sat con2 a |- Sat con1' b :* Sat con2' b)
          -> (Sat (con1 &+& con2) a |- Sat (con1' &+& con2') b)
inForkCon h = joinCon . h . forkCon

-- We might want forkCon, joinCon, and inForkCon elsewhere as well.
-- Consider renaming.

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

instance OpCon (:*) (Sat Eq) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

instance OpCon (:*) (Sat Ord) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

-- TODO: more OpCon instances for standard type classes

instance OpCon (:*) (Sat Additive) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

instance OpCon (->) (Sat Additive) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

class OkAdd k where okAdd :: Ok' k a |- Sat Additive a

type Ok2 k a b         = C2 (Ok k) a b
type Ok3 k a b c       = C3 (Ok k) a b c
type Ok4 k a b c d     = C4 (Ok k) a b c d
type Ok5 k a b c d e   = C5 (Ok k) a b c d e
type Ok6 k a b c d e f = C6 (Ok k) a b c d e f

type Oks k as = AllC (Ok k) as

-- I like the elegance of Oks, but it leads to complex dictionary expressions.
-- For now, use Okn for the operations introduced by lambda-to-ccc conversion.

{--------------------------------------------------------------------
    Categories
--------------------------------------------------------------------}

class Category k where
  type Ok k :: * -> Constraint
  type Ok k = Yes1
  id  :: Ok k a => a `k` a
  infixr 9 .
  (.) :: forall b c a. Ok3 k a b c => (b `k` c) -> (a `k` b) -> (a `k` c)
#ifdef DefaultCat
  -- Defaults experiment
  default id :: C.Category k => a `k` a
  id = C.id
  default (.) :: C.Category k => b `k` c -> a `k` b -> a `k` c
  (.) = (C..)
#endif

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

instance Monoid m => Category (Monoid2 m) where
  id = Monoid2 mempty
  Monoid2 m . Monoid2 n = Monoid2 (m `mappend` n)

instance (Category k, Category k') => Category (k :**: k') where
  type Ok (k :**: k') = Ok k &+& Ok k'
  id = id :**: id
  (g :**: g') . (f :**: f') = g.f :**: g'.f'
  PINLINER(id)
  PINLINER((.))

{--------------------------------------------------------------------
    Products
--------------------------------------------------------------------}

type Prod k = (:*)

infixr 3 ***, &&&

type OkProd k = OpCon (Prod k) (Ok' k)

okProd :: forall k a b. OkProd k
       => Ok' k a && Ok' k b |- Ok' k (Prod k a b)
okProd = inOp
{-# INLINE okProd #-}

-- | Category with monoidal product.
class (OkProd k, Category k) => MonoidalPCat k where
  (***) :: forall a b c d. Ok4 k a b c d
        => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
  default (***) :: forall a b c d. (ProductCat k, Ok4 k a b c d)
                => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
  f *** g = f . exl &&& g . exr
            <+ okProd @k @a @b
  {-# INLINE (***) #-}

-- | Category with product.
class (OkProd k, MonoidalPCat k) => ProductCat k where
  exl :: Ok2 k a b => Prod k a b `k` a
  exr :: Ok2 k a b => Prod k a b `k` b
  dup :: Ok  k a => a `k` Prod k a a
  dup = id &&& id
  swapP :: forall a b. Ok2 k a b => Prod k a b `k` Prod k b a
  swapP = exr &&& exl
          <+ okProd @k @a @b
  -- (***) :: forall a b c d. Ok4 k a b c d
  --       => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
  -- f *** g = f . exl &&& g . exr
  --           <+ okProd @k @a @b
  -- {-# INLINE (***) #-}
  (&&&) :: forall a c d. Ok3 k a c d
        => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)
#ifndef DefaultCat
  -- We can't give two default definitions for (&&&).
  f &&& g = (f *** g) . dup
    <+ okProd @k @a @a
    <+ okProd @k @c @d
  {-# INLINE (&&&) #-}
#endif
  first :: forall a a' b. Ok3 k a b a'
        => (a `k` a') -> (Prod k a b `k` Prod k a' b)
  first = (*** id)
  {-# INLINE first #-}
  second :: forall a b b'. Ok3 k a b b'
         => (b `k` b') -> (Prod k a b `k` Prod k a b')
  second = (id ***)
  {-# INLINE second #-}
  lassocP :: forall a b c. Ok3 k a b c
          => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c
  lassocP = second exl &&& (exr . exr)
            <+ okProd @k @a @b
            <+ inOpR' @(Prod k) @(Ok' k) @a @b @c
  {-# INLINE lassocP #-}
  rassocP :: forall a b c. Ok3 k a b c
          => Prod k (Prod k a b) c `k` Prod k a (Prod k b c)
  rassocP = (exl . exl) &&& first  exr
            <+ okProd @k    @b @c
            <+ inOpL' @(Prod k) @(Ok' k) @a @b @c
  {-# INLINE rassocP #-}
#ifdef DefaultCat
  -- These defaults are not kicking in for (->). Why not?
  -- default exl :: A.Arrow k => Prod k a b `k` a
  default exl :: (A.Arrow k, Ok k ~ Yes1, Ok2 k a b) => (a :* b) `k` a
  exl = arr exl
  default exr :: A.Arrow k => Prod k a b `k` b
  exr = arr exr
  default (&&&) :: A.Arrow k => a `k` c -> a `k` d -> a `k` (c :* d)
  (&&&) = (A.&&&)
#endif
  {-# MINIMAL exl, exr, ((&&&) | dup) #-}

#if 0

-- -- TEMP
-- fork :: forall k a b c d. (ProductCat k, Ok4 k a b c d)
--      => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
-- f `fork` g = f . exl &&& g . exr
--             -- <+ okProd @k @a @b

lassocP' :: forall k a b c. (ProductCat k, Ok3 k a b c, Ok3 k (Prod k b c) (Prod k a (Prod k b c)) (Prod k a b))
         => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c
lassocP' = second exl &&& (exr . exr)
--            <+ okProd @k @a @b
--            <+ inOpR' @(Prod k) @(Ok' k) @a @b @c
{-# INLINE lassocP' #-}

rassocP' :: forall k a b c. (ProductCat k, Oks k [a,b,c], Oks k [Prod k a b, Prod k b c, Prod k (Prod k a b) c])
        => Prod k (Prod k a b) c `k` Prod k a (Prod k b c)
rassocP' = (exl . exl) &&& first  exr
{-# INLINE lassocP' #-}

inLassocP' :: forall k a b c a' b' c'.
             -- (ProductCat k, Ok6 k a b c a' b' c')
             -- Needs :set -fconstraint-solver-iterations=5 or greater:
             (ProductCat k, Oks k [a,b,c,a',b',c'])
          => Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
          -> Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))

--               <+ (inOpLR @(Prod k) @(Ok' k) @a  @b  @c ***
--                   inOpLR @(Prod k) @(Ok' k) @a' @b' @c')

#endif

instance MonoidalPCat (->) where
  (***) = (A.***)

instance ProductCat (->) where
#ifndef DefaultCat
  -- type Prod (->) = (:*)
  exl     = fst
  exr     = snd
  (&&&)   = (A.&&&)
  first   = A.first
  second  = A.second
  lassocP = \ (a,(b,c)) -> ((a,b),c)
  rassocP = \ ((a,b),c) -> (a,(b,c))
#endif

-- TODO: do we want inline for (&&&), (***), first, and second?

instance MonoidalPCat U2 where
  U2 *** U2 = U2
  PINLINER((***))

instance ProductCat U2 where
  exl = U2
  exr = U2
  U2 &&& U2 = U2
  PINLINER(exl)
  PINLINER(exr)
  PINLINER((&&&))

instance (MonoidalPCat k, MonoidalPCat k') => MonoidalPCat (k :**: k') where
  (f :**: f') *** (g :**: g') = (f *** g) :**: (f' *** g')
  PINLINER((***))

instance (ProductCat k, ProductCat k') => ProductCat (k :**: k') where
  exl = exl :**: exl
  exr = exr :**: exr
  (f :**: f') &&& (g :**: g') = (f &&& g) :**: (f' &&& g')
  dup   = dup   :**: dup
  swapP = swapP :**: swapP
  first (f :**: f') = first f :**: first f'
  second (f :**: f') = second f :**: second f'
  lassocP = lassocP :**: lassocP
  rassocP = rassocP :**: rassocP
  PINLINER(exl)
  PINLINER(exr)
  PINLINER((&&&))
  PINLINER(swapP)
  PINLINER(first)
  PINLINER(second)
  PINLINER(lassocP)
  PINLINER(rassocP)

-- | Apply to both parts of a product
twiceP :: (ProductCat k, Oks k [a,c])
       => (a `k` c) -> Prod k a a `k` (Prod k c c)
twiceP f = f *** f
{-# INLINE twiceP #-}

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
{-# INLINE inLassocP #-}

-- | Operate on right-associated form
inRassocP :: forall a b c a' b' c' k.
--              (ProductCat k, Ok6 k a b c a' b' c')
             (ProductCat k, Oks k [a,b,c,a',b',c'])
          => Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))
          -> Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
inRassocP = lassocP <~ rassocP
              <+ (inOpLR @(Prod k) @(Ok' k) @a  @b  @c ***
                  inOpLR @(Prod k) @(Ok' k) @a' @b' @c')
{-# INLINE inRassocP #-}

-- TODO: move twiceP, inLassocP, inRassocP to AltCat

instance Monad m => MonoidalPCat (Kleisli m) where
  (***) = (A.***)
          -- inNew2 crossK
  PINLINER((***))

instance Monad m => ProductCat (Kleisli m) where
  -- type Prod (Kleisli m) = (:*)
  exl   = arr exl
  exr   = arr exr
  dup   = arr dup
  (&&&) = (A.&&&)
          -- inNew2 forkK
  PINLINER(exl)
  PINLINER(exr)
  PINLINER(dup)
  PINLINER((&&&))

#if 0
-- Underlies '(&&&)' on Kleisli arrows
forkK :: Applicative m => (a -> m c) -> (a -> m d) -> (a -> m (c :* d))
(f `forkK` g) a = liftA2 (,) (f a) (g a)

-- Underlies '(***)' on Kleisli arrows
crossK :: Applicative m => (a -> m c) -> (b -> m d) -> (a :* b -> m (c :* d))
(f `crossK` g) (a,b) = liftA2 (,) (f a) (g b)
#endif

{--------------------------------------------------------------------
    Coproducts
--------------------------------------------------------------------}

type Coprod k = (:+)

type OkCoprod k = OpCon (Coprod k) (Ok' k)

okCoprod :: forall k a b. OkCoprod k
         => Ok' k a && Ok' k b |- Ok' k (Coprod k a b)
okCoprod = inOp
{-# INLINE okCoprod #-}

infixr 2 +++, |||

-- Monoidal category over sums
class (OkCoprod k, Category k) => MonoidalSCat k where
  (+++) :: forall a b c d. Ok4 k a b c d
        => (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b)
  default (+++) :: forall a b c d. (CoproductCat k, Ok4 k a b c d)
                => (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b)
  f +++ g = inl . f ||| inr . g
            <+ okCoprod @k @a @b
  {-# INLINE (+++) #-}

-- | Category with coproduct.
class MonoidalSCat k => CoproductCat k where
  -- type Coprod k :: u -> u -> u
  -- type Coprod k = (:+)
  inl :: Ok2 k a b => a `k` Coprod k a b
  inr :: Ok2 k a b => b `k` Coprod k a b
  jam :: Oks k '[a] => Coprod k a a `k` a
  jam = id ||| id
  {-# INLINE jam #-}
  swapS :: forall a b. Ok2 k a b => Coprod k a b `k` Coprod k b a
  swapS = inr ||| inl
          <+ okCoprod @k @b @a
  {-# INLINE swapS #-}
  (|||) :: forall a c d. Oks k [a,c,d]
        => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a)
#ifndef DefaultCat
  -- We can't give two default definitions for (&&&).
  f ||| g = jam . (f +++ g)
          <+ okCoprod @k @a @a
          <+ okCoprod @k @c @d
  {-# INLINE (|||) #-}
#endif
  left  :: forall a a' b. Oks k [a,b,a']
        => (a `k` a') -> (Coprod k a b `k` Coprod k a' b)
  left  = (+++ id)
  {-# INLINE left #-}
  right :: forall a b b'. Oks k [a,b,b']
        => (b `k` b') -> (Coprod k a b `k` Coprod k a b')
  right = (id +++)
  {-# INLINE right #-}
  lassocS :: forall a b c. Oks k [a,b,c]
          => Coprod k a (Coprod k b c) `k` Coprod k (Coprod k a b) c
  lassocS = inl.inl ||| (inl.inr ||| inr)
            <+ inOpL' @(Coprod k) @(Ok' k) @a @b @c
            <+ okCoprod @k    @b @c
  {-# INLINE lassocS #-}
  rassocS :: forall a b c. Oks k [a,b,c]
          => Coprod k (Coprod k a b) c `k` Coprod k a (Coprod k b c)
  rassocS = (inl ||| inr.inl) ||| inr.inr
            <+ inOpR' @(Coprod k) @(Ok' k) @a @b @c
            <+ okCoprod @k @a @b
  {-# INLINE rassocS #-}
#ifdef DefaultCat
  default inl :: A.ArrowChoice k => a `k` Coprod k a b
  inl = arr inl
  default inr :: A.ArrowChoice k => b `k` Coprod k a b
  inr = arr inr
  default (|||) :: A.ArrowChoice k => (a `k` c) -> (b `k` c) -> (Coprod k a b `k` c)
  (|||) = (A.|||)
#endif
  {-# MINIMAL inl, inr, ((|||) | jam) #-}

-- type CoprodOk' k ok = (CoproductCat k, ok ~ Ok' k)

instance MonoidalSCat (->) where
  (+++) = (A.+++)

instance CoproductCat (->) where
#ifndef DefaultCat
  -- type Coprod (->) = (:+)
  inl   = Left
  inr   = Right
  (|||) = (A.|||)
  left  = A.left
  right = A.right
#endif

-- TODO: do we want inline for (|||), (+++), left, and right?

instance Monad m => MonoidalSCat (Kleisli m) where
  -- (+++) = inNew2 (\ f g -> (fmap Left ||| fmap Right) . (f +++ g))

-- f :: a -> m c
-- g :: b -> m d
-- f +++ g :: a :+ b -> m c :+ m d
-- fmap Left ||| fmap Right :: m c :+ m d -> m (c :+ d)

instance Monad m => CoproductCat (Kleisli m) where
  inl = arr inl
  inr = arr inr
  (|||) = inNew2 (|||)

-- f :: a -> m c
-- g :: b -> m c
-- h :: a :+ b -> m c

--   want :: a -> m (a :+ b)

instance MonoidalSCat U2 where
  U2 +++ U2 = U2

instance CoproductCat U2 where
  inl = U2
  inr = U2
  U2 ||| U2 = U2

instance (MonoidalSCat k, MonoidalSCat k') => MonoidalSCat (k :**: k') where
  (f :**: f') +++ (g :**: g') = (f +++ g) :**: (f' +++ g')
  PINLINER((+++))

instance (CoproductCat k, CoproductCat k') => CoproductCat (k :**: k') where
  inl = inl :**: inl
  inr = inr :**: inr
  (f :**: f') ||| (g :**: g') = (f ||| g) :**: (f' ||| g')
  jam = jam :**: jam
  swapS = swapS :**: swapS
  left (f :**: f') = left f :**: left f'
  right (f :**: f') = right f :**: right f'
  lassocS = lassocS :**: lassocS
  rassocS = rassocS :**: rassocS
  PINLINER(inl)
  PINLINER(inr)
  PINLINER((|||))
  PINLINER(swapS)
  PINLINER(left)
  PINLINER(right)
  PINLINER(lassocS)
  PINLINER(rassocS)

-- | Apply to both parts of a coproduct
twiceS :: (CoproductCat k, Oks k [a,c])
       => (a `k` c) -> Coprod k a a `k` (Coprod k c c)
twiceS f = f +++ f

-- | Operate on left-associated form
inLassocS :: forall k a b c a' b' c'.
             -- (CoproductCat k, Ok6 k a b c a' b' c')
             (CoproductCat k, Oks k [a,b,c,a',b',c'])
          => Coprod k (Coprod k a b) c `k` Coprod k (Coprod k a' b') c'
          -> Coprod k a (Coprod k b c) `k` (Coprod k a' (Coprod k b' c'))
inLassocS = rassocS <~ lassocS
            <+ (inOpLR @(Coprod k) @(Ok' k) @a  @b  @c ***
                inOpLR @(Coprod k) @(Ok' k) @a' @b' @c')
{-# INLINE inLassocS #-}

-- | Operate on right-associated form
inRassocS :: forall a b c a' b' c' k.
             -- (CoproductCat k, Ok6 k a b c a' b' c')
             (CoproductCat k, Oks k [a,b,c,a',b',c'])
          => Coprod k a (Coprod k b c) `k` (Coprod k a' (Coprod k b' c'))
          -> Coprod k (Coprod k a b) c `k` Coprod k (Coprod k a' b') c'
inRassocS = lassocS <~ rassocS
            <+ (inOpLR @(Coprod k) @(Ok' k) @a  @b  @c ***
                inOpLR @(Coprod k) @(Ok' k) @a' @b' @c')
{-# INLINE inRassocS #-}

transposeS :: forall k a b c d. (CoproductCat k, Ok4 k a b c d)
           => Coprod k (Coprod k a b) (Coprod k c d) `k` Coprod k (Coprod k a c) (Coprod k b d)
transposeS = (inl.inl ||| inr.inl) ||| (inl.inr ||| inr.inr)
  <+ okCoprod @k @(Coprod k a c) @(Coprod k b d)
  <+ okCoprod @k @c @d
  <+ okCoprod @k @a @b
  <+ okCoprod @k @b @d
  <+ okCoprod @k @a @c
{-# INLINE transposeS #-}

{--------------------------------------------------------------------
    Abelian categories
--------------------------------------------------------------------}

#if 1

type AbelianCat k =
  (ProductCat k, CoproductPCat k, TerminalCat k, CoterminalCat k, OkAdd k)

zeroC :: (AbelianCat k, Ok2 k a b) => a `k` b
zeroC = ti . it

plusC :: forall k a b. (AbelianCat k, Ok2 k a b) => Binop (a `k` b)
f `plusC` g = jamP . (f *** g) . dup
  <+ okProd @k @b @b
  <+ okProd @k @a @a
  <+ okAdd  @k @b

#else

class AbelianCat k where
  zeroC :: forall a b. (Ok2 k a b, Additive b) => a `k` b
  plusC :: forall a b. (Ok2 k a b, Additive b) => Binop (a `k` b)
  default plusC :: forall a b. (Ok2 k a b, Additive b, ProductCat k, CoproductPCat k)
                => Binop (a `k` b)
  -- Two reasonable defaults
#if 1
  f `plusC` g = (f |||| g) . dup <+ okProd @k @a @a
#else
  f `plusC` g = jamP . (f &&& g) <+ okProd @k @b @b
#endif

-- TODO: probably remove the Additive constraints here, but use OkAdd k in the
-- plusC default.

instance AbelianCat U2 where
  zeroC = U2
  U2 `plusC` U2 = U2

instance (AbelianCat k, AbelianCat k') => AbelianCat (k :**: k') where
  zeroC = zeroC :**: zeroC
  (f :**: f') `plusC` (g :**: g') = (f `plusC` g) :**: (f' `plusC` g')
  PINLINER(zeroC)
  PINLINER(plusC)

-- TODO: relate AbelianCat to ProductCat and CoproductPCat.
-- Also to IxProductCat and IxCoproductPCat.

#endif

{--------------------------------------------------------------------
    A dual to ProductCat. Temporary workaround.
--------------------------------------------------------------------}

-- TODO: eliminate CoproductPCat in favor of when we have associated products,
-- coproducts, etc.

infixr 2 ||||, ++++

type CoprodP k = Prod k

type OkCoprodP k = OkProd k

okCoprodP :: forall k a b. OkCoprodP k
           => Ok' k a && Ok' k b |- Ok' k (CoprodP k a b)
okCoprodP = inOp
{-# INLINE okCoprodP #-}

-- | Category with coproduct as Cartesian product.
class MonoidalPCat k => CoproductPCat k where
  inlP :: Ok2 k a b => a `k` CoprodP k a b
  inrP :: Ok2 k a b => b `k` CoprodP k a b
  jamP :: Ok k a => CoprodP k a a `k` a
  jamP = id |||| id
  {-# INLINE jamP #-}
  swapPS :: forall a b. Ok2 k a b
         => CoprodP k a b `k` CoprodP k b a
  default swapPS :: forall a b. (OkAdd k, Ok2 k a b)
                 => CoprodP k a b `k` CoprodP k b a
  swapPS = inrP |||| inlP
           <+ okCoprodP @k @b @a
           <+ okAdd @k @a <+ okAdd @k @b
  {-# INLINE swapPS #-}
  (||||) :: forall a c d. Ok3 k a c d
         => (c `k` a) -> (d `k` a) -> (CoprodP k c d `k` a)
#ifndef DefaultCat
  -- We canDt give two default definitions for (&&&).
  f |||| g = jamP . (f ++++ g)
           <+ okCoprodP @k @a @a
           <+ okCoprodP @k @c @d
  {-# INLINE (||||) #-}
#endif
  {-# MINIMAL inlP, inrP, ((||||) | jamP) #-}

-- Don't bother with left, right, lassocS, rassocS, and misc helpers.

-- instance CoproductPCat (->) where
--   inlP a = (a,zero)
--   inrP b = (zero,b)
--   (f |||| g) (a,b) = f a ^+^ g b
--   jamP (a,a') = a ^+^ a'
--   swapPS = swapP

instance CoproductPCat U2 where
  inlP = U2
  inrP = U2
  U2 |||| U2 = U2
  swapPS = U2

instance (CoproductPCat k, CoproductPCat k') => CoproductPCat (k :**: k') where
  inlP = inlP :**: inlP
  inrP = inrP :**: inrP
  (f :**: f') |||| (g :**: g') = (f |||| g) :**: (f' |||| g')
  jamP = jamP :**: jamP
  swapPS = swapPS :**: swapPS
  -- leftD (f :**: f') = leftD f :**: leftD f'
  -- rightD (f :**: f') = rightD f :**: rightD f'
  -- lassocSD = lassocSD :**: lassocSD
  -- rassocSD = rassocSD :**: rassocSD
  PINLINER(inlP)
  PINLINER(inrP)
  PINLINER((||||))
  PINLINER(swapPS)
  -- PINLINER(leftD)
  -- PINLINER(rightD)
  -- PINLINER(lassocSD)
  -- PINLINER(rassocSD)

-- Scalar multiplication

class ScalarCat k a where
  scale :: a -> (a `k` a)

instance Num a => ScalarCat (->) a where
  scale = (*)  -- I don't think I want to inline (*)
  PINLINER(scale)

instance ScalarCat U2 a where
  scale = const U2

instance (ScalarCat k a, ScalarCat k' a) => ScalarCat (k :**: k') a where
  scale s = scale s :**: scale s
  PINLINER(scale)

type LinearCat k a = (ProductCat k, CoproductPCat k, ScalarCat k a, Ok k a)

{--------------------------------------------------------------------
    Distributive
--------------------------------------------------------------------}

class (ProductCat k, CoproductCat k) => DistribCat k where
  distl :: forall a u v. Oks k [a,u,v]
        => Prod k a (Coprod k u v) `k` Coprod k (Prod k a u) (Prod k a v)
  distr :: forall u v b. Oks k [u,v,b]
        => Prod k (Coprod k u v) b `k` Coprod k (Prod k u b) (Prod k v b)
  distl = (swapP +++ swapP) . distr . swapP
    <+ okProd   @k @(Coprod k u v) @a
    <+ okCoprod @k @(Prod k u a) @(Prod k v a)
    <+ okProd   @k @u @a
    <+ okProd   @k @v @a
    <+ okCoprod @k @(Prod k a u) @(Prod k a v)
    <+ okProd   @k @a @u
    <+ okProd   @k @a @v
    <+ okProd   @k @a @(Coprod k u v)
    <+ okCoprod @k @u @v
  {-# INLINE distl #-}
  distr = (swapP +++ swapP) . distl . swapP
    <+ okProd   @k @b @(Coprod k u v)
    <+ okCoprod @k @(Prod k b u) @(Prod k b v)
    <+ okProd   @k @b @u
    <+ okProd   @k @b @v
    <+ okCoprod @k @(Prod k u b) @(Prod k v b)
    <+ okProd   @k @u @b
    <+ okProd   @k @v @b
    <+ okProd   @k @(Coprod k u v) @b
    <+ okCoprod @k @u @v
  {-# INLINE distr #-}
  {-# MINIMAL distl | distr #-}

-- instance DistribCat (->) where
--   distl (a,uv) = ((a,) +++ (a,)) uv
--   distr (uv,b) = ((,b) +++ (,b)) uv

instance DistribCat (->) where
  distl (a,Left  u) = Left  (a,u)
  distl (a,Right v) = Right (a,v)
  distr (Left  u,b) = Left  (u,b)
  distr (Right v,b) = Right (v,b)

instance DistribCat U2 where
  distl = U2
  distr = U2

instance (DistribCat k, DistribCat k') => DistribCat (k :**: k') where
  distl = distl :**: distl
  distr = distr :**: distr
  PINLINER(distl)
  PINLINER(distr)

-- | Inverse to 'distl': @(a * u) + (a * v) --> a * (u + v)@
undistl :: forall k a u v. (ProductCat k, CoproductCat k, Oks k [a,u,v])
        => Coprod k (Prod k a u) (Prod k a v) `k` Prod k a (Coprod k u v)
undistl = (exl ||| exl) &&& (exr +++ exr)
  <+ okCoprod @k @(Prod k a u) @(Prod k a v)
  <+ okProd   @k @a @u
  <+ okProd   @k @a @v
  <+ okCoprod @k @u @v
{-# INLINE undistl #-}

-- | Inverse to 'distr': @(u * b) + (v * b) --> (u + v) * b@
undistr :: forall k u v b. (ProductCat k, CoproductCat k, Oks k [u,v,b])
        => Coprod k (Prod k u b) (Prod k v b) `k` Prod k (Coprod k u v) b
undistr = (exl +++ exl) &&& (exr ||| exr)
  <+ okCoprod @k @(Prod k u b) @(Prod k v b)
  <+ okCoprod @k @u @v
  <+ okProd   @k @u @b
  <+ okProd   @k @v @b
{-# INLINE undistr #-}

{--------------------------------------------------------------------
    Exponentials
--------------------------------------------------------------------}

type OkExp k = OpCon (Exp k) (Ok' k)

okExp :: forall k a b. OkExp k
      => Ok' k a && Ok' k b |- Ok' k (Exp k a b)
okExp = inOp
{-# INLINE okExp #-}

-- #define ExpAsCat

#ifdef ExpAsCat
type Exp k = k
#else
type Exp k = (->)
#endif

class (OkExp k, ProductCat k) => ClosedCat k where
  -- type Exp k :: u -> u -> u
  apply   :: forall a b. Ok2 k a b => Prod k (Exp k a b) a `k` b
  apply = uncurry id
          <+ okExp @k @a @b
  {-# INLINE apply #-}
  curry   :: Ok3 k a b c => (Prod k a b `k` c) -> (a `k` Exp k b c)
  uncurry :: forall a b c. Ok3 k a b c
          => (a `k` Exp k b c)  -> (Prod k a b `k` c)
  uncurry g = apply . first g
              <+ okProd @k @(Exp k b c) @b
              <+ okProd @k @a @b
              <+ okExp  @k @b @c
  {-# INLINE uncurry #-}
  {-# MINIMAL curry, (apply | uncurry) #-}

--   apply   :: (Ok2 k a b, p ~ Prod k, e ~ Exp k) => ((a `e` b) `p` a) `k` b

instance ClosedCat (->) where
  -- type Exp (->) = (->)
  apply   = P.uncurry ($)
  curry   = P.curry
  uncurry = P.uncurry

-- TODO: do we want inline for apply, curry, and uncurry?

applyK   ::            Kleisli m (Kleisli m a b :* a) b
curryK   :: Monad m => Kleisli m (a :* b) c -> Kleisli m a (Kleisli m b c)
uncurryK :: Monad m => Kleisli m a (Kleisli m b c) -> Kleisli m (a :* b) c

applyK   = pack (apply . first unpack)
curryK   = inNew $ \ h -> return . pack . curry h
uncurryK = inNew $ \ f -> \ (a,b) -> f a >>= ($ b) . unpack

#if 0
instance Monad m => ClosedCat (Kleisli m) where
  -- type Exp (Kleisli m) = Kleisli m
  apply   = applyK
  curry   = curryK
  uncurry = uncurryK
#endif

instance ClosedCat U2 where
  apply = U2
  curry U2 = U2
  uncurry U2 = U2

#ifdef ExpAsCat
instance (ClosedCat k, ClosedCat k') => ClosedCat (k :**: k') where
  apply = (apply . first exl) :**: undefined
  -- apply = (apply . first exl) :**: (apply . first exr)

  -- apply = (apply . exl) :**: (apply . exr)
  -- apply :: forall a b. (Ok2 k a b, Ok2 k' a b)
  --       => (k :**: k') ((k :**: k') a b :* a) b
  -- apply = undefined -- (apply . exl) :**: _
  curry (f :**: f') = curry f :**: curry f'
  uncurry (g :**: g') = uncurry g :**: uncurry g'
  PINLINER(apply)
  PINLINER(curry)
  PINLINER(uncurry)
#else
instance (ClosedCat k, ClosedCat k') => ClosedCat (k :**: k') where
  apply = apply :**: apply
  -- apply = (apply . exl) :**: (apply . exr)
  -- apply :: forall a b. (Ok2 k a b, Ok2 k' a b)
  --       => (k :**: k') ((k :**: k') a b :* a) b
  -- apply = undefined -- (apply . exl) :**: _
  curry (f :**: f') = curry f :**: curry f'
  uncurry (g :**: g') = uncurry g :**: uncurry g'
  PINLINER(apply)
  PINLINER(curry)
  PINLINER(uncurry)
#endif

-- An alternative to ClosedCat
class OkExp k => FlipCat k where
  flipC  :: Ok3 k a b c => (a `k` (b -> c)) -> (b -> (a `k` c))
  flipC' :: Ok3 k a b c => (b -> (a `k` c)) -> (a `k` (b -> c))

instance FlipCat (->) where
  flipC  = flip
  flipC' = flip

-- TODO: inline?

instance FlipCat U2 where
  flipC  U2 = const U2
  flipC' _ = U2

instance (FlipCat k, FlipCat k') => FlipCat (k :**: k') where
  flipC (f :**: f') b = flipC f b :**: flipC f' b
  flipC' h = flipC' (exl2 . h) :**: flipC' (exr2 . h)

-- Hm. The use of exl2 and exr2 here suggest replication of effort

--                h  :: b -> (k :**: k') a c
--         exl2 . h  :: b -> a `k` c
-- flipC' (exl2 . h) :: b -> a `k` c

type Unit k = ()

type OkUnit k = Ok k (Unit k)

class OkUnit k => TerminalCat k where
  -- type Unit k :: u
  it :: Ok k a => a `k` Unit k
  default it :: (ConstCat k (Unit k), Ok k a) => a `k` Unit k
  it = const ()
  {-# INLINE it #-}

-- TODO: add default it = const () when ConstCat k, and then remove instances
-- that were using this definition explicitly.

instance TerminalCat (->) where
  -- type Unit (->) = ()
  it = const ()

instance Monad m => TerminalCat (Kleisli m) where
  -- type Unit (Kleisli m) = ()
  it = arr it

instance TerminalCat U2 where
  it = U2

instance (TerminalCat k, TerminalCat k') => TerminalCat (k :**: k') where
  it = it :**: it
  PINLINER(it)

lunit :: (ProductCat k, TerminalCat k, Ok k a) => a `k` Prod k (Unit k) a
lunit = it &&& id

runit :: (ProductCat k, TerminalCat k, Ok k a) => a `k` Prod k a (Unit k)
runit = id &&& it

type Counit k = ()  -- for now

class Ok k (Counit k) => CoterminalCat k where
  ti :: Ok k a => Counit k `k` a

instance CoterminalCat U2 where
  ti = U2

instance (CoterminalCat k, CoterminalCat k') => CoterminalCat (k :**: k') where
  ti = ti :**: ti
  PINLINER(ti)

#if 0

class Category k => UnsafeArr k where
  unsafeArr :: Ok2 k a b => (a -> b) -> a `k` b

instance UnsafeArr (->) where
  unsafeArr = A.arr

instance Monad m => UnsafeArr (Kleisli m) where
  unsafeArr = A.arr

#endif

constFun :: forall k p a b. (ClosedCat k, Ok3 k p a b)
         => (a `k` b) -> (p `k` Exp k a b)
constFun f = curry (f . exr) <+ okProd @k @p @a
{-# INLINE constFun #-}

--        f        :: a `k` b
--        f . exl  :: Prod k p a `k` b
-- curry (f . exl) :: p `k` (Exp k a b)

-- Combine with currying:

constFun2 :: forall k p a b c. (ClosedCat k, Oks k [p,a,b,c])
          => (Prod k a b `k` c) -> (p `k` (Exp k a (Exp k b c)))
constFun2 = constFun . curry
            <+ okExp @k @b @c

unitFun :: forall k a b. (ClosedCat k, TerminalCat k, Ok2 k a b)
        => (a `k` b) -> (Unit k `k` (Exp k a b))
unitFun = constFun

unUnitFun :: forall k p a. (ClosedCat k, TerminalCat k, Oks k [p,a]) =>
             (Unit k `k` Exp k p a) -> (p `k` a)
unUnitFun g = uncurry g . (it &&& id)
              <+ okProd @k @(Unit k) @p

{--------------------------------------------------------------------
    Constant arrows
--------------------------------------------------------------------}

-- Drop ConstObj for now

type ConstObj k b = b

#if 0

class (TerminalCat k, Ok k (ConstObj k b)) => ConstCat k b where
--   type ConstObj k b
--   type ConstObj k b = b
  unitArrow  :: b -> (Unit k `k` ConstObj k b)
  const :: Ok k a => b -> (a `k` ConstObj k b)
  const b = unitArrow b . it
  unitArrow = const
  {-# MINIMAL unitArrow | const #-}

#else

-- TODO: If I keep this version, remove TerminalCat parent
class (Category k, Ok k (ConstObj k b)) => ConstCat k b where
--   type ConstObj k b
--   type ConstObj k b = b
  const :: Ok k a => b -> (a `k` ConstObj k b)
  -- default const :: (HasRep (ConstObj k b), ConstCat k (Rep b), RepCat k, Ok k a)
  --               => b -> (a `k` ConstObj k b)
  -- const = repConst
  unitArrow :: OkUnit k => b -> (Unit k `k` ConstObj k b)
  unitArrow = const
  -- default const :: (TerminalCat k, OkUnit k)
  --               => b -> (Unit k `k` ConstObj k b)
  default const :: (TerminalCat k, Ok k a)
                => b -> (a `k` ConstObj k b)
  const b = unitArrow b . it

#endif

#if 0

instance (ProductCat k, ConstCat k b, ConstCat k c, Ok k a)
      => ConstCat k (b :* c) where
  const = pairConst

instance {-# OVERLAPPABLE #-}
  ( Category k, ConstCat k (R.Rep b), RepCat k, HasRep (ConstObj k b)
  , Ok k (ConstObj k b) ) => ConstCat k b where
  const = repConst

#endif

repConst :: (HasRep b, r ~ R.Rep b, RepCat k b (ConstObj k r), ConstCat k r, Ok k a, Ok k (ConstObj k b))
         => b -> (a `k` ConstObj k b)
repConst b = abstC . const (repr b)

--                      b  :: b
--                reprC b  :: r
--         const (reprC b) :: a `k` ConstObj k r
-- abstC . const (reprC b) :: a `k` ConstObj k r

pairConst :: (ProductCat k, ConstCat k b, ConstCat k c, Ok k a)
          => b :* c -> (a `k` (b :* c))
pairConst (b,c) = const b &&& const c

-- | Inject a constant on the left
lconst :: forall k a b. (ProductCat k, ConstCat k a, Ok2 k a b)
       => a -> (b `k` (a :* b))
lconst a = first  (const a) . dup
           <+ okProd @k @b @b
           <+ okProd @k @(ConstObj k a) @b

-- | Inject a constant on the right
rconst :: forall k a b. (ProductCat k, ConstCat k b, Ok2 k a b)
       => b -> (a `k` (a :* b))
rconst b = second (const b) . dup
           <+ okProd @k @a @a
           <+ okProd @k @a @(ConstObj k b)

#if 1
instance ConstCat (->) b where const = P.const
#else

-- Temp cheat. No longer needed, since I fix transCatOp in Plugin to fail
-- gracefully when the target category doesn't inhabit the needed class.

#define LitConst(ty) \
instance ConstCat (->) (ty) where { const = P.const ; {-# INLINE const #-} }

LitConst(())
LitConst(Bool)
LitConst(Int)
LitConst(Float)
LitConst(Double)

#endif

-- instance Monad m => ConstCat (Kleisli m) b where const b = arr (const b)

instance (Monad m, ConstCat (->) b) => ConstCat (Kleisli m) b where const b = arr (const b)

-- For prims, use constFun instead.

instance ConstCat U2 a where
  const _ = U2
  -- unitArrow b = unitArrow b :**: unitArrow b

instance (ConstCat k a, ConstCat k' a) => ConstCat (k :**: k') a where
  const b = const b :**: const b
  -- unitArrow b = unitArrow b :**: unitArrow b
  PINLINER(const)
  -- PINLINER(unitArrow)

-- Note that `ConstCat` is *not* poly-kinded. Since the codomain `b` is an
-- argument to `unitArrow` and `const`, `k :: * -> * -> *`. I'm uneasy
-- about this kind restriction, which would preclude some useful categories,
-- including linear maps and entailment. Revisit this issue later.

class DelayCat k where
  delay :: Ok k a => a -> (a `k` a)

instance DelayCat (->) where
  delay = error "delay: not really defined for functions"
  -- Will I need to use oops instead?

class ProductCat k => LoopCat k where
  loop :: Ok3 k s a b => ((a :* s) `k` (b :* s)) -> (a `k` b)

instance LoopCat (->) where
  loop = error "loop: not really defined for functions"
  -- Will I need to use oops instead?

{--------------------------------------------------------------------
    Class aggregates
--------------------------------------------------------------------}

-- | Bi-cartesion (cartesian & co-cartesian) closed categories. Also lumps in
-- terminal and distributive, though should probably be moved out.
type BiCCC k = (ClosedCat k, CoproductCat k, TerminalCat k, DistribCat k)

-- -- | 'BiCCC' with constant arrows.
-- type BiCCCC k p = (BiCCC k, ConstCat k p {-, RepCat k, LoopCat k, DelayCat k-})


{--------------------------------------------------------------------
    Add constraints to a category
--------------------------------------------------------------------}

-- infixr 3 &+&
-- class    (con a, con' a) => (con &+& con') a
-- instance (con a, con' a) => (con &+& con') a

-- instance (HasCon (f a), HasCon (g a)) => HasCon ((f &+& g) a) where
--   type Con ((f &+& g) a) = (Con (f a),Con (g a))
--   toDict (And1 (toDict -> Dict) (toDict -> Dict)) = Dict
--   unDict = And1 unDict unDict

data Constrained (con :: * -> Constraint) k a b = Constrained (a `k` b)

instance (OpSat op con, OpSat op con') => OpCon op (Sat (con &+& con')) where
  inOp :: forall a b. Sat (con &+& con') a && Sat (con &+& con') b |- Sat (con &+& con') (a `op` b)
  inOp = Entail (Sub $ Dict <+ inSat @op @con @a @b <+ inSat @op @con' @a @b)

-- TODO: define inSat, combining inOp and Sat

instance Category k => Category (Constrained con k) where
  type Ok (Constrained con k) = Ok k &+& con
  id = Constrained id
  Constrained g . Constrained f = Constrained (g . f)

instance (MonoidalPCat k, OpSat (Prod k) con)
      => MonoidalPCat (Constrained con k) where
  Constrained f *** Constrained g = Constrained (f *** g)

instance (ProductCat k, OpSat (Prod k) con) => ProductCat (Constrained con k) where
  -- type Prod (Constrained con k) = Prod k
  exl = Constrained exl
  exr = Constrained exr
  Constrained f &&& Constrained g = Constrained (f &&& g)

instance (MonoidalSCat k, OpSat (Coprod k) con)
      => MonoidalSCat (Constrained con k) where
  Constrained f +++ Constrained g = Constrained (f +++ g)

instance (CoproductCat k, OpSat (Coprod k) con)
      => CoproductCat (Constrained con k) where
  -- type Coprod (Constrained con k) = Coprod k
  inl = Constrained inl
  inr = Constrained inr
  Constrained a ||| Constrained b = Constrained (a ||| b)

instance (ClosedCat k, OpSat (Prod k) con, OpSat (Exp k) con) => ClosedCat (Constrained con k) where
  -- type Exp (Constrained con k) = Exp k
  apply = Constrained apply
  curry   (Constrained f) = Constrained (curry f)
  uncurry (Constrained g) = Constrained (uncurry g)

{--------------------------------------------------------------------
    Other category subclasses, perhaps to move elsewhere
--------------------------------------------------------------------}

-- I don't think I want the general Kleisli instances for the rest.
-- For instance, for circuits, type BoolOf (:>) = Source Bool.

#define KleisliInstances

-- Adapted from Circat.Classes

type BoolOf k = Bool

class (ProductCat k, Ok k (BoolOf k)) => BoolCat k where
  -- type BoolOf k
  notC :: BoolOf k `k` BoolOf k
  andC, orC, xorC :: Prod k (BoolOf k) (BoolOf k) `k` BoolOf k

--     • Potential superclass cycle for ‘BoolCat’
--         one of whose superclass constraints is headed by a type family:
--           ‘Ok k bool’
--       Use UndecidableSuperClasses to accept this
--     • In the class declaration for ‘BoolCat’

instance BoolCat (->) where
  -- type BoolOf (->) = Bool
  notC = not
  andC = P.uncurry (&&)
  orC  = P.uncurry (||)
  xorC = P.uncurry (/=)

-- No inline, since not, (&&), (||) are not class-ops, and (/=) is
-- specialized to Bool here (and hence appears as $fEqBool_$c/=)

#ifdef KleisliInstances
instance Monad m => BoolCat (Kleisli m) where
  -- type BoolOf (Kleisli m) = Bool
  notC = arr notC
  andC = arr andC
  orC  = arr orC
  xorC = arr xorC
#endif

instance BoolCat U2 where
  notC = U2
  andC = U2
  orC  = U2
  xorC = U2

instance (BoolCat k, BoolCat k') => BoolCat (k :**: k') where
  notC = notC :**: notC
  andC = andC :**: andC
  orC  = orC  :**: orC
  xorC = xorC :**: xorC
  PINLINER(notC)
  PINLINER(andC)
  PINLINER(orC)
  PINLINER(xorC)

okTT :: forall k a. OkProd k => Ok' k a |- Ok' k (Prod k a a)
okTT = okProd @k @a @a . dup

class (BoolCat k, Ok k a) => EqCat k a where
  equal, notEqual :: Prod k a a `k` BoolOf k
  notEqual = notC . equal    <+ okTT @k @a
  equal    = notC . notEqual <+ okTT @k @a
  {-# MINIMAL equal | notEqual #-}

instance Eq a => EqCat (->) a where
  equal    = uncurry (IC.inline (==))
  notEqual = uncurry (IC.inline (/=))
  {-# OPINLINE equal #-}
  {-# OPINLINE notEqual #-}

#ifdef KleisliInstances
instance (Monad m, Eq a) => EqCat (Kleisli m) a where
  equal    = arr equal
  notEqual = arr notEqual
#endif

instance EqCat U2 a where
  equal = U2
  notEqual = U2

instance (EqCat k a, EqCat k' a) => EqCat (k :**: k') a where
  equal = equal :**: equal
  notEqual = notEqual :**: notEqual
  PINLINER(equal)
  PINLINER(notEqual)

class (EqCat k a, Ord a) => OrdCat k a where
  lessThan, greaterThan, lessThanOrEqual, greaterThanOrEqual :: Prod k a a `k` BoolOf k
  greaterThan        = lessThan . swapP    <+ okTT @k @a
  lessThan           = greaterThan . swapP <+ okTT @k @a
  lessThanOrEqual    = notC . greaterThan  <+ okTT @k @a
  greaterThanOrEqual = notC . lessThan     <+ okTT @k @a
  {-# MINIMAL lessThan | greaterThan #-}

class MinMaxCat k a where
  minC, maxC :: Ok k a => Prod k a a `k` a
#if 0
  default minC :: (OrdCat k a, IfCat k a, Ok k a) => Prod k a a `k` a
  default maxC :: (OrdCat k a, IfCat k a, Ok k a) => Prod k a a `k` a
  minC = ifC . (lessThanOrEqual &&& id)
           <+ okProd @k @Bool @(a :* a)
           <+ okProd @k @a @a
  maxC = ifC . (greaterThan     &&& id)
           <+ okProd @k @Bool @(a :* a)
           <+ okProd @k @a @a
#endif

-- TODO: maybe replace minC and maxC with sortP :: (a :* b) `k` (a :* b). Or add
-- a sortP method and defaults for all three. Would be groovy for parallel
-- sorting.

instance Ord a => MinMaxCat (->) a where
  minC = uncurry (IC.inline min)
  maxC = uncurry (IC.inline max)
  {-# OPINLINE minC #-}
  {-# OPINLINE maxC #-}

instance Ord a => OrdCat (->) a where
  lessThan           = uncurry (IC.inline (<))
  greaterThan        = uncurry (IC.inline (>))
  lessThanOrEqual    = uncurry (IC.inline (<=))
  greaterThanOrEqual = uncurry (IC.inline (>=))
  {-# OPINLINE lessThan #-}
  {-# OPINLINE greaterThan #-}
  {-# OPINLINE lessThanOrEqual #-}
  {-# OPINLINE greaterThanOrEqual #-}

#ifdef KleisliInstances
instance (Monad m, Ord a) => OrdCat (Kleisli m) a where
  lessThan           = arr lessThan
  greaterThan        = arr greaterThan
  lessThanOrEqual    = arr lessThanOrEqual
  greaterThanOrEqual = arr greaterThanOrEqual
#endif

instance Ord a => OrdCat U2 a where
  lessThan           = U2
  greaterThan        = U2
  lessThanOrEqual    = U2
  greaterThanOrEqual = U2

instance MinMaxCat U2 a where
  minC = U2
  maxC = U2

instance (OrdCat k a, OrdCat k' a) => OrdCat (k :**: k') a where
  lessThan = lessThan :**: lessThan
  greaterThan = greaterThan :**: greaterThan
  lessThanOrEqual = lessThanOrEqual :**: lessThanOrEqual
  greaterThanOrEqual = greaterThanOrEqual :**: greaterThanOrEqual
  PINLINER(lessThan)
  PINLINER(greaterThan)
  PINLINER(lessThanOrEqual)
  PINLINER(greaterThanOrEqual)

instance (MinMaxCat k a, MinMaxCat k' a) => MinMaxCat (k :**: k') a where
  minC = minC :**: minC
  maxC = maxC :**: maxC
  PINLINER(minC)
  PINLINER(maxC)

class (Category k, Ok k a) => EnumCat k a where
  succC, predC :: a `k` a
  default succC :: (ProductCat k, NumCat k a, ConstCat k a, Num a) => a `k` a
  default predC :: (ProductCat k, NumCat k a, ConstCat k a, Num a) => a `k` a
  succC = addC . rconst 1 <+ okProd @k @a @a
  predC = subC . rconst 1 <+ okProd @k @a @a

instance Enum a => EnumCat (->) a where
  succC = IC.inline succ
  predC = IC.inline pred
  {-# OPINLINE succC #-}
  {-# OPINLINE predC #-}

instance EnumCat U2 a where
  succC = U2
  predC = U2

instance (EnumCat k a, EnumCat k' a) => EnumCat (k :**: k') a where
  succC = succC :**: succC
  predC = predC :**: predC
  PINLINER(succC)
  PINLINER(predC)

class Ok k a => NumCat k a where
  negateC :: a `k` a
  addC, subC, mulC :: Prod k a a `k` a
  powIC :: Prod k a Int `k` a
  default subC :: ProductCat k => Prod k a a `k` a
  subC = addC . second negateC <+ okProd @k @a @a
  {-# INLINE subC #-}

instance Num a => NumCat (->) a where
  negateC = IC.inline negate
  -- mysterious bug workaround, but leads to different error. see 2017-12-27 notes.
  -- addC (x,y) = IC.inline (+) x y
  addC    = uncurry (IC.inline (+))
  subC    = uncurry (IC.inline (-))
  mulC    = uncurry (IC.inline (*))
  powIC   = uncurry (^) -- (^) is not a class-op
  {-# OPINLINE negateC #-}
  {-# OPINLINE addC #-}
  {-# OPINLINE subC #-}
  {-# OPINLINE mulC #-}
  {-# OPINLINE powIC #-}

#ifdef KleisliInstances
instance (Monad m, Num a) => NumCat (Kleisli m) a where
  negateC = arr negateC
  addC    = arr addC
  subC    = arr subC
  mulC    = arr mulC
  powIC   = arr powIC
#endif

instance NumCat U2 a where
  negateC = U2
  addC    = U2
  subC    = U2
  mulC    = U2
  powIC   = U2

instance (NumCat k a, NumCat k' a) => NumCat (k :**: k') a where
  negateC = negateC :**: negateC
  addC    = addC    :**: addC
  subC    = subC    :**: subC
  mulC    = mulC    :**: mulC
  powIC   = powIC   :**: powIC
  PINLINER(negateC)
  PINLINER(addC)
  PINLINER(subC)
  PINLINER(mulC)
  PINLINER(powIC)

class Ok k a => IntegralCat k a where
  -- For now
  divC :: Prod k a a `k` a
  modC :: Prod k a a `k` a

divModC :: forall k a. (ProductCat k, IntegralCat k a, Ok k a)
        => Prod k a a `k` Prod k a a
divModC = divC &&& modC  <+ okProd @k @a @a

instance Integral a => IntegralCat (->) a where
  divC = uncurry (IC.inline div)
  modC = uncurry (IC.inline mod)
  {-# OPINLINE divC #-}
  {-# OPINLINE modC #-}

#ifdef KleisliInstances
instance (Monad m, Integral a) => IntegralCat (Kleisli m) a where
  divC = arr divC
  modC = arr modC
#endif

instance IntegralCat U2 a where
  divC = U2
  modC = U2

instance (IntegralCat k a, IntegralCat k' a) => IntegralCat (k :**: k') a where
  divC = divC :**: divC
  modC = modC :**: modC
  PINLINER(divC)
  PINLINER(modC)

class Ok k a => FractionalCat k a where
  recipC :: a `k` a
  divideC :: Prod k a a `k` a
  default recipC :: (ProductCat k, ConstCat k a, Num a) => a `k` a
  recipC = divideC . lconst 1 <+ okProd @k @a @a
  {-# INLINE recipC #-}
  default divideC :: (ProductCat k, NumCat k a) => Prod k a a `k` a
  divideC = mulC . second recipC <+ okProd @k @a @a
  {-# INLINE divideC #-}
  {-# MINIMAL recipC | divideC #-}

instance Fractional a => FractionalCat (->) a where
  recipC  = IC.inline recip
  divideC = uncurry (IC.inline (/))
  {-# OPINLINE recipC #-}
  {-# OPINLINE divideC #-}

#ifdef KleisliInstances
instance (Monad m, Fractional a) => FractionalCat (Kleisli m) a where
  recipC  = arr recipC
  divideC = arr divideC
#endif

instance FractionalCat U2 a where
  recipC  = U2
  divideC = U2

instance (FractionalCat k a, FractionalCat k' a) => FractionalCat (k :**: k') a where
  recipC  = recipC  :**: recipC
  divideC = divideC :**: divideC
  PINLINER(recipC)
  PINLINER(divideC)

class Ok k a => FloatingCat k a where
  expC, logC, cosC, sinC :: a `k` a
  -- powC :: (a :* a) `k` a

-- ln :: Floating a => a -> a
-- ln = logBase (exp 1)

instance Floating a => FloatingCat (->) a where
  expC = IC.inline exp
  logC = IC.inline log
  cosC = IC.inline cos
  sinC = IC.inline sin
  -- powC = IC.inline (**)
  {-# OPINLINE expC #-}
  {-# OPINLINE logC #-}
  {-# OPINLINE cosC #-}
  {-# OPINLINE sinC #-}

#ifdef KleisliInstances
instance (Monad m, Floating a) => FloatingCat (Kleisli m) a where
  expC = arr expC
  logC = arr logC
  cosC = arr cosC
  sinC = arr sinC
  -- powC = arr powC
#endif

instance FloatingCat U2 a where
  expC = U2
  logC = U2
  cosC = U2
  sinC = U2
  -- powC = U2

instance (FloatingCat k a, FloatingCat k' a) => FloatingCat (k :**: k') a where
  expC = expC :**: expC
  logC = logC :**: logC
  cosC = cosC :**: cosC
  sinC = sinC :**: sinC
  PINLINER(expC)
  PINLINER(logC)
  PINLINER(cosC)
  PINLINER(sinC)
  -- powC = powC :**: powC
  -- PINLINER(powC)

class Ok k a => RealFracCat k a b where
  floorC, ceilingC :: a `k` b
  truncateC :: a `k` b

instance (RealFrac a, Integral b) => RealFracCat (->) a b where
  floorC    = IC.inline floor
  ceilingC  = IC.inline ceiling
  truncateC = IC.inline truncate
  {-# OPINLINE floorC #-}
  {-# OPINLINE ceilingC #-}
  {-# OPINLINE truncateC #-}

#ifdef KleisliInstances
instance (Monad m, RealFrac a, Integral b) => RealFracCat (Kleisli m) a b where
  floorC    = arr floorC
  ceilingC  = arr ceilingC
  truncateC = arr truncateC
#endif

instance Integral b => RealFracCat U2 a b where
  floorC    = U2
  ceilingC  = U2
  truncateC = U2

instance (RealFracCat k a b, RealFracCat k' a b) => RealFracCat (k :**: k') a b where
  floorC    = floorC    :**: floorC
  ceilingC  = ceilingC  :**: ceilingC
  truncateC = truncateC :**: truncateC
  PINLINER(floorC)
  PINLINER(ceilingC)
  PINLINER(truncateC)

-- Stand-in for fromIntegral, avoiding the intermediate Integer in the Prelude
-- definition.
class FromIntegralCat k a b where
  fromIntegralC :: a `k` b
  foo_FromIntegralCat :: ()  -- experiment
  foo_FromIntegralCat = ()

instance (Integral a, Num b) => FromIntegralCat (->) a b where
  fromIntegralC = X.inline fromIntegral -- non-class-op
  {-# OPINLINE fromIntegralC #-}

#ifdef KleisliInstances
instance (Monad m, Integral a, Num b) => FromIntegralCat (Kleisli m) a b where
  fromIntegralC = arr fromIntegral
#endif

instance FromIntegralCat U2 a b where
  fromIntegralC = U2

instance (FromIntegralCat k a b, FromIntegralCat k' a b) => FromIntegralCat (k :**: k') a b where
  fromIntegralC = fromIntegralC :**: fromIntegralC
  PINLINER(fromIntegralC)

#if 1

-- Revisit later. I used BottomCat for an encoding of sums via products.

class BottomCat k a b where
  bottomC :: a `k` b

-- instance (BottomCat k a b, BottomCat k a c, ProductCat k, Ok3 k a b c) => BottomCat k a (b :* c) where
--   bottomC = bottomC &&& bottomC

instance (BottomCat k a b, ClosedCat k, Ok4 k z b a (z -> b)) => BottomCat k a (z -> b) where
  bottomC = curry (bottomC . exl) <+ okProd @k @a @ z

instance BottomCat (->) a b where bottomC = error "bottomC for (->) evaluated"

instance BottomCat U2 a b where
  bottomC = U2

instance (BottomCat k a b, BottomCat k' a b) => BottomCat (k :**: k') a b where
  bottomC = bottomC :**: bottomC
  PINLINER(bottomC)

#endif

type IfT k a = Prod k (BoolOf k) (Prod k a a) `k` a

class (BoolCat k, Ok k a) => IfCat k a where
  ifC :: IfT k a

instance IfCat (->) a where
  ifC (i,(t,e)) = if i then t else e

#ifdef KleisliInstances
instance Monad m => IfCat (Kleisli m) a where
  ifC = arr ifC
#endif

instance IfCat U2 a where
  ifC = U2

instance (IfCat k a, IfCat k' a) => IfCat (k :**: k') a where
  ifC = ifC :**: ifC
  PINLINER(ifC)

class UnknownCat k a b where
  unknownC :: a `k` b

instance UnknownCat (->) a b where
  unknownC = error "unknown"

instance UnknownCat U2 a b where
  unknownC = U2

instance (UnknownCat k a b, UnknownCat k' a b) => UnknownCat (k :**: k') a b where
  unknownC = unknownC :**: unknownC
  PINLINER(unknownC)

class RepCat k a r where
  reprC :: a `k` r
  abstC :: r `k` a

-- 2018-02-08 (notes): I removed the "| a -> r" functional dependency.

instance (HasRep a, r ~ R.Rep a) => RepCat (->) a r where
  reprC = repr
  abstC = abst

instance (r ~ R.Rep a) => RepCat U2 a r where
  reprC = U2
  abstC = U2

instance (RepCat k a b, RepCat k' a b) => RepCat (k :**: k') a b where
  reprC = reprC :**: reprC
  abstC = abstC :**: abstC
  PINLINER(reprC)
  PINLINER(abstC)

class TransitiveCon con where
  trans :: (con a b, con b c) :- con a c

instance TransitiveCon Coercible where
  trans = Sub Dict

-- instance TransitiveCon (CoerceCat (->)) where
--   trans = Sub Dict

class (
      -- TransitiveCon (CoerceCat k)
      ) => CoerceCat k a b where
  coerceC :: a `k` b

instance Coercible a b => CoerceCat (->) a b where
  coerceC = coerce

instance CoerceCat U2 a b where
  coerceC = U2

instance (CoerceCat k a b, CoerceCat k' a b) => CoerceCat (k :**: k') a b where
  coerceC = coerceC :**: coerceC
  PINLINER(coerceC)

#if 0

#ifdef VectorSized
-- TODO: drop "Arr" alias if these definitions work out
type Arr = Vector

class (ClosedCat k, {-KnownNat n, -}Ok3 k b (Finite n) (Arr n b))
   => ArrayCat k n b where
  array :: Exp k (Finite n) b `k` Arr n b
  arrAt :: Prod k (Arr n b) (Finite n) `k` b

instance KnownNat n => ArrayCat (->) n b where
  array = arrayFun
  arrAt = arrAtFun
  PINLINER(array)
  PINLINER(arrAt)

arrayFun :: KnownNat n => (Finite n -> b) -> Arr n b
arrayFun = VS.generate_
{-# NOINLINE arrayFun #-}

arrAtFun :: KnownNat n => Arr n b :* Finite n -> b
arrAtFun = uncurry VS.index
{-# NOINLINE arrAtFun #-}

-- TODO: working definitions for arrayFun and arrAtFun

instance {- KnownNat n => -} ArrayCat U2 n b where
  array = U2
  -- array _ = U2
  arrAt = U2

instance (ArrayCat k n b, ArrayCat k' n b) => ArrayCat (k :**: k') n b where
  array = array :**: array
  arrAt = arrAt :**: arrAt
  PINLINER(array)
  PINLINER(arrAt)
  -- at = at :**: at
  -- PINLINER(at)

-- #ifdef KleisliInstances
-- instance (Monad m, Enum n) => ArrayCat (Kleisli m) n b where
--   array = arr array
--   arrAt = arr arrAt
-- #endif

#else
-- Arrays
data Arr i a = MkArr (Array i a) deriving Show

-- I'm using "data" instead of "newtype" here to avoid the coercion.

class (ClosedCat k, Ok3 k a b (Arr a b)) => ArrayCat k a b where
  array :: Exp k a b `k` Arr a b
  arrAt :: Prod k (Arr a b) a `k` b
  -- at    :: Arr a b `k` Exp k a b
  -- {-# MINIMAL array, (arrAt | at) #-}
  -- arrAt = uncurry at
  -- at = curry arrAt

instance {- Enum a => -} ArrayCat (->) a b where
  array = arrayFun
  arrAt = arrAtFun
  PINLINER(array)
  PINLINER(arrAt)

arrayFun :: {- Enum a => -} (a -> b) -> Arr a b
arrayFun = oops "arrayFun not yet defined"
{-# NOINLINE arrayFun #-}

arrAtFun :: {- Enum a => -} Arr a b :* a -> b
arrAtFun = oops "arrAtFun not yet defined"
{-# NOINLINE arrAtFun #-}

-- TODO: working definitions for arrayFun and arrAtFun

instance ArrayCat U2 a b where
  array = U2
  -- array _ = U2
  arrAt = U2

instance (ArrayCat k a b, ArrayCat k' a b) => ArrayCat (k :**: k') a b where
  array = array :**: array
  arrAt = arrAt :**: arrAt
  PINLINER(array)
  PINLINER(arrAt)
  -- at = at :**: at
  -- PINLINER(at)

-- #ifdef KleisliInstances
-- instance (Monad m, Enum a) => ArrayCat (Kleisli m) a b where
--   array = arr array
--   arrAt = arr arrAt
-- #endif

#endif

#endif

{--------------------------------------------------------------------
    Functors
--------------------------------------------------------------------}

-- -- These functors change categories but not objects

-- -- | Functors map objects and arrows.
-- class (Category k, Category k'{-, OkTarget f k k'-})
--    => FunctorC f k k' {-  | f -> k k'-} where
--   -- | @fmapC@ maps arrows.
--   fmapC :: (Ok2 k a b, Oks k' [a,b]) => (a `k` b) -> (a `k'` b)
--   -- Laws:
--   -- fmapC id == id
--   -- fmapC (q . p) == fmapC q . fmapC p

{--------------------------------------------------------------------
    Functor-level operations
--------------------------------------------------------------------}

class OkFunctor k h where
  okFunctor :: Ok' k a |- Ok' k (h a)

instance OkFunctor (->) h where okFunctor = Entail (Sub Dict)

instance (OkFunctor k h, OkFunctor k' h)
      => OkFunctor (k :**: k') h where
  okFunctor = inForkCon (okFunctor @k *** okFunctor @k')

class (Functor h, OkFunctor k h) => FunctorCat k h where
  fmapC :: Ok2 k a b => (a `k` b) -> (h a `k` h b)
  unzipC :: forall a b. Ok2 k a b => h (a :* b) `k` (h a :* h b)
#if 0
  default unzipC :: forall a b.
          (FunctorCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
       => h (a :* b) `k` (h a :* h b)
  unzipC = fmapC exl &&& fmapC exr
             <+ okFunctor @k @h @(a :* b)
             <+ okFunctor @k @h @a
             <+ okFunctor @k @h @b
             <+ okProd    @k @a @b
#endif

-- TODO: Maybe rename FunctorCat to avoid confusion.

class (Zip h, OkFunctor k h) => ZipCat k h where
  zipC :: Ok2 k a b => (h a :* h b) `k` h (a :* b)
  -- zipWithC :: Ok3 k a b c => (a :* b -> c) `k` (h a :* h b -> h c)

class OkFunctor k h => ZapCat k h where
  zapC :: Ok2 k a b => h (a `k` b) -> (h a `k` h b)

class ({- Pointed h, -} OkFunctor k h, Ok k a) => PointedCat k h a where
  pointC :: a `k` h a

-- TODO: remove superclasses like Pointed from other classes, and then review
-- instances for unnecessary parent constraints. I've removed them the
-- PointedCat instances in Syntactic and Circuit.

-- TODO: eliminate pointC in favor of using tabulate

-- TODO: Try removing Representable h and maybe OkFunctor k h from the
-- superclasses.

-- TODO: Try removing OkFunctor superclass constraint.
-- When I first triec, I ran into trouble with a rule in AltCat.

-- class DiagCat k h where
--   diagC  :: Ok k a => (a :* a) `k` h (h a)

-- TODO: do I want SumCat, AddCat, or both?

-- class (Ok k a, Num a) => SumCat k h a where
--   sumC :: h a `k` a

class (Ok k a, Additive a) => AddCat k h a where
  sumAC :: h a `k` a

-- class IxSummable n => IxSummableCat k n where
--   ixSumC ::  (Ok k a, Additive a) => (a :^ n) `k` a

-- TODO: Keep only one of AddCat and IxSummableCat, depending on whether I go
-- with functions or functors for indexed products and coproducts.
-- Nope. Use jamPF instead of ixSumC.

instance Functor h => FunctorCat (->) h where
  fmapC  = IC.inline fmap
  unzipC = X.inline unzip
  {-# OPINLINE fmapC #-}
  {-# OPINLINE unzipC #-}

#if 0
instance (Zip h, Representable h) => ZipCat (->) h where
  zipC (as,bs) = tabulate (index as &&& index bs)
instance (Pointed h, Representable h) => PointedCat (->) h where
  pointC a = tabulate (const a)

-- Overlapping instances for ConCat.Misc.Yes1 (Rep h)
--   arising from a use of ‘&&&’
-- Matching instances:
--   instance [safe] forall k (a :: k). ConCat.Misc.Yes1 a
--     -- Defined at /Users/conal/Haskell/concat/classes/src/ConCat/Misc.hs:123:10
-- There exists a (perhaps superclass) match:
--   from the context: Representable h
--     bound by the instance declaration
--   or from: Ok2 (->) a b
--     bound by the type signature for:
--                zipC :: Ok2 (->) a b => h a :* h b -> h (a :* b)

-- TODO: inline for tabulate and index?

#else

instance Zip h => ZipCat (->) h where
  zipC = uncurry (IC.inline zip)
  -- zipWithC :: (a :* b -> c) -> (h a :* h b -> h c)
  -- zipWithC f = uncurry (inline zipWith (curry f))
  {-# OPINLINE zipC #-}

instance Zip h => ZapCat (->) h where
  -- zapC = IC.inline zap
  -- zapC = zap
  zapC = zipWith id  -- as in the default; 2017-12-27 notes
  {-# OPINLINE zapC #-}

instance Pointed h => PointedCat (->) h a where
  pointC = IC.inline point
  {-# OPINLINE pointC #-}

#endif

-- instance (Foldable h, Num a) => SumCat (->) h a where
--   sumC = IC.inline sum
--   {-# OPINLINE sumC #-}

instance (Summable h, Additive a) => AddCat (->) h a where
  sumAC = sumA  -- not a method, so no IC.inline
  {-# OPINLINE sumAC #-}

-- instance (OkFunctor k h, OkFunctor k' h) => OkFunctor (k :**: k') h where
--   okFunctor = inForkCon (okFunctor @k *** okFunctor @k')

instance (FunctorCat k h, FunctorCat k' h) => FunctorCat (k :**: k') h where
  fmapC (f :**: g) = fmapC f :**: fmapC g
  unzipC = unzipC :**: unzipC
  {-# INLINE fmapC #-}
  {-# INLINE unzipC #-}

instance (ZipCat k h, ZipCat k' h) => ZipCat (k :**: k') h where
  zipC = zipC :**: zipC
  {-# INLINE zipC #-}
  -- zipWithC = zipWithC :**: zipWithC
  -- {-# INLINE zipWithC #-}

instance (ZapCat k h, ZapCat k' h, Functor h) => ZapCat (k :**: k') h where
  zapC = uncurry (:**:) . (zapC *** zapC) . unzip . fmap unProd
  {-# INLINE zapC #-}

--             unProd  :: (p :**: q) a b -> p a b :* q a b
--        fmap unProd  :: h ((p :**: q) a b) -> h (p a b :* q a b)
-- unzip (fmap unProd) :: h (p a b :* q a b) -> h (p a b) :* h (q a b)
-- (zapC *** zapC)     :: h (p a b) :* h (q a b) -> p (h a) (h b) :* q (h a) (h b)
-- uncurry (:**:)      :: p (h a) (h b) :* q (h a) (h b) -> (p :**: q) (h a) (h b)

instance (PointedCat k h a, PointedCat k' h a) => PointedCat (k :**: k') h a where
  pointC = pointC :**: pointC
  {-# INLINE pointC #-}

-- instance (DiagCat k h, DiagCat k' h) => DiagCat (k :**: k') h where
--   diagC  = diagC :**: diagC
--   {-# INLINE diagC #-}

-- instance (SumCat k h a, SumCat k' h a) => SumCat (k :**: k') h a where
--   sumC = sumC :**: sumC
--   {-# INLINE sumC #-}

instance (AddCat k h a, AddCat k' h a) => AddCat (k :**: k') h a where
  sumAC = sumAC :**: sumAC
  {-# INLINE sumAC #-}

-- instance (IxSummableCat k h a, IxSummableCat k' h a) => IxSummableCat (k :**: k') h a where
--   ixSumC = ixSumC :**: ixSumC
--   {-# INLINE ixSumC #-}

class DistributiveCat k g f where
  distributeC :: Ok k a => f (g a) `k` g (f a)

-- TODO: perhaps remove the f parameter:
--
-- class DistributiveCat k g where
--   distributeC :: (OkFunctor k f, Ok k a) => f (g a) `k` g (f a)

instance (Distributive g, Functor f) => DistributiveCat (->) g f where
  distributeC = IC.inline distribute
  {-# OPINLINE distributeC #-}

instance (DistributiveCat k g f, DistributiveCat k' g f)
      => DistributiveCat (k :**: k') g f where
  distributeC = distributeC :**: distributeC
  {-# INLINE distributeC #-}

class RepresentableCat k f where
  tabulateC :: Ok k a => (Rep f -> a) `k` f a
  indexC    :: Ok k a => f a `k` (Rep f -> a)

instance Representable f => RepresentableCat (->) f where
  tabulateC = IC.inline tabulate
  indexC    = IC.inline index
  {-# OPINLINE tabulateC #-}
  {-# OPINLINE indexC #-}

instance (RepresentableCat k h, RepresentableCat k' h)
      => RepresentableCat (k :**: k') h where
  tabulateC = tabulateC :**: tabulateC
  indexC    = indexC    :**: indexC
  {-# INLINE tabulateC #-}
  {-# INLINE indexC #-}

---- Experiment

-- fmap' and liftA2' are class-op-inlining synonyms for fmap and liftA2. Look
-- for a better alternative. See 2017-10-20 notes.

fmap' :: Functor f => (a -> b) -> f a -> f b
fmap' = IC.inline fmap

liftA2' :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2' f as bs = fmap' f as <*> bs

-- dbanas 2018-01-08
zipWith' :: Zip f => (a -> b -> c) -> f a -> f b -> f c
zipWith' = IC.inline zipWith

#if 0

class FunctorCat k h => Strong k h where
  strength :: Ok2 k a b => (a :* h b) `k` h (a :* b)

instance Functor h => Strong (->) h where
  strength (a,bs) = (a,) <$> bs

instance (Strong k h, Strong k' h) => Strong (k :**: k') h where
  strength = strength :**: strength

#endif

{--------------------------------------------------------------------
    Indexed products and coproducts
--------------------------------------------------------------------}

-- I intend to replace all of the functor-level vocabulary with indexed products
-- and coproducts.

class OkIxProd k h where
  okIxProd :: Ok' k a |- Ok' k (h a)
-- TODO: Now same as OkFunctor, so drop one.

class (Category k, OkIxProd k h) => IxMonoidalPCat k h where
  crossF :: forall a b. Ok2 k a b => h (a `k` b) -> (h a `k` h b)

class IxMonoidalPCat k h => IxProductCat k h where
  exF    :: forall a  . Ok  k a   => h (h a `k` a)
  forkF  :: forall a b. Ok2 k a b => h (a `k` b) -> (a `k` h b)
  replF  :: forall a  . Ok  k a   => a `k` h a
  -- Defaults
  forkF fs = crossF fs . replF <+ okIxProd @k @h @a <+ okIxProd @k @h @b
  default replF :: forall a . (Pointed h, Ok k a) => a `k` h a
  replF     = forkF (point id)
  {-# INLINE forkF #-}
  {-# INLINE replF #-}
  {-# MINIMAL exF, (forkF | replF) #-}

  -- default crossF :: forall a b. (Zip h, Ok2 k a b) => h (a `k` b) -> (h a `k` h b)
  -- crossF fs = forkF (zipWith (.) fs exF) <+ okIxProd @k @h @a
  -- {-# INLINE crossF #-}

#if 0
-- Types for forkF

fs                :: h (a `k` b)
crossF fs         :: h a `k` h b
crossF fs . replF :: a `k` h b

-- Types for crossF

                      exF  :: h (h a `k` a)
                   fs      :: h (a `k` b)
       zipWith (.) fs exF  :: h (h a `k` b)
forkF (zipWith (.) fs exF) :: h a `k` h b

-- Types for `replF` via `forkF`:

       const id  :: h (a `k` a)
forkF (const id) :: a `k` h a

-- Laws:

forkF exF == id
(. forkF fs) <$> exF == fs

-- Types:

      exF :: h (h b `k` b)
forkF exF :: h b `k` h b

         fs          :: h (a `k` b)
   forkF fs          :: a `k` h b
(. forkF fs)         :: (h b `k` b) -> (a `k` b)
             <$> exF :: h (h b `k` b)
(. forkF fs) <$> exF :: h (a `k` b)

#endif

instance OkIxProd (->) h where okIxProd = Entail (Sub Dict)

instance Zip h => IxMonoidalPCat (->) h where
  crossF = zipWith id -- 2018-02-07 notes
  {-# OPINLINE crossF #-}

instance (Representable h, Zip h, Pointed h) => IxProductCat (->) h where
  exF    = tabulate (flip index)
  replF  = point
           -- zap
  forkF = \ fs x -> ($ x) <$> fs
  {-# OPINLINE exF    #-}
  {-# OPINLINE replF  #-}
  {-# OPINLINE forkF #-}

--           flip index :: Rep h -> h a -> a
-- tabulate (flip index) :: h (h a -> a)
-- 
-- point :: a -> h a
-- zap   :: h (a -> b) -> h a -> h b

instance OkIxProd U2 h where
  okIxProd = Entail (Sub Dict)

instance IxMonoidalPCat U2 h where
  crossF = const U2

instance Pointed h => IxProductCat U2 h where
  exF    = point U2
  forkF  = const U2
  replF  = U2

instance (OkIxProd k h, OkIxProd k' h) => OkIxProd (k :**: k') h where
  okIxProd :: forall a. Ok' (k :**: k') a |- Ok' (k :**: k') (h a)
  okIxProd = Entail (Sub (Dict <+ okIxProd @k  @h @a
                               <+ okIxProd @k' @h @a))

instance (IxMonoidalPCat k h, IxMonoidalPCat k' h, Zip h) => IxMonoidalPCat (k :**: k') h where
  crossF = prod . (crossF *** crossF) . unzip . fmap unProd

instance (IxProductCat k h, IxProductCat k' h, Zip h) => IxProductCat (k :**: k') h where
  exF    = zipWith (:**:) exF exF
  forkF  = prod . (forkF  *** forkF ) . unzip . fmap unProd
  replF  = replF :**: replF

#if 0
-- forkF:
fmap unProd     :: h ((k :**: k') a b) -> h ((a `k` b) :* (a `k'` b))
unzip           :: ... -> h (a `k` b) :* h (a `k'` b)
forkF *** forkF :: ... -> (a `k` h b) :* (a `k'` h b)
prod            :: ... -> (k :**: k') a (h b)
#endif

#if 0

class OkIxCoprod k n where
  okIxCoprod :: Ok' k a |- Ok' k (n , a)

-- TODO: is there a functor-style equivalent/dual for (n , a), say some kind of
-- co-representable thingy?

-- | Indexed monoidal coproducts
class (Category k, OkIxCoprod k h) => IxMonoidalSCat k n where
  plusF :: forall a b . Ok2 k a b => h (b `k` a) -> ((n , b) `k` (n , a))

  -- -- Defaults
  -- plusF fs = joinF (zipWith (.) inF fs) <+ okIxCoprod @k @n @a
  -- {-# INLINE plusF #-}

-- | Indexed cocartesian
class IxMonoidalSCat k h => IxCoproductCat k n where
  inF   :: forall a   . Ok  k a   => h (a `k` (n , a))
  joinF :: forall a b . Ok2 k a b => h (b `k` a) -> ((n , b) `k` a)
  jamF  :: forall a   . Ok  k a   => (n , a) `k` a
  joinF fs = jamF . plusF fs <+ okIxCoprod @k @n @a <+ okIxCoprod @k @n @b
  jamF     = joinF (const id)  -- or exr if we assumed products.
  {-# INLINE joinF #-}
  {-# INLINE jamF #-}
  {-# MINIMAL inF, (joinF | jamF) #-}

instance OkIxCoprod (->) n where okIxCoprod = Entail (Sub Dict)

instance IxCoproductCat (->) n where
  inF   = (,)
  joinF = uncurry
  jamF  = snd
  {-# OPINLINE inF   #-}
  {-# OPINLINE joinF #-}
  {-# OPINLINE jamF  #-}

#if 0

-- Types for plusF default:

                   inF     :: h (a `k` (n , a))
                       fs  :: h (b `k` a)
       zipWith (.) inF fs  :: h (b `k` (n , a))
joinF (zipWith (.) inF fs) :: (n , b) `k` (n , a)

-- Types for `joinPF` default:

               fs :: h (b `k` a)
        plusPF fs :: (n , b) `k` (n , a)
jamPF . plusPF fs :: (n , b) `k` a

-- Types for `jamF` default:

       const id  :: h (a `k` a)
joinF (const id) :: (n , a) `k` a

-- Laws:

joinF inF == id
(joinF fs .) <$> inF == fs

-- Types:

       inF :: h (b `k` h b)
joinF inF :: h b `k` h b

          fs         :: h (b `k` a)
   joinF fs          :: h b `k` a
(. joinF fs)         :: (b `k` h b) -> (b `k` a)
             <$> inF :: h (b `k` h b)
(. joinF fs) <$> inF :: h (b `k` a)

#endif

instance OkIxCoprod U2 n where
  okIxCoprod = Entail (Sub Dict)

instance IxMonoidalSCat U2 n where
  plusF = const U2

instance IxCoproductCat U2 n where
  inF   = pure U2
  joinF = const U2
  jamF  = U2

instance (OkIxCoprod k n, OkIxCoprod k' n) => OkIxCoprod (k :**: k') n where
  okIxCoprod :: forall a. Ok' (k :**: k') a |- Ok' (k :**: k') (n , a)
  okIxCoprod = Entail (Sub (Dict <+ okIxCoprod @k  @n @a
                                 <+ okIxCoprod @k' @n @a))

instance (IxMonoidalSCat k n, IxMonoidalSCat k' n) => IxMonoidalSCat (k :**: k) n where
  plusF = prod . (plusF *** plusF) . unzip . fmap unProd

instance (IxCoproductCat k n, IxCoproductCat k' n) => IxCoproductCat (k :**: k) n where
  inF   = zipWith (:**:) inF inF
  joinF = prod . (joinF *** joinF) . unzip . fmap unProd
  jamF  = jamF :**: jamF

#endif

-- Functor additivity
class Additive1 h where additive1 :: Sat Additive a |- Sat Additive (h a)

instance Additive1 ((->) a) where additive1 = Entail (Sub Dict)
instance Additive1 Sum      where additive1 = Entail (Sub Dict)
instance Additive1 Product  where additive1 = Entail (Sub Dict)
instance Additive1 U1       where additive1 = Entail (Sub Dict)
instance Additive1 Par1     where additive1 = Entail (Sub Dict)
instance (AddF f, AddF g) => Additive1 (f :*: g)  where additive1 = Entail (Sub Dict)
instance (AddF f, AddF g) => Additive1 (g :.: f)  where additive1 = Entail (Sub Dict)
instance KnownNat n       => Additive1 (Vector n) where additive1 = Entail (Sub Dict)

-- TODO: move Additive1 elsewhere

-- | Indexed coproducts as indexed products.
-- Requires additivity for now. See 2018-01-14 notes.
class (IxMonoidalPCat k h, OkIxProd k h) => IxCoproductPCat k h where
  inPF   :: forall a   . Ok  k a   => h (a `k` h a)
  joinPF :: forall a b . Ok2 k a b => h (b `k` a) -> (h b `k` a)
  -- plusPF :: forall a b . Ok2 k a b => h (b `k` a) -> (h b `k` h a)  -- same as crossPF
  jamPF  :: forall a   . Ok  k a   => h a `k` a
  -- Defaults
  -- default plusPF :: forall a b . (Zip h, Ok2 k a b) => h (b `k` a) -> (h b `k` h a)
  -- plusPF fs = joinPF (zipWith (.) inPF fs)
  --     <+ okIxProd @k @h @a
  default joinPF :: forall a b . (IxMonoidalPCat k h, Ok2 k a b) => h (b `k` a) -> (h b `k` a)
  joinPF fs = jamPF . plusPF fs <+ okIxProd @k @h @a <+ okIxProd @k @h @b
  default jamPF :: forall a . (Pointed h, Ok k a) => h a `k` a
  jamPF     = joinPF (point id)
  {-# INLINE joinPF #-}
  -- {-# INLINE plusPF #-}
  {-# INLINE jamPF #-}
  -- {-# MINIMAL inPF, (joinPF | (plusPF, jamPF)) #-}
  {-# MINIMAL inPF, (joinPF | jamPF) #-}

#if 0

-- Types for `joinPF` default:

               fs :: h (b `k` a)
        plusPF fs :: h b `k` h a
jamPF . plusPF fs :: h b `k` a

-- Types for `plusPF` default:

                    inPF     :: h (a `k` h a)
                         fs  :: h (b `k` a)
        zipWith (.) inPF fs  :: h (b `k` h a)
joinPF (zipWith (.) inPF fs) :: h b `k` h a

-- Types for `jamPF` via `joinPF`:

        const id  :: h (a `k` a)
joinPF (const id) :: h a `k` a

-- Laws:

joinPF inPF == id
(joinPF fs .) <$> inPF == fs

-- Types:

       inPF :: h (b `k` h b)
joinPF inPF :: h b `k` h b

          fs           :: h (b `k` a)
   joinPF fs           :: h b `k` a
(. joinPF fs)          :: (b `k` h b) -> (b `k` a)
              <$> inPF :: h (b `k` h b)
(. joinPF fs) <$> inPF :: h (b `k` a)

#endif

-- instance Summable h => IxCoproductPCat (->) h where
--   inPF      = tabulate (\ i a -> tabulate (\ j -> if i == j then a else zero))
--   plusPF    = crossF
--   jamPF     = sumA
--   {-# OPINLINE inPF #-}
--   {-# OPINLINE plusPF #-}
--   {-# OPINLINE jamPF #-}

  -- joinPF fs = jamPF . plusPF fs  -- default, so remove
  -- {-# OPINLINE joinPF #-}

-- inPF :: h (a -> h a)

-- Rep h -> a -> h a
-- Rep h -> a -> Rep h -> a

-- jamPF :: h a -> a

instance Pointed h => IxCoproductPCat U2 h where
  inPF   = point U2
  joinPF = const U2
  jamPF  = U2
  -- plusPF = const U2

instance (IxCoproductPCat k h, IxCoproductPCat k' h, Zip h)
      => IxCoproductPCat (k :**: k') h where
  inPF   = zipWith (:**:) inPF inPF
  joinPF = prod . (joinPF *** joinPF) . unzip . fmap unProd
  jamPF  = jamPF :**: jamPF
  -- plusPF = prod . (plusPF *** plusPF) . unzip . fmap unProd

{--------------------------------------------------------------------
    Obsolete
--------------------------------------------------------------------}

-- | Alias for '(***)'
(++++) :: (MonoidalPCat k, Ok4 k a b c d) =>
          (c `k` a) -> (d `k` b) -> (CoprodP k c d `k` CoprodP k a b)
(++++) = (***)
{-# INLINE (++++) #-}

-- Alias for 'crossF'
plusPF :: (IxMonoidalPCat k h, Ok2 k a b) => h (b `k` a) -> (h b `k` h a)
plusPF = crossF
{-# INLINE plusPF #-}
