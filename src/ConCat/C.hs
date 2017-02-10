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

-- {-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experiment with polykinded category theory functors

module ConCat.C where

import Prelude hiding (id,(.),zipWith,curry,uncurry)
import qualified Prelude as P
import Data.Kind
import GHC.Generics (U1(..),(:*:)(..),(:+:)(..),(:.:)(..))
import Control.Applicative (liftA2,liftA3)
import Control.Monad ((<=<))
import Control.Arrow (arr,Kleisli(..))
import qualified Control.Arrow as A
import Control.Monad.State (State,modify,put,get,execState,StateT,evalStateT)

import Data.Constraint (Dict(..),(:-)(..),refl,trans,(\\))
import Control.Newtype
import Data.Pointed
import Data.Key
import Data.IntMap ()

import ConCat.Misc (Yes1,inNew,inNew2,oops,type (+->)(..))
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow (lapplyL,OkLF,idL,(@.),exlL,exrL,forkL,inlL,inrL,joinL,HasL(..))
import ConCat.Rep
import ConCat.Orphans

{--------------------------------------------------------------------
    Constraints
--------------------------------------------------------------------}

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

infixr 3 &&
class    (a,b) => a && b
instance (a,b) => a && b

--     • Potential superclass cycle for ‘&&’
--         one of whose superclass constraints is headed by a type variable:
--           ‘a’
--       Use UndecidableSuperClasses to accept this

class OpCon op con where
  inOp :: forall a b. con a && con b |- con (a `op` b)

{--------------------------------------------------------------------
    Categories
--------------------------------------------------------------------}

infixr 9 .
class Category k where
  type Ok k :: u -> Constraint
  type Ok k = Yes1
  id  :: Ok k a => a `k` a
  (.) :: forall b c a. Ok3 k a b c => (b `k` c) -> (a `k` b) -> (a `k` c)

infixl 1 <~
infixr 1 ~>
-- | Add post- and pre-processing
(<~) :: (Category k, Ok4 k a b a' b') 
     => (b `k` b') -> (a' `k` a) -> ((a `k` b) -> (a' `k` b'))
(h <~ f) g = h . g . f

-- | Add pre- and post-processing
(~>) :: (Category k, Ok4 k a b a' b') 
     => (a' `k` a) -> (b `k` b') -> ((a `k` b) -> (a' `k` b'))
f ~> h = h <~ f

infixr 3 &&&
-- | Category with product.
class (OkProd k, Category k) => Cartesian k where
  type Prod k :: u -> u -> u
  exl :: Ok2 k a b => Prod k a b `k` a
  exr :: Ok2 k a b => Prod k a b `k` b
  (&&&) :: forall a c d. Ok3 k a c d => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)

type OkProd k = OpCon (Prod k) (Ok k)

okProd :: forall k a b. OpCon (Prod k) (Ok k)
       => Ok k a && Ok k b |- Ok k (Prod k a b)
okProd = inOp
{-# INLINE okProd #-}

infixr 3 ***
(***) :: forall k a b c d. (Cartesian k, Ok4 k a b c d)
      => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
f *** g = f . exl &&& g . exr
          -- <+ inOp @(Prod k) @(Ok k) @a @b
          <+ okProd @k @a @b

dup :: (Cartesian k, Ok k a) => a `k` Prod k a a
dup = id &&& id

swapP :: forall k a b. (Cartesian k, Ok2 k a b) => Prod k a b `k` Prod k b a
swapP = exr &&& exl  <+ okProd @k @a @b

first :: forall k a a' b. (Cartesian k, Ok3 k a b a')
      => (a `k` a') -> (Prod k a b `k` Prod k a' b)
first = (*** id)
second :: forall k a b b'. (Cartesian k, Ok3 k a b b')
       => (b `k` b') -> (Prod k a b `k` Prod k a b')
second = (id ***)

lassocP :: forall k a b c. (Cartesian k, Ok3 k a b c)
        => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c
lassocP = second exl &&& (exr . exr)
          <+ okProd @k @a @(Prod k b c)
          <+ okProd @k @b @c
          <+ okProd @k @a @b

rassocP :: forall k a b c. (Cartesian k, Ok3 k a b c)
        => Prod k (Prod k a b) c `k` Prod k a (Prod k b c)
rassocP = (exl . exl) &&& first  exr
          <+ okProd @k @(Prod k a b) @c
          <+ okProd @k @b @c
          <+ okProd @k @a @b

infixr 2 +++, |||
-- | Category with coproduct.
class (OpCon (Coprod k) (Ok k),Category k) => Cocartesian k where
  type Coprod k :: u -> u -> u
  inl :: Ok2 k a b => a `k` Coprod k a b
  inr :: Ok2 k a b => b `k` Coprod k a b
  (|||) :: forall a c d. Ok3 k a c d
        => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a)

(+++) :: forall k a b c d. (Cocartesian k, Ok4 k a b c d)
      => (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b)
f +++ g = inl . f ||| inr . g
          <+ okCoprod @k @a @b

type OkCoprod k = OpCon (Coprod k) (Ok k)

okCoprod :: forall k a b. OpCon (Coprod k) (Ok k)
         => Ok k a && Ok k b |- Ok k (Coprod k a b)
okCoprod = inOp
{-# INLINE okCoprod #-}

class (Category k, Ok k (Unit k)) => Terminal k where
  type Unit k :: u
  it :: Ok k a => a `k` Unit k

--     • Illegal constraint ‘Ok k (Unit k)’ in a superclass context
--         (Use UndecidableInstances to permit this)

class (OpCon (Exp k) (Ok k), Cartesian k) => CartesianClosed k where
  type Exp k :: u -> u -> u
  apply   :: forall a b. Ok2 k a b => Prod k (Exp k a b) a `k` b
  apply = uncurry id
          <+ okExp @k @a @b
  curry   :: Ok3 k a b c => (Prod k a b `k` c) -> (a `k` Exp k b c)
  uncurry :: forall a b c. Ok3 k a b c
          => (a `k` Exp k b c)  -> (Prod k a b `k` c)
  uncurry g = apply . first g
              <+ okProd @k @(Exp k b c) @b
              <+ okProd @k @a @b
              <+ okExp @k @b @c

type OkExp k = OpCon (Exp k) (Ok k)

okExp :: forall k a b. OpCon (Exp k) (Ok k)
       => Ok k a && Ok k b |- Ok k (Exp k a b)
okExp = inOp
{-# INLINE okExp #-}

-- Misc type-specific classes

class (Cartesian k, Ok k (BoolOf k)) => BoolCat k where
  type BoolOf k
  notC :: BoolOf k `k` BoolOf k
  andC, orC, xorC :: Prod k (BoolOf k) (BoolOf k) `k` BoolOf k

class (BoolCat k, Ok k a) => EqCat k a where
  equal, notEqual :: Prod k a a `k` BoolOf k
  notEqual = notC . equal    <+ okProd @k @a @a
  equal    = notC . notEqual <+ okProd @k @a @a

class Ok k a => NumCat k a where
  negateC :: a `k` a
  addC, subC, mulC :: Prod k a a `k` a
  default subC :: Cartesian k => Prod k a a `k` a
  subC = addC . second negateC <+ okProd @k @a @a
  type IntOf k
  powIC :: Prod k a (IntOf k) `k` a

{--------------------------------------------------------------------
    Functors
--------------------------------------------------------------------}

infixr 9 %, %%

class (Category src, Category trg) => FunctorC f src trg | f -> src trg where
  type f %% (a :: u) :: v
  type OkF f (a :: u) (b :: u) :: Constraint
  (%) :: forall a b. OkF f a b => f -> src a b -> trg (f %% a) (f %% b)

class FunctorC f src trg => CartesianFunctor f src trg where
  preserveProd :: Dict ((f %% Prod src a b) ~ Prod trg (f %% a) (f %% b))
  -- default preserveProd :: (f %% Prod src a b) ~ Prod trg (f %% a) (f %% b)
  --              => Dict ((f %% Prod src a b) ~ Prod trg (f %% a) (f %% b))
  -- preserveProd = Dict

-- This preserveProd default doesn't work in instances. Probably a GHC bug.

class FunctorC f src trg => CocartesianFunctor f src trg where
  preserveCoprod :: Dict ((f %% Coprod src a b) ~ Coprod trg (f %% a) (f %% b))

class FunctorC f src trg => CartesianClosedFunctor f src trg where
  preserveExp :: Dict ((f %% Exp src a b) ~ Exp trg (f %% a) (f %% b))

#if 0
-- Functor composition. I haven't been able to get a declared type to pass.

data (g #. f) = g :#. f

-- compF :: forall u v w (p :: u -> u -> Type) (q :: v -> v -> Type) (r :: w -> w -> Type) f g (a :: u) (b :: u).
--          (FunctorC f p q, FunctorC g q r)
--       => g -> f -> (a `p` b) -> ((g %% f %% a) `r` (g %% f %% b))

(g `compF` f) pab = g % f % pab

-- instance (FunctorC f u v, FunctorC g v w) => FunctorC (g #. f) u w where
--   type (g #. f) %% a = g %% (f %% a)
--   type OkF (g #. f) a b = OkF f a b
--   -- (%) (g :#. f) = (g %) . (f %)
--   (g :#. f) % a = g % (f % a)
#endif

{--------------------------------------------------------------------
    Haskell types and functions ("Hask")
--------------------------------------------------------------------}

instance Category (->) where
  id  = P.id
  (.) = (P..)

instance OpCon op Yes1 where inOp = Sub Dict

instance Cartesian (->) where
  type Prod (->) = (,)
  exl = fst
  exr = snd
  (f &&& g) x = (f x, g x)

instance Cocartesian (->) where
  type Coprod (->) = Either
  inl = Left
  inr = Right
  (|||) = either

instance Terminal (->) where
  type Unit (->) = ()
  it = const ()

instance CartesianClosed (->) where
  type Exp (->) = (->)
  apply (f,x) = f x
  curry = P.curry
  uncurry = P.uncurry

instance BoolCat (->) where
  type BoolOf (->) = Bool
  notC = not
  andC = uncurry (&&)
  orC  = uncurry (||)
  xorC = uncurry (/=)

#if 1
data HFunctor (t :: * -> *) = HFunctor

instance Functor t => FunctorC (HFunctor t) (->) (->) where
  type HFunctor t %% a = t a
  type OkF (HFunctor t) a b = ()
  (%) HFunctor = fmap
#else
-- Alternatively, put the `FunctorC` constraint into `HFunctor`:
data HFunctor (t :: * -> *) = Functor t => HFunctor

instance FunctorC (HFunctor t) (->) (->) where
  type HFunctor t %% a = t a
  type OkF (HFunctor t) a b = ()
  (%) HFunctor = fmap
#endif

{--------------------------------------------------------------------
    Kleisli
--------------------------------------------------------------------}

instance Monad m => Category (Kleisli m) where
  id = pack return
  (.) = inNew2 (<=<)

instance Monad m => Cartesian (Kleisli m) where
  type Prod (Kleisli m) = (,)
  exl = arr exl
  exr = arr exr
  -- Kleisli f &&& Kleisli g = Kleisli ((liftA2.liftA2) (,) f g)
  -- (&&&) = (inNew2.liftA2.liftA2) (,)
  -- Kleisli f &&& Kleisli g = Kleisli (uncurry (liftA2 (,)) . (f &&& g))
  (&&&) = (A.&&&)

-- f :: a -> m b
-- g :: a -> m c
-- f &&& g :: a -> m b :* m c
-- uncurry (liftA2 (,)) . (f &&& g) :: a -> m (b :* c)

instance Monad m => Cocartesian (Kleisli m) where
  type Coprod (Kleisli m) = Either
  inl = arr inl
  inr = arr inr
  (|||) = (A.|||)

instance Monad m => Terminal (Kleisli m) where
  type Unit (Kleisli m) = ()
  it = arr it

instance Monad m => CartesianClosed (Kleisli m) where
  type Exp (Kleisli m) = Kleisli m
  apply   = pack (apply . first unpack)
  curry   = inNew (\ f -> return . pack . curry f)
  uncurry = inNew (\ g -> \ (a,b) -> g a >>= ($ b) . unpack)

-- We could handle Kleisli categories as follows, but we'll want specialized
-- versions for specific monads m.

-- instance Monad m => BoolCat (Kleisli m) where
--   type BoolOf (Kleisli m) = Bool
--   notC = arr notC
--   andC = arr andC
--   orC  = arr orC
--   xorC = arr xorC

{--------------------------------------------------------------------
    Constraint entailment
--------------------------------------------------------------------}

infixr 1 |-
type (|-) = (:-)

infixl 1 <+
(<+) :: (b => r) -> (a |- b) -> (a => r)
r <+ Sub Dict = r
{-# INLINE (<+) #-}
-- (<+) = (\\)

instance Category (|-) where
  id  = Sub Dict
  g . f = Sub (Dict <+ g <+ f)

-- instance Category (|-) where
--   id  = refl
--   (.) = trans

instance Cartesian (|-) where
  type Prod (|-) = (&&)
  exl = Sub Dict
  exr = Sub Dict
  f &&& g = Sub (Dict <+ f <+ g)

instance Terminal (|-) where
  type Unit (|-) = ()
  it = Sub Dict

-- Tweaked from Data.Constraint
mapDict :: (a |- b) -> Dict a -> Dict b
mapDict (Sub q) Dict = q

unmapDict :: (Dict a -> Dict b) -> (a |- b)
unmapDict f = Sub (f Dict)

data MapDict = MapDict

instance FunctorC MapDict (|-) (->) where
  type MapDict %% a = Dict a
  type OkF MapDict a b = ()
  (%) MapDict = mapDict

-- -- Couldn't match type ‘Dict (a && b)’ with ‘(Dict a, Dict b)’
-- instance CartesianFunctor MapDict (|-) (->) where preserveProd = Dict

class HasCon a where
  type Con a :: Constraint
  toDict :: a -> Dict (Con a)
  unDict :: Dict (Con a) -> a

instance HasCon (Dict con) where
  type Con (Dict con) = con
  toDict = id
  unDict = id

instance (HasCon a, HasCon b) => HasCon (a,b) where
  type Con (a,b) = (Con a,Con b)
  toDict (toDict -> Dict, toDict -> Dict) = Dict
  unDict Dict = (unDict Dict,unDict Dict)

entail :: (HasCon a, HasCon b) => (a -> b) -> (Con a |- Con b)
entail f = unmapDict (toDict . f . unDict)

data Entail = Entail

instance FunctorC Entail (->) (|-) where
  type Entail %% a = Con a
  type OkF Entail a b = (HasCon a, HasCon b)
  (%) Entail = entail

-- -- Couldn't match type ‘(Con a, Con b)’ with ‘Con a && Con b’.
-- instance CartesianFunctor Entail (->) (|-) where preserveProd = Dict
-- -- Fails:
-- preserveProd :: Dict (MapDict %% (a && b)) ~ (MapDict %% a, MapDict %% b)

-- Isomorphic but not equal.

{--------------------------------------------------------------------
    Functors applied to given type argument
--------------------------------------------------------------------}

newtype Arg (s :: Type) a b = Arg { unArg :: a s -> b s }

instance Newtype (Arg s a b) where
  { type O (Arg s a b) = a s -> b s ; pack = Arg ; unpack = unArg }

instance Category (Arg s) where
  id = pack id
  (.) = inNew2 (.)

instance Cartesian (Arg s) where
  type Prod (Arg s) = (:*:)
  exl = pack (\ (a :*: _) -> a)
  exr = pack (\ (_ :*: b) -> b)
  (&&&) = inNew2 forkF

forkF :: (a t -> c t) -> (a t -> d t) -> a t -> (c :*: d) t
forkF = ((fmap.fmap.fmap) pack (&&&))

-- forkF ac ad = \ a -> (ac a :*: ad a)
-- forkF ac ad = \ a -> pack (ac a,ad a)
-- forkF ac ad = pack . (ac &&& ad)

instance Cocartesian (Arg s) where
  type Coprod (Arg s) = (:+:)
  inl = pack L1
  inr = pack R1
  (|||) = inNew2 eitherF

instance Terminal (Arg s) where
  type Unit (Arg s) = U1
  it = Arg (const U1)

instance CartesianClosed (Arg s) where
  type Exp (Arg s) = (+->) -- from ConCat.Misc
  apply = pack (\ (Fun1 f :*: a) -> f a)
  -- curry (Arg f) = Arg (pack . curry (f . pack))
  curry = inNew (\ f -> pack . curry (f . pack))
  uncurry = inNew (\ g -> uncurry (unpack . g) . unpack)

-- curry :: Arg s (a :*: b) c -> Arg s a (b +-> c)

-- Arg f :: Arg s (a :*: b) c
-- f :: (a :*: b) s -> c s
-- f . pack :: (a s,b s) -> c s
-- curry (f . pack) :: a s -> b s -> c s
-- pack . curry (f . pack) :: a s -> (b +-> c) s

--   apply   :: forall a b. Ok2 k a b => Prod k (Exp k a b) a `k` b
--   curry   :: Ok3 k a b c => (Prod k a b `k` c) -> (a `k` Exp k b c)
--   uncurry :: forall a b c. Ok3 k a b c
--           => (a `k` Exp k b c)  -> (Prod k a b `k` c)

toArg :: (HasV s a, HasV s b) => (a -> b) -> Arg s (V s a) (V s b)
toArg f = Arg (toV . f . unV)

-- unArg :: (HasV s a, HasV s b) => Arg s (V s a) (V s b) -> (a -> b)
-- unArg (Arg g) = unV . g . toV

data ToArg (s :: Type) = ToArg

instance FunctorC (ToArg s) (->) (Arg s) where
  type ToArg s %% a = V s a
  type OkF (ToArg s) a b = (HasV s a, HasV s b)
  (%) ToArg = toArg

instance   CartesianFunctor (ToArg s) (->) (Arg s) where   preserveProd = Dict
instance CocartesianFunctor (ToArg s) (->) (Arg s) where preserveCoprod = Dict

-- -- Couldn't match type ‘(->) a :.: V s b’ with ‘V s a +-> V s b’
-- instance CartesianClosedFunctor (ToArg s) (->) (Arg s) where preserveExp = Dict

{--------------------------------------------------------------------
    Linear maps
--------------------------------------------------------------------}

-- Linear map in row-major form
newtype LMap s a b = LMap (b (a s))

instance Num s => Category (LMap s) where
  type Ok (LMap s) = OkLF
  id = LMap idL
  LMap g . LMap f = LMap (g @. f)

instance OpCon (:*:) OkLF where inOp = Sub Dict

instance Num s => Cartesian (LMap s) where
  type Prod (LMap s) = (:*:)
  exl = LMap exlL
  exr = LMap exrL
  LMap g &&& LMap f = LMap (g `forkL` f)
  
instance Num s => Cocartesian (LMap s) where
  type Coprod (LMap s) = (:*:)
  inl = LMap inlL
  inr = LMap inrL
  LMap f ||| LMap g = LMap (f `joinL` g)

toLMap :: (OkLF b, HasL a, Num s) => Arg s a b -> LMap s a b
toLMap (Arg h) = LMap (linearL h)

data ToLMap s = ToLMap
instance Num s => FunctorC (ToLMap s) (Arg s) (LMap s) where
  type ToLMap s %% a = a
  type OkF (ToLMap s) a b = (OkLF b, HasL a)
  (%) ToLMap = toLMap

instance Num s => CartesianFunctor (ToLMap s) (Arg s) (LMap s) where preserveProd = Dict

#if 0

-- Apply a linear map
lapply :: (Zip a, Foldable a, Zip b, Num s) => LMap s a b -> Arg s a b
lapply (LMap ba) = Arg (lapplyL ba)

data Lapply s = Lapply
instance Num s => FunctorC (Lapply s) (LMap s) (Arg s) where
  type Lapply s %% a = a
  type OkF (Lapply s) a b = (Zip a, Foldable a, Zip b)
  (%) Lapply = lapply

#else

-- Apply a linear map
lapply :: (Zip a, Foldable a, Zip b, Num s) => LMap s a b -> (a s -> b s)
lapply (LMap ba) = lapplyL ba

data Lapply s = Lapply
instance Num s => FunctorC (Lapply s) (LMap s) (->) where
  type Lapply s %% a = a s
  type OkF (Lapply s) a b = (Zip a, Foldable a, Zip b)
  (%) Lapply = lapply

#endif

linear :: (Num s, HasL a, OkLF b) => Arg s a b -> LMap s a b
linear (Arg h) = LMap (linearL h)

data Linear s = Linear
instance Num s => FunctorC (Linear s) (Arg s) (LMap s) where
  type Linear s %% a = a
  type OkF (Linear s) a b = (HasL a, OkLF b)
  (%) Linear = linear

{--------------------------------------------------------------------
    Differentiable functions
--------------------------------------------------------------------}

-- | Differentiable function on vector space with field s
data D (s :: Type) a b = D (a s -> (b s, LMap s a b))

-- TODO: try a more functorish representation: (a :->: b :*: (a :->: b))

-- linearD :: Ok2 (LMap s) a b => (a s -> b s) -> D s a b
-- linearD h = D (h &&& const (toLMap (Arg h)))

linearD :: Ok2 (LMap s) a b => (a s -> b s) -> LMap s a b -> D s a b
linearD h h' = D (h &&& const h')

instance Num s => Category (D s) where
  type Ok (D s) = OkLF
  id = linearD id id
  D g . D f = D (\ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f'))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance Num s => Cartesian (D s) where
  type Prod (D s) = (:*:)
  exl = linearD fstF exl
  exr = linearD sndF exr
  D f &&& D g = D (\ a ->
    let (b,f') = f a
        (c,g') = g a
    in
      ((b :*: c), f' &&& g'))
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

instance Num s => Cocartesian (D s) where
  type Coprod (D s) = (:*:)
  inl = linearD (:*: zeroV) inl
  inr = linearD (zeroV :*:) inr
  D f ||| D g = D (\ (a :*: b) ->
    let (c,f') = f a
        (d,g') = g b
    in
      (c ^+^ d, f' ||| g'))
  {-# INLINE inl #-}
  {-# INLINE inr #-}
  {-# INLINE (|||) #-}

#if 0

f :: a s -> (c s, a s -> c s)
g :: b s -> (c s, b s -> c s)

a :: a s
b :: b s
c, d :: c s

f' :: a s -> c s
g' :: b s -> c s

#endif

data Deriv s = Deriv

instance Num s => FunctorC (Deriv s) (Arg s) (D s) where
  type Deriv s %% a = a
  type OkF (Deriv s) a b = OkF (ToLMap s) a b
  (%) Deriv = oops "Deriv % not implemented"

instance Num s => CartesianFunctor (Deriv s) (Arg s) (D s) where preserveProd = Dict

{--------------------------------------------------------------------
    Graphs / circuits
--------------------------------------------------------------------}

-- newtype Port = Port  Int deriving (Eq,Ord,Show,Enum)
type Port = Int

data Ports :: * -> * where
  UnitP   :: Ports ()
  BoolP   :: Port -> Ports Bool
  IntP    :: Port -> Ports Int
  DoubleP :: Port -> Ports Double
  PairP   :: Ports a -> Ports b -> Ports (a,b)

-- Component: primitive instance with inputs & outputs
data Comp = forall a b. Comp String (Ports a) (Ports b)

type GraphM = State (Port,[Comp])
type Graph  = Kleisli GraphM

genPort :: GraphM Port
genPort = do { (o,comps) <- get ; put (o+1,comps) ; return o }

class GenPorts a where genPorts :: GraphM (Ports a)

instance GenPorts ()     where genPorts = return UnitP 
instance GenPorts Bool   where genPorts = BoolP   <$> genPort
instance GenPorts Int    where genPorts = IntP    <$> genPort
instance GenPorts Double where genPorts = DoubleP <$> genPort

instance (GenPorts a, GenPorts b) => GenPorts (a,b) where
  genPorts = liftA2 PairP genPorts genPorts

-- Instantiate a primitive component
genComp1 :: GenPorts b => String -> Graph (Ports a) (Ports b)
genComp1 nm = Kleisli (\ a ->
              do b <- genPorts
                 modify (second (Comp nm a b :))
                 return b)

genComp2 :: GenPorts c => String -> Graph (Ports a, Ports b) (Ports c)
genComp2 nm = genComp1 nm . arr (uncurry PairP)

instance BoolCat Graph where
  type BoolOf Graph = Ports Bool
  notC = genComp1 "¬"
  andC = genComp2 "∧"
  orC  = genComp2 "∨"
  xorC = genComp2 "⊕"

instance Eq a => EqCat Graph (Ports a) where
  equal    = genComp2 "≡"
  notEqual = genComp2 "≠"

instance (Num a, GenPorts a) => NumCat Graph (Ports a) where
  type IntOf Graph = Ports Int
  negateC = genComp1 "negate"
  addC    = genComp2 "+"
  subC    = genComp2 "-"
  mulC    = genComp2 "×"
  powIC   = genComp2 "↑"

-- The Eq and Num constraints aren't strictly necessary, but they serve to
-- remind us of the expected translation from Eq and Num methods.

{--------------------------------------------------------------------
    Standardize types
--------------------------------------------------------------------}

class HasStd a where
  type Standard a
  toStd :: a -> Standard a
  unStd :: Standard a -> a
  -- defaults via Rep
  type Standard a = Rep a
  default toStd :: HasRep a => a -> Rep a
  default unStd :: HasRep a => Rep a -> a
  toStd = repr
  unStd = abst

standardize :: (HasStd a, HasStd b) => (a -> b) -> (Standard a -> Standard b)
standardize = toStd <~ unStd

instance (HasStd a, HasStd b) => HasStd (a,b) where
  type Standard (a,b) = (Standard a, Standard b)
  toStd = toStd *** toStd
  unStd = unStd *** unStd

instance (HasStd a, HasStd b) => HasStd (Either a b) where
  type Standard (Either a b) = Either (Standard a) (Standard b)
  toStd = toStd +++ toStd
  unStd = unStd +++ unStd

instance (HasStd a, HasStd b) => HasStd (a -> b) where
  type Standard (a -> b) = Standard a -> Standard b
  toStd = toStd <~ unStd
  unStd = unStd <~ toStd

#define StdPrim(ty) \
instance HasStd (ty) where { type Standard (ty) = (ty) ; toStd = id ; unStd = id }

StdPrim(())
StdPrim(Bool)
StdPrim(Int)
StdPrim(Float)
StdPrim(Double)

instance (HasStd a, HasStd b, HasStd c) => HasStd (a,b,c)

-- If this experiment works out, move HasStd to ConCat.Rep and add instances there.

data Standardize s = Standardize

instance FunctorC (Standardize s) (->) (->) where
  type Standardize s %% a = Standard a
  type OkF (Standardize s) a b = (HasStd a, HasStd b)
  (%) Standardize = standardize

instance CartesianFunctor       (Standardize s) (->) (->) where preserveProd   = Dict
instance CocartesianFunctor     (Standardize s) (->) (->) where preserveCoprod = Dict
instance CartesianClosedFunctor (Standardize s) (->) (->) where preserveExp    = Dict

{--------------------------------------------------------------------
    Memoization
--------------------------------------------------------------------}

class HasTrie a where
  type Trie a :: * -> *
  toTrie :: (a -> b) -> Trie a b
  unTrie :: Trie a b -> (a -> b)

data Pair a = a :# a deriving (Functor,Foldable,Traversable)

instance HasTrie Bool where
  type Trie Bool = Pair
  toTrie f = f False :# f True
  unTrie (f :# _) False = f
  unTrie (_ :# t) True  = t

-- instance HasTrie Int where ...

instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
  type Trie (Either a b) = Trie a :*: Trie b
  toTrie f = toTrie (f . Left) :*: toTrie (f . Right)
  unTrie (s :*: t) = either (unTrie s) (unTrie t)

instance (HasTrie a, HasTrie b) => HasTrie (a,b) where
  type Trie (a,b) = Trie a :.: Trie b
  toTrie f = Comp1 (toTrie (toTrie . curry f))
  unTrie (Comp1 t) = uncurry (unTrie .  unTrie t)

-- f :: (a,b) -> c
-- curry f :: a -> b -> c
-- toTrie . curry f :: a -> Trie b c
-- toTrie (toTrie . curry f) :: Trie a (Trie b c)
-- Comp1 (toTrie (toTrie . curry f)) :: (Trie a :.: Trie b) c

-- Memoized functions
infixr 0 :->:
newtype a :->: b = MF { unMF :: Trie a b }

toMemo :: HasTrie a => (a -> b) -> (a :->: b)
toMemo = MF . toTrie

unMemo :: HasTrie a => (a :->: b) -> (a -> b)
unMemo = unTrie . unMF

-- | Apply a unary function inside of a memo function
inMemo :: (HasTrie a, HasTrie c) =>
          ((a  ->  b) -> (c  ->  d))
       -> ((a :->: b) -> (c :->: d))
inMemo = toMemo <~ unMemo

-- | Apply a binary function inside of a trie
inMemo2 :: (HasTrie a, HasTrie c, HasTrie e) =>
           ((a  ->  b) -> (c  ->  d) -> (e  ->  f))
        -> ((a :->: b) -> (c :->: d) -> (e :->: f))
inMemo2 = inMemo <~ unMemo

instance Category (:->:) where
  type Ok (:->:) = HasTrie
  id  = toMemo id
  (.) = inMemo2 (.)

instance OpCon (,) HasTrie where inOp = Sub Dict

instance Cartesian (:->:) where
  type Prod (:->:) = (,)
  exl :: forall a b. Ok2 (:->:) a b => (a,b) :->: a
  exl = toMemo exl <+ okProd @(:->:) @a @b
  exr :: forall a b. Ok2 (:->:) a b => (a,b) :->: b
  exr = toMemo exr <+ okProd @(:->:) @a @b
  (&&&) = inMemo2 (&&&)

instance OpCon Either HasTrie where inOp = Sub Dict

instance Cocartesian (:->:) where
  type Coprod (:->:) = Either
  inl :: forall a b. Ok2 (:->:) a b => a :->: Either a b
  inl = toMemo inl <+ okCoprod @(:->:) @a @b
  inr :: forall a b. Ok2 (:->:) a b => b :->: Either a b
  inr = toMemo inr <+ okCoprod @(:->:) @a @b
  (|||) = inMemo2 (|||)

data ToMemo = ToMemo
instance FunctorC ToMemo (->) (:->:) where
  type ToMemo %% a = a
  type OkF ToMemo a b = HasTrie a
  (%) ToMemo = toMemo

data UnMemo = UnMemo
instance FunctorC UnMemo (:->:) (->) where
  type UnMemo %% a = a
  type OkF UnMemo a b = HasTrie a
  (%) UnMemo = unMemo

{--------------------------------------------------------------------
    Free vector spaces
--------------------------------------------------------------------}

class Enumerable a where enumerate :: [a]

instance Enumerable () where enumerate = [()]

instance Enumerable Bool where enumerate = [False,True]

instance (Enumerable a, Enumerable b) => Enumerable (Either a b) where
  enumerate = map Left enumerate ++ map Right enumerate

instance (Enumerable a, Enumerable b) => Enumerable (a,b) where
  enumerate = liftA2 (,) enumerate enumerate
instance (Enumerable a, Enumerable b, Enumerable c) => Enumerable (a,b,c) where
  enumerate = liftA3 (,,) enumerate enumerate enumerate

type Vec s a = a -> s

-- Linear map from (a -> s) to (b -> s)
newtype FL s a b = FL ((a,b) -> s)

class    (Eq a, Enumerable a) => OkFL a
instance (Eq a, Enumerable a) => OkFL a

instance Num s => Category (FL s) where
  type Ok (FL s) = OkFL
  id = FL (\ (a,a') -> if a == a' then 1 else 0)
  FL g . FL f = FL (\ (a,c) -> sum [g (b,c) * f (a,b) | b <- enumerate])

-- instance Num s => Cartesian (FL s) where
--   type Prod (FL s) = (,)
--   exl = FL _
