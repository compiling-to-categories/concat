{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilyDependencies #-}
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

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Like D, but drop the functor categories

module ConCat.E where

import Prelude hiding (id,(.),const,zipWith,curry,uncurry)
import qualified Prelude as P
import Data.Kind
import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:+:)(..),(:.:)(..))
import GHC.Prim (Any)
import Control.Applicative (liftA2,liftA3)
import Control.Monad ((<=<))
import Control.Arrow (arr,Kleisli(..))
import qualified Control.Arrow as A
import Control.Monad.State (State,modify,put,get,execState,StateT,evalStateT)
import Text.Show.Functions () -- for Funk

import Data.Constraint (Dict(..),(:-)(..),refl,trans,(\\))
import Control.Newtype
import Data.Pointed
import Data.Key

import ConCat.Misc ((:*),inNew,inNew2,oops,type (+->)(..),R)
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow (lapplyL,OkLF,idL,compL,exlL,exrL,forkL,itL,inlL,inrL,joinL,HasL(..))
import ConCat.Rep
import ConCat.Orphans

{--------------------------------------------------------------------
    Constraints
--------------------------------------------------------------------}

type Ok2 k a b         = (Ok k a, Ok k b)
type Ok3 k a b c       = (Ok2 k a b, Ok k c)
type Ok4 k a b c d     = (Ok3 k a b c, Ok k d)
type Ok5 k a b c d e   = (Ok4 k a b c d, Ok k e)
type Ok6 k a b c d e f = (Ok5 k a b c d e, Ok k f)

infixl 1 <+
(<+) :: (b => r) -> (a :- b) -> (a => r)
r <+ Sub Dict = r
{-# INLINE (<+) #-}
-- (<+) = (\\)

{--------------------------------------------------------------------
    Categories
--------------------------------------------------------------------}

infixr 9 .
class Category (k :: u -> u -> *) where
  type Ok k (a :: u) :: Constraint
  type Ok k a = ()
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

infixr 3 &&&, ***
class (OkProd k, Category k) => Cartesian k where
  type Prod k (a :: u) (b :: u) = (ab :: u) | ab -> a b
  exl :: Ok2 k a b => Prod k a b `k` a
  exr :: Ok2 k a b => Prod k a b `k` b
  (&&&) :: forall a c d. Ok3 k a c d => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)

class OkProd k where okProd :: Ok2 k a b :- Ok k (Prod k a b)

(***) :: forall k a b c d. (Cartesian k, Ok4 k a b c d)
      => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
f *** g = f . exl &&& g . exr  <+ okProd @k @a @b

dup :: (Cartesian k, Ok k a) => a `k` Prod k a a
dup = id &&& id

swapP :: forall k a b. (Cartesian k, Ok2 k a b) => Prod k a b `k` Prod k b a
swapP = exr &&& exl  <+ okProd @k @a @b

-- -- experiment
-- swapP' :: Cartesian k => Prod k a b `k` Prod k b a
-- swapP' = ccc (\ (a,b) -> (b,a))

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
class (OkCoprod k,Category k) => Cocartesian k where
  type Coprod k (a :: u) (b :: u) = (ab :: u) | ab -> a b
  inl :: Ok2 k a b => a `k` Coprod k a b
  inr :: Ok2 k a b => b `k` Coprod k a b
  (|||) :: forall a c d. Ok3 k a c d
        => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a)

class OkCoprod k where okCoprod :: Ok2 k a b :- Ok k (Coprod k a b)

(+++) :: forall k a b c d. (Cocartesian k, Ok4 k a b c d)
      => (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b)
f +++ g = inl . f ||| inr . g  <+ okCoprod @k @a @b

class (Category k, Ok k (Unit k)) => Terminal k where
  type Unit k :: u
  it :: Ok k a => a `k` Unit k

class (Cartesian k, Cocartesian k) => Distributive k where
  distl :: Prod k a (Coprod k u v) `k` Coprod k (Prod k a u) (Prod k a v)
  distr :: Prod k (Coprod k u v) b `k` Coprod k (Prod k u b) (Prod k v b)

class (OkExp k, Cartesian k) => CartesianClosed k where
  type Exp k (a :: u) (b :: u) = (ab :: u) | ab -> a b
  apply   :: forall a b. Ok2 k a b => Prod k (Exp k a b) a `k` b
  apply = uncurry id
          <+ okExp @k @a @b
  curry   :: Ok3 k a b c => (Prod k a b `k` c) -> (a `k` Exp k b c)
  uncurry :: forall a b c. Ok3 k a b c
          => (a `k` Exp k b c)  -> (Prod k a b `k` c)
  uncurry g = apply . first g
              <+ okProd @k @(Exp k b c) @b
              <+ okProd @k @a @b
              <+ okExp  @k @b @c
  {-# MINIMAL curry, (apply | uncurry) #-}

class OkExp k where okExp :: Ok2 k a b :- Ok k (Exp k a b)

class (Category k, Ok k (ConstObj k b)) => ConstCat k b where
  type ConstObj k b
  type ConstObj k b = b
  const :: Ok k a => b -> (a `k` ConstObj k b)

class (Cartesian k, Ok k (BoolOf k)) => BoolCat k where
  type BoolOf k
  notC :: BoolOf k `k` BoolOf k
  andC, orC, xorC :: Prod k (BoolOf k) (BoolOf k) `k` BoolOf k

okDup :: forall k a. OkProd k => Ok k a :- Ok k (Prod k a a)
okDup = okProd @k @a @a . dup

class (BoolCat k, Ok k a) => EqCat k a where
  equal, notEqual :: Prod k a a `k` BoolOf k
  notEqual = notC . equal    <+ okDup @k @a
  equal    = notC . notEqual <+ okDup @k @a

class (Category k, Ok k a) => NumCat k a where
  negateC :: a `k` a
  addC, subC, mulC :: Prod k a a `k` a
  -- default subC :: Cartesian k => Prod k a a `k` a
  -- subC = addC . second negateC <+ okProd @k @a @a
  type IntOf k :: u
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

instance Cartesian (->) where
  type Prod (->) a b = (a,b)
  exl = fst
  exr = snd
  (f &&& g) x = (f x, g x)

instance OkProd (->) where okProd = Sub Dict

instance Cocartesian (->) where
  type Coprod (->) a b = Either a b
  inl = Left
  inr = Right
  (|||) = either

instance OkCoprod (->) where okCoprod = Sub Dict

instance Terminal (->) where
  type Unit (->) = ()
  it = const ()

instance Distributive (->) where
  distl (a,uv) = ((a,) +++ (a,)) uv
  distr (uv,b) = ((,b) +++ (,b)) uv

instance CartesianClosed (->) where
  type Exp (->) a b = a -> b
  apply (f,x) = f x
  curry = P.curry
  uncurry = P.uncurry

instance OkExp (->) where okExp = Sub Dict

instance ConstCat (->) b where const = P.const

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
  type Prod (Kleisli m) a b = (a,b)
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
  type Coprod (Kleisli m) a b = Either a b
  inl = arr inl
  inr = arr inr
  (|||) = (A.|||)

instance Monad m => Terminal (Kleisli m) where
  type Unit (Kleisli m) = ()
  it = arr it

instance OkProd   (Kleisli m) where okProd   = Sub Dict
instance OkCoprod (Kleisli m) where okCoprod = Sub Dict
instance OkExp    (Kleisli m) where okExp    = Sub Dict

instance Monad m => Distributive (Kleisli m) where
  distl = arr distl
  distr = arr distr

instance Monad m => CartesianClosed (Kleisli m) where
  type Exp (Kleisli m) a b = Kleisli m a b
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
    Product of categories
--------------------------------------------------------------------}

infixr 7 :**:
-- | Product for binary type constructors
data (k :**: k') (a :: u) (b :: u) = k a b :**: k' a b

instance (Category k, Category k') => Category (k :**: k') where
  type Ok (k :**: k') a = (Ok k a, Ok k' a)
  id = id :**: id
  (g :**: g') . (f :**: f') = (g.f) :**: (g'.f')

#if 0

instance (Cartesian (k :: * -> * -> *), Cartesian (k' :: * -> * -> *)) => Cartesian (k :**: k') where
  type Prod (k :**: k') a b = (Prod k a b, Prod k' a b)
  exl = exl :**: exl
  exr = exr :**: exr
  (f :**: f') &&& (g :**: g') = (f &&& g) :**: (f' &&& g')
#if 0
  (f :**: f') *** (g :**: g') = (f *** g) :**: (f' *** g')
  dup   = dup   :**: dup
  swapP = swapP :**: swapP
  first (f :**: f') = first f :**: first f'
  second (f :**: f') = second f :**: second f'
  lassocP = lassocP :**: lassocP
  rassocP = rassocP :**: rassocP
#endif

instance (OkProd k, OkProd k') => OkProd (k :**: k') where okProd = Sub Dict

instance (Cocartesian k, Cocartesian k') => Cocartesian (k :**: k') where
  inl = inl :**: inl
  inr = inr :**: inr
  (f :**: f') ||| (g :**: g') = (f ||| g) :**: (f' ||| g')
#if 0
  (f :**: f') +++ (g :**: g') = (f +++ g) :**: (f' +++ g')
  jam = jam :**: jam
  swapS = swapS :**: swapS
  left (f :**: f') = left f :**: left f'
  right (f :**: f') = right f :**: right f'
  lassocS = lassocS :**: lassocS
  rassocS = rassocS :**: rassocS
#endif

-- working on these ones

instance (Terminal k, Terminal k') => Terminal (k :**: k') where
  -- type Unit (k :**: k) = Prod k (Unit k
  it = it :**: it

instance (CartesianClosed k, CartesianClosed k') => CartesianClosed (k :**: k') where
  apply = apply :**: apply
  -- apply = (apply . exl) :**: (apply . exr)
  -- apply :: forall a b. (Ok2 k a b, Ok2 k' a b)
  --       => (k :**: k') ((k :**: k') a b :* a) b
  -- apply = undefined -- (apply . exl) :**: _
  curry (f :**: f') = curry f :**: curry f'
  uncurry (g :**: g') = uncurry g :**: uncurry g'

instance (BoolCat k, BoolCat k') => BoolCat (k :**: k') where
  notC = notC :**: notC
  andC = andC :**: andC
  orC  = orC  :**: orC
  xorC = xorC :**: xorC

instance (EqCat k a, EqCat k' a) => EqCat (k :**: k') a where
  equal = equal :**: equal
  notEqual = notEqual :**: notEqual

instance (NumCat k a, NumCat k' a) => NumCat (k :**: k') a where
  negateC = negateC :**: negateC
  addC    = addC    :**: addC
  subC    = subC    :**: subC
  mulC    = mulC    :**: mulC
  powIC   = powIC   :**: powIC

#endif

-- Unit for binary type constructors
data U2 (a :: u) (b :: u) = U2 deriving (Show)

instance Category U2 where
  id = U2
  U2 . U2 = U2

#if 0

type family P (a :: u) (b :: u) = (ab :: u) | ab -> a b

instance Cartesian U2 where
  -- type Prod U2 a b = Any -- violates injectivity
  -- type Prod U2 a b = P a b  -- This definition breaks Prod (:-) ?!
  exl = U2
  exr = U2
  U2 &&& U2 = U2

instance OkProd U2 where okProd = Sub Dict

instance Cocartesian U2 where
  inl = U2
  inr = U2
  U2 ||| U2 = U2

instance OkCoprod U2 where okCoprod = Sub Dict

instance Terminal U2 where
  -- type Unit (U2 :: u -> u -> *) = ??
  it = U2

instance Distributive U2 where
  distl = U2
  distr = U2

instance CartesianClosed U2 where
  apply = U2
  curry U2 = U2
  uncurry U2 = U2

instance OkExp U2 where okExp = Sub Dict

instance BoolCat U2 where
  type BoolOf U2 = ()  -- arbitrary
  notC = U2
  andC = U2
  orC  = U2
  xorC = U2

instance EqCat U2 a where
  equal = U2
  notEqual = U2

instance NumCat U2 a where
  negateC = U2
  addC    = U2
  subC    = U2
  mulC    = U2
  powIC   = U2

#endif

{--------------------------------------------------------------------
    Constraint entailment
--------------------------------------------------------------------}

instance Category (:-) where
  id  = Sub Dict
  g . f = Sub (Dict <+ g <+ f)

instance Cartesian (:-) where
  type Prod (:-) a b = (a,b)
  exl = Sub Dict
  exr = Sub Dict
  f &&& g = Sub (Dict <+ f <+ g)

instance OkProd (:-) where okProd = Sub Dict

-- instance Category (:-) where
--   id  = refl
--   (.) = trans

instance Terminal (:-) where
  type Unit (:-) = ()
  it = Sub Dict

-- Tweaked from Data.Constraint
mapDict :: (a :- b) -> Dict a -> Dict b
mapDict (Sub q) Dict = q

unmapDict :: (Dict a -> Dict b) -> (a :- b)
unmapDict f = Sub (f Dict)

data MapDict = MapDict

instance FunctorC MapDict (:-) (->) where
  type MapDict %% a = Dict a
  type OkF MapDict a b = ()
  (%) MapDict = mapDict

-- -- Couldn't match type ‘Dict (a && b)’ with ‘(Dict a, Dict b)’
-- instance CartesianFunctor MapDict (:-) (->) where preserveProd = Dict

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

entail :: (HasCon a, HasCon b) => (a -> b) -> (Con a :- Con b)
entail f = unmapDict (toDict . f . unDict)

data Entail = Entail

instance FunctorC Entail (->) (:-) where
  type Entail %% a = Con a
  type OkF Entail a b = (HasCon a, HasCon b)
  (%) Entail = entail

-- -- Couldn't match type ‘(Con a, Con b)’ with ‘Con a && Con b’.
-- instance CartesianFunctor Entail (->) (:-) where preserveProd = Dict
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

instance OkProd (Arg s) where okProd = Sub Dict

instance Cartesian (Arg s) where
  type Prod (Arg s) a b = a :*: b
  exl = pack (\ (a :*: _) -> a)
  exr = pack (\ (_ :*: b) -> b)
  (&&&) = inNew2 forkF

forkF :: (a t -> c t) -> (a t -> d t) -> a t -> (c :*: d) t
forkF = ((fmap.fmap.fmap) pack (&&&))

-- forkF ac ad = \ a -> (ac a :*: ad a)
-- forkF ac ad = \ a -> pack (ac a,ad a)
-- forkF ac ad = pack . (ac &&& ad)

instance OkCoprod (Arg s) where okCoprod = Sub Dict

instance Cocartesian (Arg s) where
  type Coprod (Arg s) a b = a :+: b
  inl = pack L1
  inr = pack R1
  (|||) = inNew2 eitherF

instance Terminal (Arg s) where
  type Unit (Arg s) = U1
  it = Arg (const U1)

instance OkExp (Arg s) where okExp = Sub Dict

instance CartesianClosed (Arg s) where
  type Exp (Arg s) a b = a +-> b -- from ConCat.Misc
  apply = pack (\ (Fun1 f :*: a) -> f a)
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
newtype LM s a b = LMap (V s b (V s a s))

scale :: V s s ~ Par1 => s -> LM s s s
scale s = LMap (Par1 (Par1 s))

class    (HasV s a, OkLF (V s a)) => OkLM s a
instance (HasV s a, OkLF (V s a)) => OkLM s a

instance Num s => Category (LM s) where
  type Ok (LM s) a = OkLM s a
  id = LMap idL
  LMap g . LMap f = LMap (g `compL` f)

instance OkProd (LM s) where okProd = Sub Dict

instance Num s => Cartesian (LM s) where
  type Prod (LM s) a b = a :* b
  exl = LMap exlL
  exr = LMap exrL
  LMap g &&& LMap f = LMap (g `forkL` f)

instance OkCoprod (LM s) where okCoprod = Sub Dict
  
instance Num s => Cocartesian (LM s) where
  type Coprod (LM s) a b = a :* b
  inl = LMap inlL
  inr = LMap inrL
  LMap f ||| LMap g = LMap (f `joinL` g)

instance Num s => Terminal (LM s) where
  type Unit (LM s) = ()
  it = LMap itL

toLMap :: (Ok2 (LM s) a b, HasL (V s a), Num s) => (a -> b) -> LM s a b
toLMap h = LMap (linearL (inV h))

data ToLMap s = ToLMap
instance Num s => FunctorC (ToLMap s) (->) (LM s) where
  type ToLMap s %% a = a
  type OkF (ToLMap s) a b = (Ok2 (LM s) a b, HasL (V s a))
  (%) ToLMap = toLMap

instance Num s => CartesianFunctor (ToLMap s) (->) (LM s) where preserveProd = Dict

-- Apply a linear map
lapply :: (Ok2 (LM s) a b, Num s) => LM s a b -> (a -> b)
lapply (LMap ba) = onV (lapplyL ba)

data Lapply s = Lapply
instance Num s => FunctorC (Lapply s) (LM s) (->) where
  type Lapply s %% a = a
  type OkF (Lapply s) a b = Ok2 (LM s) a b
  (%) Lapply = lapply

linear :: (Ok2 (LM s) a b, HasL (V s a), Num s) => (a -> b) -> LM s a b
linear h = LMap (linearL (inV h))

data Linear s = Linear
instance Num s => FunctorC (Linear s) (->) (LM s) where
  type Linear s %% a = a
  type OkF (Linear s) a b = (Ok2 (LM s) a b, HasL (V s a))
  (%) Linear = linear

{--------------------------------------------------------------------
    Differentiable functions
--------------------------------------------------------------------}

-- | Differentiable function on vector space with field s
data DF s a b = D { unD :: a -> b :* LM s a b }

deriv :: (a -> b) -> (a -> LM s a b)
deriv f = snd . unD (andDeriv f)
-- deriv f = snd . h where D h = andDeriv (Arg f)

andDeriv :: (a -> b) -> DF s a b
andDeriv f = D (f &&& deriv f)  -- specification

linearD :: (Num s, Ok2 (LM s) a b) => LM s a b -> DF s a b
linearD m = D (lapply m &&& const m)

-- linearD :: (Num s, Ok2 (LM s) a b) => (a -> b) -> LM s a b -> DF s a b
-- linearD f f' = D (f &&& const f')

instance Num s => Category (DF s) where
  type Ok (DF s) a = Ok (LM s) a
  id = linearD id
  D g . D f = D (\ a -> let { (b,f') = f a; (c,g') = g b } in (c, g' . f'))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance OkProd (DF s) where okProd = Sub Dict

instance Num s => Cartesian (DF s) where
  type Prod (DF s) a b = a :* b
  exl = linearD exl
  exr = linearD exr
  D f &&& D g = D (\ a -> let { (b,f') = f a ; (c,g') = g a } in ((b,c), f' &&& g'))
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

#if 0
addV :: forall s a. (HasV s a, Zip (V s a), Num s) => a -> a -> a
addV = onV2 (^+^)

instance OkCoprod (DF s) where okCoprod = Sub Dict

instance Num s => Cocartesian (DF s) where
  type Coprod (DF s) a b = a :* b
  inl = linearD inl
  inr = linearD inr
  D f ||| D g = D (\ (a,b) -> let { (c,f') = f a ; (d,g') = g b } in (addV @s c d, f' ||| g'))
  {-# INLINE inl #-}
  {-# INLINE inr #-}
  {-# INLINE (|||) #-}
#endif

#if 0

f :: a s -> (c s, a s -> c s)
g :: b s -> (c s, b s -> c s)

a :: a s
b :: b s
c, d :: c s

f' :: a s -> c s
g' :: b s -> c s

#endif

-- class (Category k, Ok k a) => NumCat (k :: u -> u -> *) (a :: u) where

-- data DF s (a :: * -> *) (b :: * -> *) 

-- instance Num s => NumCat (DF s) Par1 where
--   negateC = linearD (scale (-1))
--   addC = linearD (id ||| id)
--   subC = linearD (id ||| scale (-1))
--   mulC = D (\ (Par1 a :*: Par1 b) -> (Par1 (a * b), scale b ||| scale a))
--   powIC = undefined

-- foo1 :: Num s => (Par1 :*: Par1) s -> Par1 s
-- foo1 (Par1 a :*: Par1 b) = Par1 (a * b)

-- foo2 :: Num s => (Par1 :*: Par1) s -> LM s (Par1 :*: Par1) Par1
-- foo2 (Par1 a :*: Par1 b) = scale b ||| scale a

-- foo3 :: Num s => (Par1 :*: Par1) s -> Par1 s :* LM s (Par1 :*: Par1) Par1
-- -- foo3 = foo1 &&& foo2
-- foo3 (Par1 a :*: Par1 b) = (Par1 (a * b), scale b ||| scale a)

-- (Par1 :* Par1) s -> Par1 s

-- (\ (Par1 x :*: Par1 y) -> Par1 (x*y))

data Deriv s = Deriv
instance Num s => FunctorC (Deriv s) (->) (DF s) where
  type Deriv s %% a = a
  type OkF (Deriv s) a b = OkF (ToLMap s) a b
  (%) Deriv = andDeriv
              -- oops "Deriv % not implemented"

instance Num s => CartesianFunctor (Deriv s) (->) (DF s) where preserveProd = Dict

{--------------------------------------------------------------------
    Circuits
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
  type Ok (:->:) a = HasTrie a
  id  = toMemo id
  (.) = inMemo2 (.)

instance OkProd (:->:) where okProd = Sub Dict

instance Cartesian (:->:) where
  type Prod (:->:) a b = (a,b)
  exl :: forall a b. Ok2 (:->:) a b => (a,b) :->: a
  exl = toMemo exl <+ okProd @(:->:) @a @b
  exr :: forall a b. Ok2 (:->:) a b => (a,b) :->: b
  exr = toMemo exr <+ okProd @(:->:) @a @b
  (&&&) = inMemo2 (&&&)

instance OkCoprod (:->:) where okCoprod = Sub Dict

instance Cocartesian (:->:) where
  type Coprod (:->:) a b = Either a b
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
    Free vector spaces as functions
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
  type Ok (FL s) a = OkFL a
  id = FL (\ (a,a') -> if a == a' then 1 else 0)
  FL g . FL f = FL (\ (a,c) -> sum [g (b,c) * f (a,b) | b <- enumerate])

-- instance Num s => Cartesian (FL s) where
--   type Prod (FL s) = (,)
--   exl = FL _

#if 0

{--------------------------------------------------------------------
    Affine functions
--------------------------------------------------------------------}

data Affine s a b = Affine b (LM s a b)

linearA :: (Num s, Ok2 (LM s) a b) => LM s a b -> Affine s a b
linearA = Affine zeroV

instance Num s => Category (Affine s) where
  type Ok (Affine s) a = OkLF a
  id = linearA id
  Affine b g . Affine a f = Affine (b ^+^ lapply g a) (g . f)

instance Num s => Cartesian (Affine s) where
  type Prod (Affine s) a b = a :*: b
  exl = linearA exl
  exr = linearA exr
  Affine b f &&& Affine c g = Affine (b :*: c) (f &&& g)

instance OkProd (Affine s) where okProd = Sub Dict

instance Num s => Cocartesian (Affine s) where
  type Coprod (Affine s) a b = a :*: b
  inl = linearA inl
  inr = linearA inr
  Affine c f ||| Affine d g = Affine (c ^+^ d) (f ||| g)

instance OkCoprod (Affine s) where okCoprod = Sub Dict

-- ...

#endif

{--------------------------------------------------------------------
    Polynomials
--------------------------------------------------------------------}

#if 0

newtype Poly a b = Poly [Double]

instance Category (Poly :: * -> * -> *) where
  type Ok Poly a = a ~ Double
  id = undefined
  (.) = undefined

instance Cartesian Poly where ...

#endif

{--------------------------------------------------------------------
    Functions with constant folding
--------------------------------------------------------------------}

data Funk a b = FunConst b | Fun (a -> b)

-- TODO: generalize from (->)

instance Show b => Show (Funk a b) where
  showsPrec p (FunConst b) = showsApp "const" b p
                             -- showsApp "FunConst" b p
  showsPrec p (Fun f)      = showsPrec p f
                             -- showsApp "Fun"      f p

showsApp :: Show b => String -> b -> Int -> ShowS
showsApp nm b p = showString (nm ++ " ") . showParen (p >= 9) (showsPrec 10 b)

applyFunk :: Funk a b -> (a -> b)
applyFunk (FunConst b) = const b
applyFunk (Fun f)      = f

instance Category Funk where
  id = Fun id
  Fun g . Fun f = Fun (g . f)
  g . FunConst a = FunConst (applyFunk g a)
  FunConst b . _ =  FunConst b

-- g . const a == const (g a)
-- const b . f == const b

instance Cartesian Funk where
  type Prod Funk a b = (a,b)
  exl = Fun exl
  exr = Fun exr
  FunConst c &&& FunConst d = FunConst (c,d)
  f &&& g = Fun (applyFunk f &&& applyFunk g)

-- const c &&& const d == const (c,d)

instance OkProd Funk where okProd = Sub Dict

-- What if *part* of the structure is known to be constant?
-- Possibly a more interesting product type.
-- If we apply exl to a left-constant pair, we get a constant function.

instance Cocartesian Funk where
  type Coprod Funk a b = Either a b
  inl = Fun inl
  inr = Fun inr
  f ||| g =  Fun (applyFunk f ||| applyFunk g)

instance OkCoprod Funk where okCoprod = Sub Dict

instance ConstCat Funk b where const = FunConst

-- (|||) :: (a `k` c) -> (b `k` c) -> ((a + b) `k` c)

-- (f ||| g) (Left  a) == f a
-- (f ||| g) (Right b) == g b

-- const f

-- Then first-order: constant, affine, or general. Other variants?

c1 :: Funk Int Int
c1 = const 3

c2 :: Funk Int Int
c2 = Fun succ

c3 :: Funk Int Int
c3 = c2 . c1

c4 :: Funk Int Int
c4 = c1 . c2


infixr 3 :&&&, :***
infixr 2 :+++, :|||

data Funky :: * -> * -> * where
  AllConst  :: {- Eq b => -} b -> Funky a b
  Id :: Funky a a
  (:&&&) :: Funky a c -> Funky a d -> Funky a (c,d)
  CompExl :: Funky a c -> Funky (a,b) c
  CompExr :: Funky b c -> Funky (a,b) c
  (:|||) :: Funky a c -> Funky b c -> Funky (Either a b) c
  InlComp :: Funky a c -> Funky a (Either c d)
  InrComp :: Funky a d -> Funky a (Either c d)
  Fun' :: (a -> b) -> Funky a b

-- TODO: generalize from (->): Funky k a b

pattern (:***) :: Funky a c -> Funky b d -> Funky (a,b) (c,d)
pattern f :*** g = CompExl f :&&& CompExr g

pattern Cross :: Funky a c -> Funky b d -> Funky (a,b) (c,d)
pattern Cross f g = CompExl f :&&& CompExr g

pattern (:+++) :: Funky a c -> Funky b d -> Funky (Either a b) (Either c d)
pattern f :+++ g = InlComp f :||| InrComp g

-- TODO: "Fork", "Join", "Cross", "Plus" --> ":&&&", ":|||", ":***", ":+++"

knownEq :: Funky a b -> Funky a b -> Bool
-- knownEq (AllConst b) (AllConst b') = b == b'  -- needs Eq
knownEq Id           Id            = True
knownEq (f :&&& g)   (f' :&&& g')  = knownEq f f' && knownEq g g'
knownEq (CompExl f)  (CompExl g)   = knownEq f g
knownEq (CompExr f)  (CompExr g)   = knownEq f g
knownEq (f :||| g)   (f' :||| g')  = knownEq f f' && knownEq g g'
knownEq (InlComp f)  (InlComp g)   = knownEq f g
knownEq (InrComp f)  (InrComp g)   = knownEq f g
knownEq _            _             = False

-- -- Convert to Syn
-- instance Show b => Show (Funky a b) where

applyFunky :: Funky a b -> (a -> b)
applyFunky (AllConst b) = const b
applyFunky Id           = id
applyFunky (CompExl f)  = applyFunky f . exl
applyFunky (CompExr g)  = applyFunky g . exr
applyFunky (f :&&& g)   = applyFunky f &&& applyFunky g
applyFunky (f :||| g)   = applyFunky f ||| applyFunky g
applyFunky (InlComp f)  = inl . applyFunky f
applyFunky (InrComp g)  = inr . applyFunky g
applyFunky (Fun' h)     = h

instance Category Funky where
  id = Fun' id
  AllConst b . _ = AllConst b
  Id . f = f
  CompExl h . (f :&&& _) = h . f
  CompExr h . (_ :&&& g) = h . g
  (AllConst c :&&& g) . f = AllConst c &&& g . f
  (g  :&&& AllConst c) . f = (g . f) &&& AllConst c
  (CompExl f :&&& CompExr g) . (h :&&& k) = (f . h) &&& (g . k)
  -- (f :*** g) . (h :&&& k) = ((f . h) &&& (g . k))  -- GHC bug?
  InlComp g . f = InlComp (g . f)
  InrComp g . f = InrComp (g . f)
  g . AllConst a = AllConst (applyFunky g a)
  g . Id = g
  g . CompExl f = CompExl (g . f)
  g . CompExr f = CompExr (g . f)
  g . f = Fun' (applyFunky g . applyFunky f)
#if 0
#endif

-- f :: F p r
-- g :: F q s
-- h :: F u p
-- k :: F u q

-- f &&& g :: F 


-- (g &&& h) . f

--  (h . exl) . (f &&& g) == h . f
--  (h . exr) . (f &&& g) == h . g

-- (f *** g) . (h &&& k) == (f . h) &&& (g . k)

-- (f . exl &&& g . exr) . (h &&& k) == (f . h) &&& (g . k)

-- (const c &&& g) . f == const c &&& (g . f)
-- (g &&& const d) . f == (g . f) &&& const d

-- (inl . g) . f == inl . (g . f)
-- (inr . g) . f == inr . (g . f)

-- g . const a = const (g a)
-- g . (f . exl) = (g . f) . exl
-- g . (f . exr) = (g . f) . exr

-- g . (const c &&& f) == ... -- precompute! what do I need?
-- g . (f &&& const c) == ... -- precompute! what do I need?
-- g . (inl . f) == ??

-- general partial evaluation?

instance Cartesian Funky where
  type Prod Funky a b = (a,b)
  exl = CompExl id
  exr = CompExr id
  AllConst c &&& AllConst d = AllConst (c,d)
  CompExl Id &&& CompExr Id = Id  -- generalize to other detectably equal terms?
  -- CompExl f &&& CompExr f' | knownEq f f' = f
  f &&& g = f :&&& g

instance OkProd Funky where okProd = Sub Dict

-- exl &&& exr == id

-- (f &&& g) . h == (f . h) &&& (g . h)

-- exl . h &&& exr . h == h

-- f . exl . h &&& g . exr . h == (f *** g) . (exl . h &&& exr . h) == (f *** g) . h === (f . exl &&& g . exr) . h

-- exl &&& exr


-- Idea: Represent Funky'' a b as forall ...

{--------------------------------------------------------------------
    Polynomials
--------------------------------------------------------------------}

type OkPoly b = (Pointed b, Functor b, Zip b)  -- OkLF b ?

-- Poly R = []
-- Poly (a,b) = Poly a :.: Poly b

class Functor (PolyF a) => HasPoly a where
  type PolyF (a :: * -> *) :: * -> *
  evalPoly :: (OkPoly c, Num s) => PolyF a (c s) -> a s -> c s

instance HasPoly U1 where
  type PolyF U1 = U1
  evalPoly :: (OkPoly c, Num s) => U1 (c s) -> U1 s -> c s
  evalPoly U1 U1 = zeroV

instance HasPoly Par1 where
  type PolyF Par1 = []
  evalPoly :: (OkPoly c, Num s) => [c s] -> Par1 s -> c s
  evalPoly c (Par1 s) = foldr (\ w z -> w ^+^ s *^ z) zeroV c

instance (HasPoly a, HasPoly b) => HasPoly (a :*: b) where
  type PolyF (a :*: b) = PolyF a :.: PolyF b
  evalPoly :: (OkPoly c, Num s) => (PolyF a :.: PolyF b) (c s) -> (a :*: b) s -> c s
  evalPoly (Comp1 w) (a :*: b) = evalPoly (flip evalPoly b <$> w) a

#if 0
  
w ::: PolyF a (PolyF b (c s))
a :: a s
b :: b s

flip evalPoly b :: PolyF b (c s) -> c s
flip evalPoly b <$> w :: PolyF a (c s)
evalPoly (flip evalPoly b <$> w) a :: c s

#endif

data Poly a b = forall s. Num s => Poly (PolyF a (b s))

-- instance Category Poly where
--   id = ...
