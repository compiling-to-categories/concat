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

import Data.Constraint (Dict(..),(:-)(..),refl,trans,(\\))
import Control.Newtype
import Data.Pointed
import Data.Key

import ConCat.Misc (Yes1,inNew,inNew2,oops,type (+->)(..))
import ConCat.Free.VectorSpace
import ConCat.Free.LinearRow (OkLF,idL,(@.),exlL,exrL,forkL,inlL,inrL,joinL,HasL(..))
import ConCat.Orphans

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

{--------------------------------------------------------------------
    Categories
--------------------------------------------------------------------}

class Category k where
  type Ok k :: u -> Constraint
  type Ok k = Yes1
  id  :: Ok k a => a `k` a
  infixr 9 .
  (.) :: forall b c a. Ok3 k a b c => (b `k` c) -> (a `k` b) -> (a `k` c)

-- | Category with product.
class ({-OpCon (Prod k) (Ok k), -}Category k) => Cartesian k where
  type Prod k :: u -> u -> u
  exl :: Ok2 k a b => Prod k a b `k` a
  exr :: Ok2 k a b => Prod k a b `k` b
  (&&&) :: forall a c d. Ok3 k a c d => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)

-- | Category with coproduct.
class ({-OpCon (Coprod k) (Ok' k), -}Category k) => Cocartesian k where
  type Coprod k :: u -> u -> u
  inl :: Ok2 k a b => a `k` Coprod k a b
  inr :: Ok2 k a b => b `k` Coprod k a b
  infixr 2 |||
  (|||) :: forall a c d. Ok3 k a c d
        => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a)

class (Category k, Ok k (Unit k)) => Terminal k where
  type Unit k :: u
  it :: Ok k a => a `k` Unit k

--     • Illegal constraint ‘Ok k (Unit k)’ in a superclass context
--         (Use UndecidableInstances to permit this)

class ({-OpCon (Exp k) (Ok' k), -}Cartesian k) => CartesianClosed k where
  type Exp k :: u -> u -> u
  apply   :: forall a b. Ok2 k a b => Prod k (Exp k a b) a `k` b
  -- apply = uncurry id
  --         <+ okExp @k @a @b
  curry   :: Ok3 k a b c => (Prod k a b `k` c) -> (a `k` Exp k b c)
  uncurry :: forall a b c. Ok3 k a b c
          => (a `k` Exp k b c)  -> (Prod k a b `k` c)
  -- uncurry g = apply . first g
  --             <+ okProd @k @(Exp k b c) @b
  --             <+ okProd @k @a @b
  --             <+ okExp @k @b @c

instance Category (->) where
  id  = P.id
  (.) = (P..)

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

{--------------------------------------------------------------------
    Functors
--------------------------------------------------------------------}

infixr 9 %
infixr 9 %%

class (Category src, Category trg) =>
      FunctorC f (src :: u -> u -> Type) (trg :: v -> v -> Type) | f -> src trg where
  type f %% (a :: u) :: v
  type OkF f (a :: u) (b :: u) :: Constraint
  (%) :: forall a b. OkF f a b => f -> src a b -> trg (f %% a) (f %% b)

class FunctorC f src trg => CartesianFunctor f src trg where
  prodToProd :: Dict ((f %% Prod src a b) ~ Prod trg (f %% a) (f %% b))
  -- default prodToProd :: (f %% Prod src a b) ~ Prod trg (f %% a) (f %% b)
  --              => Dict ((f %% Prod src a b) ~ Prod trg (f %% a) (f %% b))
  -- prodToProd = Dict

-- This prodToProd default doesn't work in instances. Probably a GHC bug.

class FunctorC f src trg => CocartesianFunctor f src trg where
  coprodToCoprod :: Dict ((f %% Coprod src a b) ~ Coprod trg (f %% a) (f %% b))

class FunctorC f src trg => CartesianClosedFunctor f src trg where
  expToExp :: Dict ((f %% Exp src a b) ~ Exp trg (f %% a) (f %% b))

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

newtype UT (s :: Type) f g = UT (f s -> g s)

instance Newtype (UT s f g) where
  type O (UT s f g) = f s -> g s
  pack h = UT h
  unpack (UT h) = h

instance Category (UT s) where
  id = pack id
  (.) = inNew2 (.)

instance Cartesian (UT s) where
  type Prod (UT s) = (:*:)
  exl = pack (\ (fs :*: _ ) -> fs)
  exr = pack (\ (_  :*: gs) -> gs)
  (&&&) = inNew2 forkF

forkF :: (a t -> c t) -> (a t -> d t) -> a t -> (c :*: d) t
forkF = ((fmap.fmap.fmap) pack (&&&))

-- forkF ac ad = \ a -> (ac a :*: ad a)
-- forkF ac ad = \ a -> pack (ac a,ad a)
-- forkF ac ad = pack . (ac &&& ad)

instance Cocartesian (UT s) where
  type Coprod (UT s) = (:+:)
  inl = pack L1
  inr = pack R1
  (|||) = inNew2 eitherF

instance Terminal (UT s) where
  type Unit (UT s) = U1
  it = UT (const U1)

instance CartesianClosed (UT s) where
  type Exp (UT s) = (+->) -- from ConCat.Misc
  apply = pack (\ (Fun1 f :*: a) -> f a)
  -- curry (UT f) = UT (pack . curry (f . pack))
  curry = inNew (\ f -> pack . curry (f . pack))
  uncurry = inNew (\ g -> uncurry (unpack . g) . unpack)

-- curry :: UT s (a :*: b) c -> UT s a (b +-> c)

-- UT f :: UT s (a :*: b) c
-- f :: (a :*: b) s -> c s
-- f . pack :: (a s,b s) -> c s
-- curry (f . pack) :: a s -> b s -> c s
-- pack . curry (f . pack) :: a s -> (b +-> c) s

--   apply   :: forall a b. Ok2 k a b => Prod k (Exp k a b) a `k` b
--   curry   :: Ok3 k a b c => (Prod k a b `k` c) -> (a `k` Exp k b c)
--   uncurry :: forall a b c. Ok3 k a b c
--           => (a `k` Exp k b c)  -> (Prod k a b `k` c)

toUT :: (HasV s a, HasV s b) => (a -> b) -> UT s (V s a) (V s b)
toUT f = UT (toV . f . unV)

-- unUT :: (HasV s a, HasV s b) => UT s (V s a) (V s b) -> (a -> b)
-- unUT (UT g) = unV . g . toV

data ToUT (s :: Type) = ToUT

instance FunctorC (ToUT s) (->) (UT s) where
  type ToUT s %% a = V s a
  type OkF (ToUT s) a b = (HasV s a, HasV s b)
  (%) ToUT = toUT

instance   CartesianFunctor (ToUT s) (->) (UT s) where   prodToProd   = Dict
instance CocartesianFunctor (ToUT s) (->) (UT s) where coprodToCoprod = Dict

-- -- Couldn't match type ‘(->) a :.: V s b’ with ‘V s a +-> V s b’
-- instance CartesianClosedFunctor (ToUT s) (->) (UT s) where expToExp = Dict

infixr 1 |-
type (|-) = (:-)

infixl 1 <+
(<+) :: (b => r) -> (a |- b) -> (a => r)
r <+ Sub Dict = r
{-# INLINE (<+) #-}
-- (<+) = (\\)

instance Category (|-) where
  id  = refl
  (.) = trans

infixr 3 &&
class    (a,b) => a && b
instance (a,b) => a && b

--     • Potential superclass cycle for ‘&&’
--         one of whose superclass constraints is headed by a type variable:
--           ‘a’
--       Use UndecidableSuperClasses to accept this

instance Cartesian (|-) where
  type Prod (|-) = (&&)
  exl = Sub Dict
  exr = Sub Dict
  f &&& g = Sub (Dict <+ f <+ g)

instance Terminal (|-) where
  type Unit (|-) = ()
  it = Sub Dict

mapDict :: (a :- b) -> Dict a -> Dict b
mapDict (Sub q) Dict = q

data MapDict = MapDict

instance FunctorC MapDict (|-) (->) where
  type MapDict %% a = Dict a
  type OkF MapDict a b = ()
  (%) MapDict = mapDict

-- -- Couldn't match type ‘Dict (a && b)’ with ‘(Dict a, Dict b)’
-- instance CartesianFunctor MapDict (|-) (->) where prodToProd = Dict

-- Linear map in row-major form
data LMap s a b = LMap (b (a s))

instance Newtype (LMap s a b) where
  type O (LMap s a b) = b (a s)
  pack h = LMap h
  unpack (LMap h) = h

class    (Num s, OkLF a) => OkLMap s a
instance (Num s, OkLF a) => OkLMap s a

instance Category (LMap s) where
  type Ok (LMap s) = OkLMap s
  id = pack idL
  (.) = inNew2 (@.)

instance Cartesian (LMap s) where
  type Prod (LMap s) = (:*:)
  exl = pack exlL
  exr = pack exrL
  (&&&) = inNew2 forkL
  
instance Cocartesian (LMap s) where
  type Coprod (LMap s) = (:*:)
  inl = pack inlL
  inr = pack inrL
  (|||) = inNew2 joinL

toLMap :: (OkLF b, HasL a, Num s) => UT s a b -> LMap s a b
toLMap (UT h) = LMap (linear' h)

data ToLMap s = ToLMap
instance FunctorC (ToLMap s) (UT s) (LMap s) where
  type ToLMap s %% a = a
  type OkF (ToLMap s) a b = (OkLF b, HasL a, Num s)
  (%) ToLMap = toLMap

instance CartesianFunctor (ToLMap s) (UT s) (LMap s) where prodToProd = Dict


-- | Differentiable function on vector space with field s
data D (s :: Type) a b = D (a s -> (b s, LMap s a b))

-- TODO: try a more functorish representation: (a :->: b :*: (a :->: b))

-- linearD :: Ok2 (LMap s) a b => (a s -> b s) -> D s a b
-- linearD h = D (h &&& const (toLMap (UT h)))

linearD :: Ok2 (LMap s) a b => (a s -> b s) -> LMap s a b -> D s a b
linearD h h' = D (h &&& const h')

instance Category (D s) where
  type Ok (D s) = OkLMap s
  id = linearD id id
  D g . D f = D (\ a ->
    let (b,f') = f a
        (c,g') = g b
    in
      (c, g' . f'))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance Cartesian (D s) where
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

instance Cocartesian (D s) where
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

instance FunctorC (Deriv s) (UT s) (D s) where
  type Deriv s %% a = a
  type OkF (Deriv s) a b = OkF (ToLMap s) a b
  (%) Deriv = oops "Deriv % not implemented"

instance CartesianFunctor (Deriv s) (UT s) (D s) where prodToProd = Dict
