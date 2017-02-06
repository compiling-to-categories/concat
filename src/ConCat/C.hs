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

-- {-# LANGUAGE TypeInType #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Experiment with polykinded category theory functors

module ConCat.C where

import Prelude hiding (id,(.))
import qualified Prelude as P
import Data.Kind

import Data.Constraint (Dict(..),(:-)(..),refl,trans,(\\))

import ConCat.Misc (Yes1)
import ConCat.Free.VectorSpace

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

class Category k where
  type Ok k :: u -> Constraint
  type Ok k = Yes1
  id  :: Ok k a => a `k` a
  infixr 9 .
  (.) :: forall b c a. Ok3 k a b c => (b `k` c) -> (a `k` b) -> (a `k` c)

instance Category (->) where
  id  = P.id
  (.) = (P..)

infixr 9 %
infixr 9 %%

class FunctorC f (src :: u -> u -> Type) (trg :: v -> v -> Type) | f -> src trg where
  type f %% (a :: u) :: v
  type OkF f (a :: u) (b :: u) :: Constraint
  (%) :: forall a b. OkF f a b => f -> src a b -> trg (f %% a) (f %% b)

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

newtype UT s f g = UT (f s -> g s)

toUT :: (HasV s a, HasV s b) => (a -> b) -> UT s (V s a) (V s b)
toUT f = UT (toV . f . unV)

-- unUT :: (HasV s a, HasV s b) => UT s (V s a) (V s b) -> (a -> b)
-- unUT (UT g) = unV . g . toV

data ToUT (s :: Type) = ToUT

instance FunctorC (ToUT s) (->) (UT s) where
  type ToUT s %% a = V s a
  type OkF (ToUT s) a b = (HasV s a, HasV s b)
  (%) ToUT = toUT

-- | Category with product.
class ({-OpCon (Prod k) (Ok k), -}Category k) => Cartesian k where
  type Prod k :: u -> u -> u
  exl :: Ok2 k a b => Prod k a b `k` a
  exr :: Ok2 k a b => Prod k a b `k` b
  (&&&) :: forall a c d. Ok3 k a c d => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)

class FunctorC f src trg => CartesianFunctor f src trg where
  prodToProd :: Dict ((f %% Prod src a b) ~ Prod trg (f %% a) (f %% b))

-- | Category with coproduct.
class ({-OpCon (Coprod k) (Ok' k), -}Category k) => Cocartesian k where
  type Coprod k :: u -> u -> u
  inl :: Ok2 k a b => a `k` Coprod k a b
  inr :: Ok2 k a b => b `k` Coprod k a b
  infixr 2 |||
  (|||) :: forall a c d. Ok3 k a c d
        => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a)

class FunctorC f src trg => CocartesianFunctor f src trg where
  coprodToCoprod :: Dict ((f %% Coprod src a b) ~ Coprod trg (f %% a) (f %% b))

class (Category k, Ok k (Unit k)) => Terminal k where
  type Unit k :: u
  it :: Ok k a => a `k` Unit k

--     • Illegal constraint ‘Ok k (Unit k)’ in a superclass context
--         (Use UndecidableInstances to permit this)

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
