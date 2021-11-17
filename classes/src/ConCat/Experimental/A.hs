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

-- | Experiment with polykinded category theory functors

module ConCat.Experimental.PCat where

import Prelude hiding (id,(.),zipWith,curry,uncurry)
import qualified Prelude as P

import Data.Kind (Type,Constraint)
-- import GHC.Generics (U1(..),(:*:)(..),(:+:)(..),(:.:)(..))
-- import Control.Applicative (liftA2,liftA3)
-- import Control.Monad ((<=<))
-- import Control.Arrow (arr,Kleisli(..))
-- import qualified Control.Arrow as A
-- import Control.Monad.State (State,modify,put,get,execState,StateT,evalStateT)

import Data.Constraint (Dict(..),(:-)(..),refl,trans,(\\))
-- import Control.Newtype.Generics
-- import Data.Pointed
-- import Data.Key
-- import Data.IntMap ()

import ConCat.Misc (Yes1,type (&+&),inNew,inNew2,oops,type (+->)(..))
-- import ConCat.Free.VectorSpace
-- import ConCat.Free.LinearRow (lapplyL,OkLF,idL,compL,exlL,exrL,forkL,inlL,inrL,joinL,HasL(..))
-- import ConCat.Rep
-- import ConCat.Orphans

--------------------------------------------------
-- * Constraints


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
-- type Ok4 k a b c d     = C4 (Ok k) a b c d
-- type Ok5 k a b c d e   = C5 (Ok k) a b c d e
-- type Ok6 k a b c d e f = C6 (Ok k) a b c d e f

#endif


infixr 3 &&
class    (a,b) => a && b
instance (a,b) => a && b

--     • Potential superclass cycle for ‘&&’
--         one of whose superclass constraints is headed by a type variable:
--           ‘a’
--       Use UndecidableSuperClasses to accept this

class OpCon op con where
  inOp :: forall a b. con a && con b |- con (a `op` b)

infixr 1 |-
type (|-) = (:-)

infixl 1 <+
(<+) :: (b => r) -> (a |- b) -> (a => r)
r <+ Sub Dict = r
{-# INLINE (<+) #-}
-- (<+) = (\\)

--------------------------------------------------
-- * Categories


-- type family Obj (k :: u -> u -> Type) :: u

class Category (k :: u -> u -> Type) where
  -- type Obj k
  -- type Ok k :: Obj k -> Constraint
  type Ok k :: u -> Constraint
  type Ok k = Yes1
  id  :: Ok k a => a `k` a
  infixr 9 .
  (.) :: forall b c a. Ok3 k a b c => (b `k` c) -> (a `k` b) -> (a `k` c)
  -- (.) :: forall b c a. (Ok k a, Ok k b, Ok k c) => (b `k` c) -> (a `k` b) -> (a `k` c)

-- • Type constructor ‘Obj’ cannot be used here
--     (it is defined and used in the same recursive group)
-- • In the kind ‘Obj k -> Constraint’

-- foo :: P Constraint (Type -> Type)
-- foo = undefined

-- | Category with product.
class ({- OkProd k, -} Category k) => Cartesian k where
  type Prod k :: u -> u -> u
  exl :: Ok2 k a b => Prod k a b `k` a
  exr :: Ok2 k a b => Prod k a b `k` b
  (&&&) :: forall a c d. Ok3 k a c d => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)
  -- exl :: (Ok k a, Ok k b) => Prod k a b `k` a
  -- exr :: (Ok k a, Ok k b) => Prod k a b `k` b
  -- (&&&) :: forall a c d. (Ok k a, Ok k c, Ok k d) => (a `k` c) -> (a `k ` d) -> (a `k` Prod k c d)

--------------------------------------------------
-- * Constructions


-- I don't think GHC 8 can promote this P to a new kind.
data P (a :: u) (b :: v)

type family Fst t where Fst (P a b) = a
type family Snd t where Snd (P a b) = b

-- Product of categories
infixl 1 :**:
data (p :**: q) a b = p (Fst a) (Fst b) :**: q (Snd a) (Snd b)

class    (Ok k (Fst ab), Ok k' (Snd ab)) => OkProd k k' ab
instance (Ok k (Fst ab), Ok k' (Snd ab)) => OkProd k k' ab

instance (Category k, Category k') => Category (k :**: k') where
  type Ok (k :**: k') = OkProd k k'
  id = id :**: id
  (g :**: g') . (f :**: f') = (g . f) :**: (g' . f')

-- data ProdProd (k :: u -> u -> Type) (k' :: v -> v -> Type) ab cd =
--   P (Prod k (Fst ab) (Fst cd)) (Prod k' (Snd ab) (Snd cd))

-- Prod (k :* k') (a,b) (a',b') = Prod k a c :* Prod k' a' b'

instance (Cartesian k, Cartesian k') => Cartesian (k :**: k') where
  type Prod (k :**: k') = ProdProd k k'
  exl = exl :**: exl

exl :: (k :**: k') (Prod (k :**: k') ab cd) ab
    :: (k :**: k') (Prod k (Fst ab) (Fst cd) :* Prod k' (Snd ab) (Snd cd)) ab


-- instance (Cartesian k, Cartesian k') => Cartesian (k :**: k') where
--   type Prod (k :**: k') ab cd = P (Prod k (Fst ab) (Fst cd)) (Prod k' (Snd ab) (Snd cd))
--   exl = exl :**: exl

-- instance (Cartesian k, Cartesian k') => Cartesian (k :**: k') where
--   type Prod (k :**: k') ab cd = P (Prod k (Fst ab) (Fst cd)) (Prod k' (Snd ab) (Snd cd))
--   exl = exl :**: exl

-- Type family equation violates injectivity annotation.
-- Type variables ‘ab’, ‘cd’
-- cannot be inferred from the right-hand side.
-- In the type family equation:
--   forall {k} {k1} {k' :: k -> k -> *} {k2 :: k1
--                                              -> k1 -> *} {cd} {ab}.
--     Prod (k2 :**: k') ab cd = P (Prod k2 (Fst ab) (Fst cd))
--                                 (Prod k' (Snd ab) (Snd cd))
