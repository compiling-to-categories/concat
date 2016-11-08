{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}

-- TODO: trim extensions

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Linear maps for the blog post(s)

module ConCat.PostLinear where

import Prelude hiding (id,(.),curry,uncurry)
import qualified Prelude as P
import Control.Arrow (Kleisli(..),arr)
import qualified Control.Arrow as A
import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import qualified Control.Category as Cat
-- import Data.Constraint (Dict(..),(:-)(..))
import Control.Newtype
import GHC.Types (Constraint)
import Data.MemoTrie

import Data.VectorSpace
import Data.LinearMap
import Data.Basis

import Data.Constraint hiding ((&&&),(***),(:=>))
import qualified Data.Constraint as C

import ConCat.Misc hiding ((<~))
import ConCat.ConCat

class    (VectorSpace a, Scalar a ~ s, HasBasis a, HasTrie (Basis a)) => OkL s a
instance (VectorSpace a, Scalar a ~ s, HasBasis a, HasTrie (Basis a)) => OkL s a

-- | Linear map over a given scalar field
-- data LMap s a b = C2 (OkL s) a b => LMap (a :-* b)
data LMap (s :: *) a b = LMap (a :-* b)

-- Needs ExistentialQuantification

instance C2 (OkL s) a b => Newtype (LMap s a b) where
  type O (LMap s a b) = a :-* b
  pack t = LMap t
  unpack (LMap t) = t

instance Category (LMap s) where
  type Ok (LMap s) = OkL s
  id  = pack idL
  (.) = inNew2 (*.*)

instance OpCon (:*) (OkL s) where inOp = Sub Dict

-- exlL  :: ... => a :* b :-* a
-- exRL  :: ... => a :* b :-* b
-- forkL :: ... => (a :-* c) -> (a :-* d) -> (a :-* c :* d)

instance ProductCat (LMap s) where
  type Prod (LMap s) = (:*)
  exl   = pack exlL
  exr   = pack exrL
  (&&&) = inNew2 forkL

-- inlL  :: ... => a :-* a :* b
-- inrL  :: ... => b :-* a :* b
-- joinL :: ... => (a :-* c) -> (b :-* c) -> (a :* b :-* c)

instance CoproductCat (LMap s) where
  type Coprod (LMap s) = (:*)
  inl   = pack inlL
  inr   = pack inrL
  (|||) = inNew2 joinL
