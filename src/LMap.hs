{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

-- | Linear maps as constrained category

module LMap where

import Prelude hiding (id,(.))
import Control.Applicative (liftA2)

import Control.Newtype (Newtype(..))
import Data.Constraint (Dict(..),(:-)(..))
import Data.MemoTrie      (HasTrie(..),(:->:))

import Misc ((:*),inNew,inNew2)
import ConCat
import Additive
import Semimodule
import Basis

class    (Mod s u, HasBasis u, HasTrie (Basis u)) => OkL s u
instance (Mod s u, HasBasis u, HasTrie (Basis u)) => OkL s u

type OkL2 s u v = (OkL s u, OkL s v)

type LMap' u v = Basis u :->: v

-- | Linear map, represented as a memo-trie from basis to values
data LMap s u v = OkL2 s u v => LMap { unLMap :: LMap' u v }

instance OkL2 s u v => Newtype (LMap s u v) where
  type O (LMap s u v) = LMap' u v
  pack = LMap
  unpack = unLMap

-- | Function (assumed linear) as linear map. Only sampled on basis.
linear :: OkL2 s u v => (u -> v) -> LMap s u v
linear f = LMap (trie (f . basisValue))

-- | Apply a linear map to a vector.
lapply :: OkL2 s u v => LMap s u v -> (u -> v)
lapply (LMap tr) = linearCombo . map (first (untrie tr)) . decompose

($@) :: OkL2 s a b => LMap s a b -> a -> b
($@) = lapply

instance OkL2 s u v => Additive (LMap s u v) where
  zero  = linear zero
  (^+^) = inNew2 (^+^)

instance OkL2 s u v => Semimodule (LMap s u v) where
  type Scalar (LMap s u v) = Scalar v
  s *^ m = m . scaleL s

scaleL :: OkL s u => s -> LMap s u u
scaleL = linear . (*^)

{--------------------------------------------------------------------
    Category instances
--------------------------------------------------------------------}

instance Category (LMap s) where
  type Ok (LMap s) = OkL s
  id  = linear id   
  (.) = inNew . fmap . lapply

instance OpCon (:*) (OkL s) where
  inOp = Sub Dict
  -- exProd = Sub Dict

instance ProductCat (LMap s) where
  type Prod (LMap s) = (:*)
  exl   = linear exl
  exr   = linear exr
  (&&&) = inNew2 (liftA2 (,))

--   f &&& g = linear (lapply f &&& lapply g)

-- The instance comes from the following homomorphic specification:
-- 
--   lapply exl      == exl
--   lapply exr      == exr
--   lapply (f &&& g) == lapply f &&& lapply g

instance CoproductCat (LMap s) where
  type Coprod (LMap s) = (:*)  -- direct sum
  inl = linear (, zero)
  inr = linear (zero ,)
  f ||| g = linear (lapply f `joinF` lapply g)

joinF :: Additive c => (a -> c) -> (b -> c) -> (a :* b -> c)
(f `joinF` g) (a,b) = f a ^+^ g b

-- This implementation comes easily from solving the following homomorphisms:
-- 
--   lapply inl = (, zero)
--   lapply inr = (zero ,)
--   lapply (f ||| g) = lapply f `joinF` lapply g
-- 
-- TODO: more efficient (|||)

-- TODO: consider more efficient implementations of the defaulted methods for
-- ProductCat and CoproductCat.
