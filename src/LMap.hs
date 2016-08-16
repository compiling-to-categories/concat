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

import Data.Constraint (Dict(..),(:-)(..))

import Data.MemoTrie      (HasTrie(..),(:->:))

import Misc ((:*))
import ConCat
import Additive
import Semimodule
import Basis

class    (Mod s u, HasBasis u, HasTrie (Basis u)) => OkL s u
instance (Mod s u, HasBasis u, HasTrie (Basis u)) => OkL s u

type LMap' u v = Basis u :->: v

-- | Linear map, represented as an optional memo-trie from basis to
-- values
data LMap s u v = (OkL s u, OkL s v) => LMap { unLMap :: LMap' u v }

inLMap :: (OkL s c, OkL s d) =>
          (LMap' a b -> LMap' c d) -> (LMap s a b -> LMap s c d)
inLMap h (LMap ab) = LMap (h ab)

inLMap2 :: (OkL s e, OkL s f) =>
           (LMap' a b -> LMap' c d -> LMap' e f)
        -> (LMap s a b -> LMap s c d -> LMap s e f)
inLMap2 h (LMap ab) (LMap cd) = LMap (h ab cd)

-- | Function (assumed linear) as linear map. Only sampled on basis.
linear :: (OkL s u, OkL s v) => (u -> v) -> LMap s u v
linear f = LMap (trie (f . basisValue))

-- | Apply a linear map to a vector.
lapply :: (OkL s u, OkL s v) => LMap s u v -> (u -> v)
lapply (LMap tr) = linearCombo . map (first (untrie tr)) . decompose

instance (OkL s u, OkL s v) => Additive (LMap s u v) where
  zero  = linear zero
  (^+^) = inLMap2 (^+^)

instance (OkL s u, OkL s v) => Semimodule (LMap s u v) where
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
  (.) = inLMap . fmap . lapply

instance OpCon (:*) (OkL s) where
  inOp = Sub Dict
  -- exProd = Sub Dict

instance ProductCat (LMap s) where
  type Prod (LMap s) = (:*)
  exl   = linear exl
  exr   = linear exr
  (&&&) = inLMap2 (liftA2 (,))

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
  f ||| g = linear (joinF (lapply f) (lapply g))

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
