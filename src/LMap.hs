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
{-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

-- | Linear maps as constrained category

module LMap where

import Prelude hiding (id,(.))

import Data.Constraint

import Data.MemoTrie      (HasTrie(..),(:->:))
import Data.AdditiveGroup (Sum(..), AdditiveGroup(..))

import ConCat
import Ring
import Basis

class    (Ring u, Scalar u ~ s, HasBasis u, HasTrie (Basis u)) => OkL s u
instance (Ring u, Scalar u ~ s, HasBasis u, HasTrie (Basis u)) => OkL s u

type LMap' u v = Basis u :->: v

-- | Linear map, represented as an optional memo-trie from basis to
-- values
data LMap s u v = (OkL s u, OkL s v) => LMap { unLMap :: LMap' u v }

inLMap :: (OkL s c, OkL s d) =>
          (LMap' a b -> LMap' c d) -> (LMap s a b -> LMap s c d)
inLMap h (LMap ab) = LMap (h ab)

-- scale1 :: LMap s s s
-- scale1 = LMap (trie id)

-- The OkL constraints on u & v allow okay to work.

-- deriving instance (HasTrie (Basis u), AdditiveGroup v) => AdditiveGroup (u :-* v)

-- instance (HasTrie (Basis u), OkL v) =>
--          OkL (u :-* v) where
--   type Scalar (u :-* v) = Scalar v
--   (*^) s = fmap (s *^)

-- | Function (assumed linear) as linear map.
linear :: (OkL s u, OkL s v) => (u -> v) -> LMap s u v
linear f = LMap (trie (f . basisValue))

-- | Apply a linear map to a vector.
lapply :: (OkL s u, OkL s v) =>
          LMap s u v -> (u -> v)
lapply (LMap tr) = linearCombo . fmap (first (untrie tr)) . decompose

{--------------------------------------------------------------------
    Category instances
--------------------------------------------------------------------}

instance Category (LMap s) where
  type Ok (LMap s) = OkL s
  id  = linear id   
  (.) = inLMap . fmap . lapply

-- Alternatively,
-- 
--   vw . LMap uv = LMap (lapply vw <$> uv)
--
--   (.) vw = inLMap (fmap (lapply vw))
