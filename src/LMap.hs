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
{-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

-- | Linear maps as constrained category

module LMap where

import Prelude hiding (id,(.))

import Data.Constraint

import Data.MemoTrie      (HasTrie(..),(:->:))
import Data.AdditiveGroup (Sum(..), AdditiveGroup(..))

import ConCat
import Module
import Basis

class    (Module u, Scalar u ~ s, HasBasis u, HasTrie (Basis u)) => OkL s u
instance (Module u, Scalar u ~ s, HasBasis u, HasTrie (Basis u)) => OkL s u

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

-- | Function (assumed linear) as linear map.
linear :: (OkL s u, OkL s v) => (u -> v) -> LMap s u v
linear f = LMap (trie (f . basisValue))

-- | Apply a linear map to a vector.
lapply :: (OkL s u, OkL s v) => LMap s u v -> (u -> v)
lapply (LMap tr) = linearCombo . fmap (first (untrie tr)) . decompose

instance (OkL s u, OkL s v) => AdditiveGroup (LMap s u v) where
  zeroV   = linear (const zeroV)
  (^+^)   = inLMap2 (^+^)
  negateV = inLMap negateV

instance (OkL s u, OkL s v) => Module (LMap s u v) where
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

--   vw . LMap uv = LMap (lapply vw <$> uv)
--
--   (.) vw = inLMap (fmap (lapply vw))
