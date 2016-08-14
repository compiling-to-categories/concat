{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ExistentialQuantification #-}
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

class    (Ring u, HasBasis u, HasTrie (Basis u)) => OkL u
instance (Ring u, HasBasis u, HasTrie (Basis u)) => OkL u

type LMap' u v = Basis u :->: v

-- | Linear map, represented as an optional memo-trie from basis to
-- values
data u :-* v = (OkL u, OkL v) => LMap { unLMap :: LMap' u v }

inLMap :: (OkL t, OkL u) =>
          (LMap' r s -> LMap' t u) -> ((r :-* s) -> (t :-* u))
inLMap = unLMap ~> LMap

-- The OkL constraints on u & v allow okay to work.

inLMap2 :: (OkL v, OkL w) =>
           (LMap' r s -> LMap' t u -> LMap' v w)
        -> ((r :-* s) -> (t :-* u) -> (v :-* w))
inLMap2 = unLMap ~> inLMap

inLMap3 :: (OkL x, OkL y) =>
           (LMap' r s -> LMap' t u -> LMap' v w -> LMap' x y)
        -> ((r :-* s) -> (t :-* u) -> (v :-* w) -> (x :-* y))
inLMap3 = unLMap ~> inLMap2

-- deriving instance (HasTrie (Basis u), AdditiveGroup v) => AdditiveGroup (u :-* v)

-- instance (HasTrie (Basis u), OkL v) =>
--          OkL (u :-* v) where
--   type Scalar (u :-* v) = Scalar v
--   (*^) s = fmap (s *^)

-- | Function (assumed linear) as linear map.
linear :: (OkL u, OkL v) => (u -> v) -> (u :-* v)
linear f = LMap (trie (f . basisValue))

-- | Apply a linear map to a vector.
lapply :: (OkL u, OkL v, Scalar u ~ Scalar v) =>
          (u :-* v) -> (u -> v)
lapply (LMap tr) = linearCombo . fmap (first (untrie tr)) . decompose

-- | Compose linear maps
(*.*) :: (OkL v, OkL w, Functor ((:-*) u), Scalar v ~ Scalar w) =>
         (v :-* w) -> (u :-* v) -> (u :-* w)
(*.*) vw = fmap (lapply vw)


{--------------------------------------------------------------------
    Category instances
--------------------------------------------------------------------}

#define OKAY OD Dict
#define OKAY2 (OKAY,OKAY)

instance Category (:-*) where
  type Ok (:-*) = OkL
  okay (LMap _) = OKAY2
  id = linear id   
--   (.) = inLMap2 (*.*)
  -- LMap g . LMap f = LMap (g *.* f)
