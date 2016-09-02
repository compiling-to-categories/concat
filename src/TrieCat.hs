{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Tries as category

module TrieCat where

import Prelude hiding (id,(.))
import Data.Constraint (Dict(..),(:-)(..))
import Control.Newtype
import Data.MemoTrie

import Misc
import ConCat

infixr 9 -->
newtype a --> b = Memod (a :->: b)

class HasTrie a => OkM a
instance HasTrie a => OkM a

-- Using OkM in place of HasTrie saves us orphan instances
-- for OpCon (:*) HasTrie and OpCon (:+) HasTrie

instance Newtype (a --> b) where
  type O (a --> b) = a :->: b
  unpack (Memod t) = t
  pack t = Memod t

instance Category (-->) where
  type Ok (-->) = OkM
  id  = pack idTrie
  (.) = (inNew2.inTrie2) (.)

instance OpCon (:*) OkM where inOp = Sub Dict
instance OpCon (:+) OkM where inOp = Sub Dict

instance ProductCat (-->) where
  exl   = (pack.trie) exl
  exr   = (pack.trie) exr
  (&&&) = (inNew2.inTrie2) (&&&)

instance CoproductCat (-->) where
  inl   = (pack.trie) inl
  inr   = (pack.trie) inr
  (|||) = (inNew2.inTrie2) (|||)
