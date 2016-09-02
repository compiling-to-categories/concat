{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Tries as category

module TrieCat where

import Prelude hiding (id,(.))
import Data.Constraint (Dict(..),(:-)(..))
import Control.Newtype
import Data.MemoTrie

import Misc
import ConCat

{--------------------------------------------------------------------
    Memo trie functors
--------------------------------------------------------------------}

instance Category (:->:) where
  type Ok (:->:) = HasTrie
  id = idTrie
  (.) = (@.@)

instance OpCon (:*) HasTrie where inOp = Sub Dict
instance OpCon (:+) HasTrie where inOp = Sub Dict

instance ProductCat (:->:) where
  exl   = trie exl
  exr   = trie exr
  (&&&) = inTrie2 (&&&)

instance CoproductCat (:->:) where
  inl   = trie inl
  inr   = trie inr
  (|||) = inTrie2 (|||)

#if 1

instance OpCon (:->:) HasTrie where -- inOp = Sub Dict

instance ClosedCat (:->:) where
  type Exp (:->:) = (:->:)
  apply :: forall a b. Ok2 (:->:) a b => Exp (:->:) a b :* a :->: b
  apply = trie (apply . first untrie)
    <+ inOp @(Exp (:->:)) @(Ok (:->:)) @a @b
  curry = unpack
  uncurry = pack

  -- apply = (pack.trie) (\ (Memod t, a) -> untrie t a)

#endif
