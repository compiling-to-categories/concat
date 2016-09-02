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

infixr 0 -->
newtype a --> b = Memod (a :->: b)

#if 1
class HasTrie a => OkM a
instance HasTrie a => OkM a
#else
type OkM = HasTrie
#endif

-- Using OkM in place of HasTrie avoids orphan instances for
-- OpCon (:*) HasTrie and OpCon (:+) HasTrie.

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

#if 0

instance OpCon (-->) OkM where inOp = Sub Dict

instance ClosedCat (-->) where
  type Exp (-->) = (-->)
  apply :: forall a b. Ok2 (-->) a b => Exp (-->) a b :* a --> b
  apply = (pack.trie) (apply . first (untrie.unpack))
    <+ inOp @(Exp (-->)) @(Ok (-->)) @a @b
  curry = pack . fmap pack . unpack . unpack
  uncurry = pack . pack . fmap unpack . unpack

  -- apply = (pack.trie) (\ (Memod t, a) -> untrie t a)

#if 0
first (untrie . unpack) :: (a --> b) :* a -> (a -> b) :* a
apply                   :: ''             -> (a --> b) :* a -> b

unpack    :: (a :* b --> c) -> (a :* b :->: c)
unpack    :: ''             -> (a :->: b :->: x)
fmap pack :: ''             -> (a :->: b --> x)
pack      :: ''             -> (a --> b --> x)
#endif

#endif
