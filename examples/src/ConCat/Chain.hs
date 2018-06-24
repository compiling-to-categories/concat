{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}

-- | Category of linear operation sequences

module ConCat.Chain where

import Prelude hiding (id,(.),curry,uncurry)

import ConCat.Misc ((:*))
import qualified ConCat.Category as C
import ConCat.AltCat

infixr 5 :<
data Chain :: (* -> * -> *) -> (* -> * -> *) where
  Nil  :: Ok  k a => Chain k a a
  (:<) :: Ok3 k a b c => a `k` b -> Chain k b c -> Chain k a c

evalChain :: Category k => Chain k a b -> a `k` b
evalChain Nil          = id
evalChain (op :< rest) = evalChain rest . op

pureChain :: Ok2 k a b => a `k` b -> Chain k a b
pureChain f = f :< Nil

instance Show2 k => Show (Chain k a b) where
  show = show . exops

exops :: Chain k a b -> [Exists2 k]
exops Nil = []
exops (op :< ops) = Exists2 op : exops ops

instance Category (Chain k) where
  type Ok (Chain k) = Ok k
  id  = Nil
  (.) = flip (++*)

infixr 5 ++*
(++*) :: Ok3 k a b c => Chain k a b -> Chain k b c -> Chain k a c
(++*) Nil ops          = ops
(++*) (op :< ops) ops' = op :< (ops ++* ops')

instance AssociativePCat k => AssociativePCat (Chain k) where
  lassocP :: forall a b c. Ok3 k a b c => Chain k (a :* (b :* c)) ((a :* b) :* c)
  lassocP = pureChain lassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  rassocP :: forall a b c. Ok3 k a b c => Chain k ((a :* b) :* c) (a :* (b :* c))
  rassocP = pureChain rassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b

instance MBraidedPCat k => MonoidalPCat (Chain k) where
  first :: forall a b c. Ok3 k a b c => Chain k a c -> Chain k (a :* b) (c :* b)
  first Nil = Nil <+ okProd @k @a @b
  first (op :< ops) = firstCons op ops
   where
     firstCons :: forall x. Ok k x => (a `k` x) -> Chain k x c -> Chain k (a :* b) (c :* b)
     firstCons f fs = first f :< first fs
       <+ okProd @k @a @b <+ okProd @k @c @b <+ okProd @k @x @b
  second = secondFirst
  (***) = crossSecondFirst

instance BraidedPCat k => BraidedPCat (Chain k) where
  swapP :: forall a b. Ok2 k a b => Chain k (a :* b) (b :* a)
  swapP = swapP :< Nil
    <+ okProd @k @a @b <+ okProd @k @b @a

instance ProductCat k => ProductCat (Chain k) where
  exl :: forall a b. Ok2 k a b => Chain k (a :* b) a
  exr :: forall a b. Ok2 k a b => Chain k (a :* b) b
  dup :: forall a  . Ok  k a   => Chain k a (a :* a)
  exl = pureChain exl <+ okProd @k @a @b
  exr = pureChain exr <+ okProd @k @a @b
  dup = pureChain dup <+ okProd @k @a @a

instance TerminalCat k => TerminalCat (Chain k) where
  it = pureChain it

instance (BraidedPCat k, MProductCat k, TerminalCat k) => UnitCat (Chain k)
  
instance (OkProd k, NumCat k a) => NumCat (Chain k) a where
  negateC = pureChain negateC
  addC  = pureChain addC  <+ okProd @k @a @a
  subC  = pureChain subC  <+ okProd @k @a @a
  mulC  = pureChain mulC  <+ okProd @k @a @a
  powIC = pureChain powIC <+ okProd @k @a @Int

-- TODO: Many more instances

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

data Exists2 k = forall a b. Exists2 (a `k` b)

instance Show2 k => Show (Exists2 k) where show (Exists2 f) = show2 f
