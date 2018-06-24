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
data Ops :: (* -> * -> *) -> (* -> * -> *) where
  Nil  :: Ok  k a => Ops k a a
  (:<) :: Ok3 k a b c => a `k` b -> Ops k b c -> Ops k a c

evalOps :: Category k => Ops k a b -> a `k` b
evalOps Nil          = id
evalOps (op :< rest) = evalOps rest . op

pureOps :: Ok2 k a b => a `k` b -> Ops k a b
pureOps f = f :< Nil

instance Show2 k => Show (Ops k a b) where
  show = show . exops

exops :: Ops k a b -> [Exists2 k]
exops Nil = []
exops (op :< ops) = Exists2 op : exops ops

instance Category (Ops k) where
  type Ok (Ops k) = Ok k
  id  = Nil
  (.) = flip (++*)

infixr 5 ++*
(++*) :: Ok3 k a b c => Ops k a b -> Ops k b c -> Ops k a c
(++*) Nil ops          = ops
(++*) (op :< ops) ops' = op :< (ops ++* ops')

instance AssociativePCat k => AssociativePCat (Ops k) where
  lassocP :: forall a b c. Ok3 k a b c => Ops k (a :* (b :* c)) ((a :* b) :* c)
  lassocP = pureOps lassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  rassocP :: forall a b c. Ok3 k a b c => Ops k ((a :* b) :* c) (a :* (b :* c))
  rassocP = pureOps rassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b

instance MBraidedPCat k => MonoidalPCat (Ops k) where
  first :: forall a b c. Ok3 k a b c => Ops k a c -> Ops k (a :* b) (c :* b)
  first Nil = Nil <+ okProd @k @a @b
  first (op :< ops) = firstCons op ops
   where
     firstCons :: forall x. Ok k x => (a `k` x) -> Ops k x c -> Ops k (a :* b) (c :* b)
     firstCons f fs = first f :< first fs
       <+ okProd @k @a @b <+ okProd @k @c @b <+ okProd @k @x @b
  second = secondFirst
  (***) = crossSecondFirst

instance BraidedPCat k => BraidedPCat (Ops k) where
  swapP :: forall a b. Ok2 k a b => Ops k (a :* b) (b :* a)
  swapP = swapP :< Nil
    <+ okProd @k @a @b <+ okProd @k @b @a

instance ProductCat k => ProductCat (Ops k) where
  exl :: forall a b. Ok2 k a b => Ops k (a :* b) a
  exr :: forall a b. Ok2 k a b => Ops k (a :* b) b
  dup :: forall a  . Ok  k a   => Ops k a (a :* a)
  exl = pureOps exl <+ okProd @k @a @b
  exr = pureOps exr <+ okProd @k @a @b
  dup = pureOps dup <+ okProd @k @a @a

instance TerminalCat k => TerminalCat (Ops k) where
  it = pureOps it

instance (BraidedPCat k, MProductCat k, TerminalCat k) => UnitCat (Ops k)
  
instance (OkProd k, NumCat k a) => NumCat (Ops k) a where
  negateC = pureOps negateC
  addC  = pureOps addC  <+ okProd @k @a @a
  subC  = pureOps subC  <+ okProd @k @a @a
  mulC  = pureOps mulC  <+ okProd @k @a @a
  powIC = pureOps powIC <+ okProd @k @a @Int

-- TODO: Many more instances

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

data Exists2 k = forall a b. Exists2 (a `k` b)

instance Show2 k => Show (Exists2 k) where show (Exists2 f) = show2 f
