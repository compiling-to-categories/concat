{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Stack machine category / compiler 

module ConCat.StackMachine where

import Prelude hiding (id,(.),curry,uncurry)

import Control.Newtype.Generics (Newtype(..))

import ConCat.Misc ((:*),(:+))
import qualified ConCat.Category as C
import ConCat.AltCat

newtype SM k a b = SM (forall z. Ok k z => (a :* z) `k` (b :* z))

pureSM :: (MonoidalPCat k, Ok2 k a b) => (a `k` b) -> SM k a b
pureSM f = SM (first f)

evalSM :: forall k a b. (ProductCat k, TerminalCat k, Ok2 k a b)
       => SM k a b -> (a `k` b)
evalSM (SM f) = exl . f . runit
                <+ okProd @k @a @()
                <+ okProd @k @b @()

-- TODO: Specify and derive the following instances by saying that pureSM or
-- evalSM is a homomorphism for the classes involved.

instance MonoidalPCat k => Category (SM k) where
  type Ok (SM k) = Ok k
  id = pureSM id
  -- SM g . SM f = SM (g . f)
  (.) :: forall a b c. Ok3 k a b c => SM k b c -> SM k a b -> SM k a c
  SM g . SM f = SM h
   where
     h :: forall z. Ok k z => (a :* z) `k` (c :* z)
     h = g . f
       <+ okProd @k @a @z
       <+ okProd @k @b @z
       <+ okProd @k @c @z

instance ProductCat k => MonoidalPCat (SM k) where
  first :: forall a b c. Ok3 k a b c => SM k a c -> SM k (a :* b) (c :* b)
  -- first (SM f) = SM (first f)
  --   <+ okProd @k @a @b
  --   <+ okProd @k @c @b
  first (SM f) = SM h
   where
     h :: forall z. Ok k z => ((a :* b) :* z) `k` ((c :* b) :* z)
     h = inRassocP f <+ okProd @k @b @z
  second = secondFirst
  (***) = crossSecondFirst

instance ProductCat k => ProductCat (SM k) where
  exl :: forall a b. Ok2 k a b => SM k (a :* b) a
  exr :: forall a b. Ok2 k a b => SM k (a :* b) b
  dup :: forall a  . Ok  k a   => SM k a (a :* a)
  exl = pureSM exl <+ okProd @k @a @b
  exr = pureSM exr <+ okProd @k @a @b
  dup = pureSM dup <+ okProd @k @a @a

instance DistribCat k => MonoidalSCat (SM k) where
  -- SM f +++ SM g = SM (indistr (f +++ g))
  (+++) :: forall a b c d. Ok4 k a b c d => SM k a c -> SM k b d -> SM k (a :+ b) (c :+ d)
  SM f +++ SM g = SM h
   where
     h :: forall z. Ok k z => ((a :+ b) :* z) `k` ((c :+ d) :* z)
     h = indistr (f +++ g)
         <+ okProd @k @a @z <+ okProd @k @b @z
         <+ okProd @k @c @z <+ okProd @k @d @z

-- The validity of this (+++) definition relies on the following fact:
-- 
--   first (f +++ g) = indistr (first f +++ first g)
-- 
-- See proof in 2018-06-11 notes.

instance DistribCat k => CoproductCat (SM k) where
  inl :: forall a b. Ok2 k a b => SM k a (a :+ b)
  inr :: forall a b. Ok2 k a b => SM k b (a :+ b)
  jam :: forall a. Ok k a => SM k (a :+ a) a
  inl = pureSM inl <+ okCoprod @k @a @b
  inr = pureSM inr <+ okCoprod @k @a @b
  jam = pureSM jam <+ okCoprod @k @a @a

instance (MonoidalPCat k, NumCat k a) => NumCat (SM k) a where
  negateC :: Ok k a => SM k a a
  addC,subC,mulC :: Ok k a => SM k (a :* a) a
  powIC :: Ok2 k a Int => SM k (a :* Int) a
  negateC = pureSM negateC
  addC    = pureSM addC  <+ okProd @k @a @a
  subC    = pureSM subC  <+ okProd @k @a @a
  mulC    = pureSM mulC  <+ okProd @k @a @a
  powIC   = pureSM powIC <+ okProd @k @a @Int

-- To do: write a GHC type-checker plugin that automatically applies `okProd`
-- and `okCoprod` entailments. Probably wait until the spurious recompilation
-- issue is fixed and I'm on a current GHC.


-- Stack operation
data Op :: (* -> * -> *) -> (* -> * -> *) where
  First  :: Ok3 k a b z => (a `k` b) -> Op k (a :* z) (b :* z)
  Rassoc :: Ok3 k a b z => Op k ((a :* b) :* z) (a :* (b :* z))
  Lassoc :: Ok3 k a b z => Op k (a :* (b :* z)) ((a :* b) :* z)

-- evalOp :: ProductCat k => Op k (a :* w) (b :* z) -> (a :* w) `k` (b :* z)
evalOp :: ProductCat k => Op k u v -> (u `k` v)
evalOp (First f) = first f
evalOp Rassoc    = rassocP
evalOp Lassoc    = lassocP

infixr 5 :<
data Ops :: (* -> * -> *) -> (* -> * -> *) where
  Nil  :: Ok  k a => Ops k a a
  (:<) :: Ok3 k a b c => Op k a b -> Ops k b c -> Ops k a c

evalOps :: ProductCat k => Ops k a b -> a `k` b
evalOps Nil          = id
evalOps (op :< rest) = evalOps rest . evalOp op

instance Category (Ops k) where
  type Ok (Ops k) = Ok k
  id  = Nil
  (.) = flip (++*)

infixr 5 ++*
(++*) :: Ok3 k a b c => Ops k a b -> Ops k b c -> Ops k a c
(++*) Nil ops          = ops
(++*) (op :< ops) ops' = op :< (ops ++* ops')

newtype SM' k a b = SM' (forall z. Ok k z => Ops k (a :* z) (b :* z))
  
evalSM' :: forall k a b. (ProductCat k, TerminalCat k, Ok2 k a b)
        => SM' k a b -> (a `k` b)
evalSM' (SM' f) = exl . evalOps f . runit
                  <+ okProd @k @a @()
                  <+ okProd @k @b @()

instance OkProd k => Category (SM' k) where
  type Ok (SM' k) = Ok k
  id :: forall a. Ok k a => SM' k a a 
  id = SM' id'
   where
     id' :: forall z. Ok k z => Ops k (a :* z) (a :* z)
     id' = id <+ okProd @k @a @z
  (.) :: forall a b c. Ok3 k a b c => SM' k b c -> SM' k a b -> SM' k a c
  SM' g . SM' f = SM' h
   where
     h :: forall z. Ok k z => Ops k (a :* z) (c :* z)
     h = g . f
       <+ okProd @k @a @z
       <+ okProd @k @b @z
       <+ okProd @k @c @z

pureSM' :: forall k a b. (OkProd k, Ok2 k a b) => (a `k` b) -> SM' k a b
pureSM' f = SM' ops
 where
   ops :: forall z. Ok k z => Ops k (a :* z) (b :* z)
   ops = First f :< Nil
         <+ okProd @k @a @z
         <+ okProd @k @b @z

instance ProductCat k => MonoidalPCat (SM' k) where
  first :: forall a b c. Ok3 k a b c => SM' k a c -> SM' k (a :* b) (c :* b)
  first (SM' ops) = SM' h
   where
     h :: forall z. Ok k z => Ops k ((a :* b) :* z) ((c :* b) :* z)
     h = Rassoc :< ops ++* Lassoc :< Nil
       <+ okProd @k @(c :* b) @z <+ okProd @k @c @b
       <+ okProd @k @c @(b :* z)
       <+ okProd @k @(a :* b) @z <+ okProd @k @a @b
       <+ okProd @k @a @(b :* z) <+ okProd @k @b @z
  second = secondFirst
  (***) = crossSecondFirst

instance ProductCat k => ProductCat (SM' k) where
  exl :: forall a b. Ok2 k a b => SM' k (a :* b) a
  exr :: forall a b. Ok2 k a b => SM' k (a :* b) b
  dup :: forall a  . Ok  k a   => SM' k a (a :* a)
  exl = pureSM' exl <+ okProd @k @a @b
  exr = pureSM' exr <+ okProd @k @a @b
  dup = pureSM' dup <+ okProd @k @a @a

-- TODO: refactor to eliminate the repetitive nature of SM vs SM'.

#if 0

SM' ops :: SM' k a c
ops :: forall z. Ok k z => Ops k (a :* z) (c :* z)

first (SM' ops) :: SM' k (a :* b) (c :* b)
SM' h           :: SM' k (a :* b) (c :* b)

h :: forall z. Ok k z => Ops k ((a :* b) :* z) ((c :* b) :* z)


first ops :: Ops k ((a :* z) :* b) ((c :* z) :* b)


rassocP . ops . lassocP :: Ops k (a :* (w :* z)) (b :* (w :* z))

first (SM' ops) :: SM' k (a :* w) (b :* w)

#endif


#if 0

-- | Stack machine
data Code :: (* -> * -> *) -> (* -> * -> *) where
  Nil  :: Ok  k a => Code k a a
  (:<) :: Ok3 k a b c => Op k a b -> Code k b c -> Code k a c

(++*) :: Ok3 k a b c => Code k a b -> Code k b c -> Code k a c
(++*) Nil ops = ops
(++*) (op :< ops) ops' = op :< (ops ++* ops')

data Op :: (* -> * -> *) -> (* -> * -> *) where
  Add    :: NumCat k a => Op k (a :* a) a
  Negate :: NumCat k a => Op k a a
  -- ...

evalCode :: Category k => Code k a b -> (a `k` b)
evalCode Nil = id
evalCode (op :< rest) = evalCode rest . evalOp op

evalOp :: Op k a b -> (a `k` b)
evalOp Add    = addC
evalOp Negate = negateC

instance Category (Code k) where
  type Ok (Code k) = Ok k
  id  = Nil
  (.) = flip (++*)

-- instance MonoidalPCat (Code k) where
--   (+++) = ...


{--------------------------------------------------------------------
    ...
--------------------------------------------------------------------}

evalOp :: Op a b -> forall z. a :* z -> b :* z
evalOp Add ((x,y),e) = (x+y,e)

newtype M a b = M (forall z. a :* z -> b :* z)

instance Category M where
  id = M id
  M g . M f = M (first g . first f)

instance Monoidal M where
  M f *** M g = ...

f :: forall z. a :* z -> c :* z
g :: forall z. b :* z -> d :* z

h :: forall z. (a :* b) :* z -> (c :* d) :* z
h ((a,b),z) = ...
 where
   f (a,(b,z))
   ...

#endif
