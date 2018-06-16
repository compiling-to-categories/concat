{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Stack machine category / compiler 

module ConCat.StackMachine where

import Prelude hiding (id,(.),curry,uncurry)

import Data.List (intercalate)

import Control.Newtype.Generics (Newtype(..))

import ConCat.Misc ((:*),(:+))
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Syntactic (Syn)
import ConCat.Ops (Ops)

{--------------------------------------------------------------------
    Stack machines
--------------------------------------------------------------------}

newtype Stack k a b =
  Stack { unStack :: forall z. Ok k z => (a :* z) `k` (b :* z) }

-- | The semantic functor that specifies 'SM'.
pureSM :: (MonoidalPCat k, Ok2 k a b) => (a `k` b) -> Stack k a b
pureSM f = Stack (first f)

evalSM :: forall k a b. (Category k, UnitCat k, OkProd k, Ok2 k a b)
       => Stack k a b -> (a `k` b)
evalSM (Stack f) = rcounit . f . runit
                <+ okProd @k @a @()
                <+ okProd @k @b @()

-- TODO: Specify and derive the following instances by saying that pureSM is a
-- homomorphism for the classes involved.

instance MonoidalPCat k => Category (Stack k) where
  type Ok (Stack k) = Ok k
  id = pureSM id
  -- Stack g . Stack f = Stack (g . f)
  (.) :: forall a b c. Ok3 k a b c => Stack k b c -> Stack k a b -> Stack k a c
  Stack g . Stack f = Stack h
   where
     h :: forall z. Ok k z => (a :* z) `k` (c :* z)
     h = g . f
       <+ okProd @k @a @z
       <+ okProd @k @b @z
       <+ okProd @k @c @z

instance BraidedPCat k => MonoidalPCat (Stack k) where
  first :: forall a b c. Ok3 k a b c => Stack k a c -> Stack k (a :* b) (c :* b)
  first (Stack f) = Stack h
   where
     h :: forall z. Ok k z => ((a :* b) :* z) `k` ((c :* b) :* z)
     h = inRassocP f <+ okProd @k @b @z   -- h = lassocP . f . rassocP
  second = secondFirst  -- relies on BraidedPCat
  (***) = crossSecondFirst  -- f *** g = swap . first g . swap . first f
  lassocP :: forall a b c. Ok3 k a b c => Stack k (a :* (b :* c)) ((a :* b) :* c)
  lassocP = pureSM lassocP
            <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
            <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  rassocP :: forall a b c. Ok3 k a b c => Stack k ((a :* b) :* c) (a :* (b :* c))
  rassocP = pureSM rassocP
            <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
            <+ okProd @k @(a :* b) @c <+ okProd @k @a @b

#if 0

f :: a -> b
g :: c -> d

rassocP    :: ((a :* b) :* z) -> (a :* (b :* z))
first f    :: (a :* (b :* z)) -> (c :* (b :* z))
lassocP    :: (c :* (b :* z)) -> ((c :* b) :* z)
first swap :: ((c :* b) :* z) -> (b :* (c :* z))
first g    :: (b :* (c :* z)) -> (d :* (c :* z))
rassocP    :: (d :* (c :* z)) -> ((d :* c) :* z)
first swap :: ((d :* c) :* z) -> ((c :* d) :* z)

#endif

instance BraidedPCat k => BraidedPCat (Stack k) where
  swapP :: forall a b. Ok2 k a b => Stack k (a :* b) (b :* a)
  swapP = pureSM swapP
        <+ okProd @k @a @b
        <+ okProd @k @b @a

instance ProductCat k => ProductCat (Stack k) where
  exl :: forall a b. Ok2 k a b => Stack k (a :* b) a
  exr :: forall a b. Ok2 k a b => Stack k (a :* b) b
  dup :: forall a  . Ok  k a   => Stack k a (a :* a)
  exl = pureSM exl <+ okProd @k @a @b
  exr = pureSM exr <+ okProd @k @a @b
  dup = pureSM dup <+ okProd @k @a @a

instance (MonoidalPCat k, TerminalCat k) => TerminalCat (Stack k) where
  it = pureSM it

instance (ProductCat k, TerminalCat k, OkUnit k) => UnitCat (Stack k)

-- instance (MonoidalPCat k, UnitCat k) => UnitCat (Stack k) where
--   lunit :: forall a. Ok k a => Stack k a (() :* a)
--   lunit = pureSM lunit <+ okProd @k @() @a
--   runit :: forall a. Ok k a => Stack k a (a :* ())
--   runit = pureSM runit <+ okProd @k @a @()
--   lcounit :: forall a. Ok k a => Stack k (() :* a) a
--   lcounit = pureSM lcounit <+ okProd @k @() @a
--   rcounit :: forall a. Ok k a => Stack k (a :* ()) a
--   rcounit = pureSM rcounit <+ okProd @k @a @()

instance DistribCat k => MonoidalSCat (Stack k) where
  -- Stack f +++ Stack g = Stack (inDistr (f +++ g))
  (+++) :: forall a b c d. Ok4 k a b c d => Stack k a c -> Stack k b d -> Stack k (a :+ b) (c :+ d)
  Stack f +++ Stack g = Stack h
   where
     h :: forall z. Ok k z => ((a :+ b) :* z) `k` ((c :+ d) :* z)
     h = inDistr (f +++ g)
         <+ okProd @k @a @z <+ okProd @k @b @z
         <+ okProd @k @c @z <+ okProd @k @d @z

-- The validity of this (+++) definition relies on the following fact:
-- 
--   first (f +++ g) = inDistr (first f +++ first g)
-- 
-- See proof in 2018-06-11 notes.

instance (BraidedSCat k, DistribCat k) => BraidedSCat (Stack k) where
  swapS :: forall a b. Ok2 k a b => Stack k (a :+ b) (b :+ a)
  swapS = pureSM swapS
        <+ okCoprod @k @a @b
        <+ okCoprod @k @b @a

instance DistribCat k => CoproductCat (Stack k) where
  inl :: forall a b. Ok2 k a b => Stack k a (a :+ b)
  inr :: forall a b. Ok2 k a b => Stack k b (a :+ b)
  jam :: forall a. Ok k a => Stack k (a :+ a) a
  inl = pureSM inl <+ okCoprod @k @a @b
  inr = pureSM inr <+ okCoprod @k @a @b
  jam = pureSM jam <+ okCoprod @k @a @a

instance (MonoidalPCat k, NumCat k a) => NumCat (Stack k) a where
  negateC :: Ok k a => Stack k a a
  addC,subC,mulC :: Ok k a => Stack k (a :* a) a
  powIC :: Ok2 k a Int => Stack k (a :* Int) a
  negateC = pureSM negateC
  addC    = pureSM addC  <+ okProd @k @a @a
  subC    = pureSM subC  <+ okProd @k @a @a
  mulC    = pureSM mulC  <+ okProd @k @a @a
  powIC   = pureSM powIC <+ okProd @k @a @Int

-- To do: write a GHC type-checker plugin that automatically applies `okProd`
-- and `okCoprod` entailments. Probably wait until the spurious recompilation
-- issue is fixed and I'm on a current GHC.

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

#if 1

t1 :: forall k. (ProductCat k, NumCat k Int) => Int `k` Int
t1 = addC . dup <+ okProd @k @Int @Int

t2 :: (ProductCat k, UnitCat k, NumCat k Int) => Int `k` Int
t2 = evalSM t1

t3 :: Int -> Int
t3 = t2

t4 :: Int
t4 = t3 17

t5 :: Syn Int Int
t5 = t2

t6 :: Syn (Int :* z) (Int :* z)
t6 = unStack t1

t7 :: Syn (Int :* Int) (Int :* Int)
t7 = negateC *** negateC

t8 :: Syn (Int :* Int) (Int :* Int)
t8 = evalSM (negateC *** negateC)

t9 :: Syn ((Int :* Int) :* z) ((Int :* Int) :* z)
t9 = unStack (negateC *** negateC)

t10 :: Syn ((Int :* Int) :* z) (Int :* z)
t10 = unStack (addC . (negateC *** negateC))

t11 :: Syn (Int :* z) (Int :* z)
t11 = unStack (addC . (negateC *** negateC) . dup)

t12 :: Syn (Int :* z) (Int :* z)
t12 = unStack (addC . (negateC &&& negateC))

-- unStack @Syn (addC . (negateC &&& negateC))

t13 :: Ops Syn (Int :* z) (Int :* z)
t13 = unStack (addC . (negateC &&& negateC))

#endif
