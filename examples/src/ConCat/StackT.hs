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

#define EXAMPLES

-- | Stack machine category / compiler 

module ConCat.StackT where

import Prelude hiding (id,(.),curry,uncurry)

import ConCat.Misc ((:*),(:+))
import qualified ConCat.Category as C
import ConCat.AltCat

#ifdef EXAMPLES
import ConCat.Syntactic (Syn)
import ConCat.Chain (Chain)
#endif

{--------------------------------------------------------------------
    Stack machines
--------------------------------------------------------------------}

data Stack k a b =
  Stack { unStack :: forall z. Ok k z => (a :* z) `k` (b :* z) }

-- unStack' :: Ok k () => Stack k a b -> ((a :* ()) `k` (b :* ()))
-- unStack' = unStack

-- | The semantic functor that specifies 'Stack'.
stack :: (MonoidalPCat k, Ok2 k a b) => (a `k` b) -> Stack k a b
stack f = Stack (first f)
{-# INLINE stack #-}

evalSM :: forall k a b. (Category k, UnitCat k, OkProd k, Ok2 k a b)
       => Stack k a b -> (a `k` b)
evalSM (Stack f) = rcounit . f . runit
                 <+ okProd @k @a @()
                 <+ okProd @k @b @()

-- TODO: Specify and derive the following instances by saying that stack is a
-- homomorphism for the classes involved.

instance (Category k, OkProd k) => Category (Stack k) where
  type Ok (Stack k) = Ok k
  -- id = stack id
  id = Stack id'
   where
     id' :: forall a z. Ok2 k a z => (a :* z) `k` (a :* z)
     id' = id <+ okProd @k @a @z
  -- Stack g . Stack f = Stack (g . f)
  (.) :: forall a b c. Ok3 k a b c => Stack k b c -> Stack k a b -> Stack k a c
  Stack g . Stack f = Stack h
   where
     h :: forall z. Ok k z => (a :* z) `k` (c :* z)
     h = g . f
       <+ okProd @k @a @z
       <+ okProd @k @b @z
       <+ okProd @k @c @z
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance (AssociativePCat k, MonoidalPCat k) => AssociativePCat (Stack k) where
  lassocP :: forall a b c. Ok3 k a b c => Stack k (a :* (b :* c)) ((a :* b) :* c)
  lassocP = stack lassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  rassocP :: forall a b c. Ok3 k a b c => Stack k ((a :* b) :* c) (a :* (b :* c))
  rassocP = stack rassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  {-# INLINE lassocP #-}
  {-# INLINE rassocP #-}

instance (AssociativePCat k, MBraidedPCat k) => MonoidalPCat (Stack k) where
  first :: forall a b c. Ok3 k a b c => Stack k a c -> Stack k (a :* b) (c :* b)
  first (Stack f) = Stack h
   where
     h :: forall z. Ok k z => ((a :* b) :* z) `k` ((c :* b) :* z)
     h = inRassocP f <+ okProd @k @b @z   -- h = lassocP . f . rassocP
  second = secondFirst  -- relies on BraidedPCat
  (***) :: forall a b c d. Ok4 k a b c d  -- probably unnecessary & unhelpful
        => Stack k a c -> Stack k b d -> Stack k (a :* b) (c :* d)
  -- (***) = cross  -- f *** g = swap . first g . swap . first f
  (***) = crossSecondFirst  -- f *** g = swap . first g . swap . first f
  -- f *** g = second g . first f
  --           <+ okProd @k @a @b
  --           <+ okProd @k @c @b
  --           <+ okProd @k @c @d
  -- (***) = oops "(***) @Stack"
  {-# INLINE first #-}
  {-# INLINE second #-}
  {-# INLINE (***) #-}

#if 0

-- TEMP
cross :: forall k a b c d. (MBraidedPCat k, Ok4 k a b c d)
      => k a c -> k b d -> k (a :* b) (c :* d)
-- cross = C.crossSecondFirst
f `cross` g = second g . first f
          <+ okProd @k @a @b
          <+ okProd @k @c @b
          <+ okProd @k @c @d
{-# INLINE cross #-}

-- TEMP
cross' :: forall k a b c d. (AssociativePCat k, MBraidedPCat k, Ok4 k a b c d)
      => Stack k a c -> Stack k b d -> Stack k (a :* b) (c :* d)
f `cross'` g = second g . first f
          <+ okProd @k @a @b
          <+ okProd @k @c @b
          <+ okProd @k @c @d
{-# INLINE cross' #-}

#endif

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

instance MBraidedPCat k => BraidedPCat (Stack k) where
  swapP :: forall a b. Ok2 k a b => Stack k (a :* b) (b :* a)
  swapP = stack swapP
        <+ okProd @k @a @b
        <+ okProd @k @b @a
  {-# INLINE swapP #-}

instance MProductCat k => ProductCat (Stack k) where
  exl :: forall a b. Ok2 k a b => Stack k (a :* b) a
  exr :: forall a b. Ok2 k a b => Stack k (a :* b) b
  dup :: forall a  . Ok  k a   => Stack k a (a :* a)
  exl = stack exl <+ okProd @k @a @b
  exr = stack exr <+ okProd @k @a @b
  dup = stack dup <+ okProd @k @a @a
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE dup #-}

instance (MonoidalPCat k, TerminalCat k) => TerminalCat (Stack k) where
  it = stack it
  {-# INLINE it #-}

instance (MProductCat k, BraidedPCat k, AssociativePCat k, TerminalCat k, OkUnit k) => UnitCat (Stack k)

-- instance (MonoidalPCat k, UnitCat k) => UnitCat (Stack k) where
--   lunit :: forall a. Ok k a => Stack k a (() :* a)
--   lunit = stack lunit <+ okProd @k @() @a
--   runit :: forall a. Ok k a => Stack k a (a :* ())
--   runit = stack runit <+ okProd @k @a @()
--   lcounit :: forall a. Ok k a => Stack k (() :* a) a
--   lcounit = stack lcounit <+ okProd @k @() @a
--   rcounit :: forall a. Ok k a => Stack k (a :* ()) a
--   rcounit = stack rcounit <+ okProd @k @a @()
--   {-# INLINE lunit #-}
--   {-# INLINE runit #-}
--   {-# INLINE lcounit #-}
--   {-# INLINE rcounit #-}

instance (MonoidalPCat k, MonoidalSCat k, DistribCat k) => MonoidalSCat (Stack k) where
  -- Stack f +++ Stack g = Stack (inDistr (f +++ g))
  (+++) :: forall a b c d. Ok4 k a b c d => Stack k a c -> Stack k b d -> Stack k (a :+ b) (c :+ d)
  Stack f +++ Stack g = Stack h
   where
     h :: forall z. Ok k z => ((a :+ b) :* z) `k` ((c :+ d) :* z)
     h = inDistr (f +++ g)
         <+ okProd @k @a @z <+ okProd @k @b @z
         <+ okProd @k @c @z <+ okProd @k @d @z
  {-# INLINE (+++) #-}

-- The validity of this (+++) definition relies on the following fact:
-- 
--   first (f +++ g) = inDistr (first f +++ first g)
-- 
-- See proof in 2018-06-11 notes.

instance (MonoidalPCat k, BraidedSCat k) => BraidedSCat (Stack k) where
  swapS :: forall a b. Ok2 k a b => Stack k (a :+ b) (b :+ a)
  swapS = stack swapS
        <+ okCoprod @k @a @b
        <+ okCoprod @k @b @a
  {-# INLINE swapS #-}

instance (MonoidalPCat k, CoproductCat k) => CoproductCat (Stack k) where
  inl :: forall a b. Ok2 k a b => Stack k a (a :+ b)
  inr :: forall a b. Ok2 k a b => Stack k b (a :+ b)
  jam :: forall a. Ok k a => Stack k (a :+ a) a
  inl = stack inl <+ okCoprod @k @a @b
  inr = stack inr <+ okCoprod @k @a @b
  jam = stack jam <+ okCoprod @k @a @a
  {-# INLINE inl #-}
  {-# INLINE inr #-}
  {-# INLINE jam #-}

instance (MonoidalPCat k, NumCat k a) => NumCat (Stack k) a where
  negateC :: Ok k a => Stack k a a
  addC,subC,mulC :: Ok k a => Stack k (a :* a) a
  powIC :: Ok2 k a Int => Stack k (a :* Int) a
  negateC = stack negateC
  addC    = stack addC  <+ okProd @k @a @a
  subC    = stack subC  <+ okProd @k @a @a
  mulC    = stack mulC  <+ okProd @k @a @a
  powIC   = stack powIC <+ okProd @k @a @Int
  {-# INLINE negateC #-}
  {-# INLINE addC #-}
  {-# INLINE subC #-}
  {-# INLINE mulC #-}
  {-# INLINE powIC #-}

-- To do: write a GHC type-checker plugin that automatically applies `okProd`
-- and `okCoprod` entailments. Probably wait until the spurious recompilation
-- issue is fixed and I'm on a current GHC.

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

#ifdef EXAMPLES

t1 :: forall k. (ProductCat k, NumCat k Int) => Int `k` Int
t1 = addC . dup <+ okProd @k @Int @Int

t2 :: (MProductCat k, UnitCat k, NumCat k Int) => Int `k` Int
t2 = evalSM t1

t3 :: Int -> Int
t3 = t2

t4 :: Int
t4 = t3 17

t5 :: Syn Int Int
t5 = t2

-- first add . first dup
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

t13 :: Chain Syn (Int :* z) (Int :* z)
t13 = unStack (addC . (negateC &&& negateC))

t14 :: Syn (Int :* z) (Int :* z)
t14 = unStack (addC . dup)

t15 :: Chain Syn (Int :* z) (Int :* z)
t15 = unStack (addC . dup)

t14' :: Syn (Int :* z) (Int :* z)
t14' = unStack (addC . (id &&& id))
{-# INLINE t14' #-}

t15' :: Chain Syn (Int :* z) (Int :* z)
t15' = unStack (addC . (id &&& id))

z1 :: Syn ((Int :* Bool) :* z) ((Int :* Bool) :* z)
z1 = unStack (first id)
{-# INLINE z1 #-}

z2 :: Syn ((Int :* Bool) :* z) ((Int :* Bool) :* z)
z2 = lassocP . first id . rassocP
{-# INLINE z2 #-}

#endif
