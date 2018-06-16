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

import Data.List (intercalate)

import Control.Newtype.Generics (Newtype(..))

import ConCat.Misc ((:*),(:+))
import qualified ConCat.Category as C
import ConCat.AltCat
import ConCat.Syntactic (Syn)

{--------------------------------------------------------------------
    Stack machines
--------------------------------------------------------------------}

newtype SM k a b = SM { unSM :: forall z. Ok k z => (a :* z) `k` (b :* z) }

-- | The semantic functor that specifies 'SM'.
pureSM :: (MonoidalPCat k, Ok2 k a b) => (a `k` b) -> SM k a b
pureSM f = SM (first f)

evalSM :: forall k a b. (Category k, UnitCat k, OkProd k, Ok2 k a b)
       => SM k a b -> (a `k` b)
evalSM (SM f) = rcounit . f . runit
                <+ okProd @k @a @()
                <+ okProd @k @b @()

-- TODO: Specify and derive the following instances by saying that pureSM is a
-- homomorphism for the classes involved.

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

instance BraidedPCat k => MonoidalPCat (SM k) where
  first :: forall a b c. Ok3 k a b c => SM k a c -> SM k (a :* b) (c :* b)
  first (SM f) = SM h
   where
     h :: forall z. Ok k z => ((a :* b) :* z) `k` ((c :* b) :* z)
     h = inRassocP f <+ okProd @k @b @z   -- h = lassocP . f . rassocP
  second = secondFirst  -- relies on BraidedPCat
  (***) = crossSecondFirst  -- f *** g = swap . first g . swap . first f
  lassocP :: forall a b c. Ok3 k a b c => SM k (a :* (b :* c)) ((a :* b) :* c)
  lassocP = pureSM lassocP
            <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
            <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  rassocP :: forall a b c. Ok3 k a b c => SM k ((a :* b) :* c) (a :* (b :* c))
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

instance BraidedPCat k => BraidedPCat (SM k) where
  swapP :: forall a b. Ok2 k a b => SM k (a :* b) (b :* a)
  swapP = pureSM swapP
        <+ okProd @k @a @b
        <+ okProd @k @b @a

instance ProductCat k => ProductCat (SM k) where
  exl :: forall a b. Ok2 k a b => SM k (a :* b) a
  exr :: forall a b. Ok2 k a b => SM k (a :* b) b
  dup :: forall a  . Ok  k a   => SM k a (a :* a)
  exl = pureSM exl <+ okProd @k @a @b
  exr = pureSM exr <+ okProd @k @a @b
  dup = pureSM dup <+ okProd @k @a @a

instance (MonoidalPCat k, TerminalCat k) => TerminalCat (SM k) where
  it = pureSM it

instance (ProductCat k, TerminalCat k, OkUnit k) => UnitCat (SM k)

-- instance (MonoidalPCat k, UnitCat k) => UnitCat (SM k) where
--   lunit :: forall a. Ok k a => SM k a (() :* a)
--   lunit = pureSM lunit <+ okProd @k @() @a
--   runit :: forall a. Ok k a => SM k a (a :* ())
--   runit = pureSM runit <+ okProd @k @a @()
--   lcounit :: forall a. Ok k a => SM k (() :* a) a
--   lcounit = pureSM lcounit <+ okProd @k @() @a
--   rcounit :: forall a. Ok k a => SM k (a :* ()) a
--   rcounit = pureSM rcounit <+ okProd @k @a @()

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

instance (BraidedSCat k, DistribCat k) => BraidedSCat (SM k) where
  swapS :: forall a b. Ok2 k a b => SM k (a :+ b) (b :+ a)
  swapS = pureSM swapS
        <+ okCoprod @k @a @b
        <+ okCoprod @k @b @a

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

{--------------------------------------------------------------------
    Stack machine with symbolic operations
--------------------------------------------------------------------}

-- Stack operation
data SOp :: (* -> * -> *) -> (* -> * -> *) where
  First  :: Ok3 k a b z => (a `k` b) -> SOp k (a :* z) (b :* z)
  Rassoc :: Ok3 k a b z => SOp k ((a :* b) :* z) (a :* (b :* z))
  Lassoc :: Ok3 k a b z => SOp k (a :* (b :* z)) ((a :* b) :* z)

evalSOp :: MonoidalPCat k => SOp k u v -> (u `k` v)
evalSOp (First f) = first f
evalSOp Rassoc    = rassocP
evalSOp Lassoc    = lassocP

instance Show2 k => Show2 (SOp k) where
  show2 (First f) = "first " ++ show2 f  -- TODO: fancy up later
  show2 Lassoc = "lassocP"
  show2 Rassoc = "rassocP"

infixr 5 :<
data Ops :: (* -> * -> *) -> (* -> * -> *) where
  Nil  :: Ok  k a => Ops k a a
  (:<) :: Ok3 k a b c => a `k` b -> Ops k b c -> Ops k a c

evalOps :: MonoidalPCat k => Ops k a b -> a `k` b
evalOps Nil          = id
evalOps (op :< rest) = evalOps rest . op

pureOps :: Ok2 k a b => a `k` b -> Ops k a b
pureOps f = f :< Nil

instance Show2 k => Show (Ops k a b) where
  show = show . exops

exops :: Ops k a b -> [Exists2 k]
exops Nil = []
exops (op :< ops) = Exists2 op : exops ops

-- showOps :: forall k a b. Show2 k => Ops k a b -> String
-- showOps ops = "[" ++ intercalate "," (sh ops) ++ "]"
--  where
--    sh :: forall u v. Ops k u v -> [String]
--    sh Nil = []
--    sh (op :< ops) = show2 op : sh ops

instance Category (Ops k) where
  type Ok (Ops k) = Ok k
  id  = Nil
  (.) = flip (++*)

infixr 5 ++*
(++*) :: Ok3 k a b c => Ops k a b -> Ops k b c -> Ops k a c
(++*) Nil ops          = ops
(++*) (op :< ops) ops' = op :< (ops ++* ops')

instance BraidedPCat k => MonoidalPCat (Ops k) where
  first :: forall a b c. Ok3 k a b c => Ops k a c -> Ops k (a :* b) (c :* b)
  first Nil = Nil <+ okProd @k @a @b
  first (op :< ops) = firstCons op ops
   where
     firstCons :: forall x. Ok k x => (a `k` x) -> Ops k x c -> Ops k (a :* b) (c :* b)
     firstCons f fs = first f :< first fs
       <+ okProd @k @a @b <+ okProd @k @c @b <+ okProd @k @x @b
  lassocP :: forall a b c. Ok3 k a b c => Ops k (a :* (b :* c)) ((a :* b) :* c)
  lassocP = pureOps lassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  rassocP :: forall a b c. Ok3 k a b c => Ops k ((a :* b) :* c) (a :* (b :* c))
  rassocP = pureOps rassocP
          <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
          <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
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
  
instance (OkProd k, NumCat k a) => NumCat (Ops k) a where
  negateC = pureOps negateC
  addC  = pureOps addC  <+ okProd @k @a @a
  subC  = pureOps subC  <+ okProd @k @a @a
  mulC  = pureOps mulC  <+ okProd @k @a @a
  powIC = pureOps powIC <+ okProd @k @a @Int

instance TerminalCat k => TerminalCat (Ops k) where
  it = pureOps it

instance (ProductCat k, TerminalCat k) => UnitCat (Ops k)

data Op :: (* -> * -> *) where
  SwapP :: Op (a :* b) (b :* a)
  Exl :: Op (a :* b) a
  Exr :: Op (a :* b) b
  Dup :: Op a (a :* a)
  It  :: Op a ()
  Negate :: Num a => Op a a
  Add, Sub, Mul :: Num a => Op (a :* a) a
  PowIC :: Num a => Op (a :* Int) a
  -- ...

instance BraidedPCat Op where swapP = SwapP
instance ProductCat  Op where { exl = Exl; exr = Exr; dup = Dup }
instance TerminalCat Op where it = It

-- I don't want the following, but I currently need them for superclass requirements.
-- TODO: try removing those superclass constraints.
instance Category     Op
instance MonoidalPCat Op

instance Num a => NumCat Op a where
  negateC = Negate
  addC    = Add
  mulC    = Mul
  subC    = Sub
  powIC   = PowIC

instance Show2 Op where
  show2 SwapP  = "swapP"
  show2 Exl    = "exl"
  show2 Exr    = "exr"
  show2 Dup    = "dup"
  show2 It     = "it"
  show2 Negate = "negate"
  show2 Add    = "add"
  show2 Sub    = "sub"
  show2 Mul    = "mul"
  show2 PowIC  = "powIC"

-- unSM :: SM (Ops k) a b -> Ops k (a :* ()) (b :* ())
-- evalSM :: Ops k (a :* ()) (b :* ()) -> (a :* ()) `k` (b :* ())

-- Could not deduce (UnitCat (Ops k)) arising from a use of ‘evalSM’
-- 
-- Makes sense. I think we'll need another evalSM without UnitCat.

t1 :: forall k a. (ProductCat k, NumCat k a) => SM k a a
t1 = addC . dup
  <+ okProd @k @a @a

t2 :: forall k a. (ProductCat k, UnitCat k, NumCat k a) => a `k` a
t2 = evalSM t1

t3 :: Num a => a -> a
t3 = t2

t4 :: Int
t4 = t3 17

t5 :: (ProductCat k, NumCat k a, TerminalCat k) => Ops k a a
t5 = t2

t6 :: Int -> Int
t6 = evalOps t2

t7 :: Ops Op Int Int
t7 = t5

t8 :: Ops Syn Int Int
t8 = t5

t9 :: Syn Int Int
t9 = t2

t10 :: Syn (Int,z) (Int,z)
t10 = unSM t1

#if 0

{--------------------------------------------------------------------
    Stack machine with symbolic operations
--------------------------------------------------------------------}

newtype SM' k a b = SM' (forall z. Ok k z => Ops k (a :* z) (b :* z))
  
evalSM' :: forall k a b. (MonoidalPCat k, UnitCat k, Ok2 k a b)
        => SM' k a b -> (a `k` b)
evalSM' (SM' f) = rcounit . evalOps f . runit
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
  lassocP :: forall a b c. Ok3 k a b c => SM' k (a :* (b :* c)) ((a :* b) :* c)
  lassocP = pureSM' lassocP
            <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
            <+ okProd @k @(a :* b) @c <+ okProd @k @a @b
  rassocP :: forall a b c. Ok3 k a b c => SM' k ((a :* b) :* c) (a :* (b :* c))
  rassocP = pureSM' rassocP
            <+ okProd @k @a @(b :* c) <+ okProd @k @b @c
            <+ okProd @k @(a :* b) @c <+ okProd @k @a @b

-- TODO: h = lassocP . ops . rassocP = inRassocP ops

instance ProductCat k => BraidedPCat (SM' k) where
  swapP :: forall a b. Ok2 k a b => SM' k (a :* b) (b :* a)
  swapP = pureSM' swapP
        <+ okProd @k @a @b
        <+ okProd @k @b @a

instance ProductCat k => ProductCat (SM' k) where
  exl :: forall a b. Ok2 k a b => SM' k (a :* b) a
  exr :: forall a b. Ok2 k a b => SM' k (a :* b) b
  dup :: forall a  . Ok  k a   => SM' k a (a :* a)
  exl = pureSM' exl <+ okProd @k @a @b
  exr = pureSM' exr <+ okProd @k @a @b
  dup = pureSM' dup <+ okProd @k @a @a

-- instance (ProductCat k, OkUnit k) => UnitCat (SM' k)

-- TODO: refactor to eliminate the repetitive nature of SM vs SM'.
-- Can I simply use SM (Ops k)?

-- TODO: Try making the product and coproduct type operations into *parameters*
-- of MonoidalCat and then maybe of ProductCat and CoproductCat.

#endif


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

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

data Exists2 k = forall a b. Exists2 (a `k` b)

instance Show2 k => Show (Exists2 k) where show (Exists2 f) = show2 f
