{-# LANGUAGE RankNTypes #-}
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
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Stack-based VM as a category, enabling compilation from Haskell.

module ConCat.StackVM where

import Prelude hiding (id,(.),curry,uncurry,const)

import ConCat.Misc ((:*),(:+))
import qualified ConCat.Category as C
import ConCat.AltCat

{--------------------------------------------------------------------
    Stack functions (for specification)
--------------------------------------------------------------------}

newtype StackFun a b = SF (forall z. a :* z -> b :* z)

inSF :: ((forall z. a :* z -> b :* z) -> (forall z. c :* z -> d :* z))
     -> StackFun a b -> StackFun c d
inSF w (SF h) = SF (w h)

inSF2 :: ((forall z. a :* z -> b :* z) -> (forall z. c :* z -> d :* z) -> (forall z. p :* z -> q :* z))
      -> StackFun a b -> StackFun c d -> StackFun p q
inSF2 w (SF h) (SF k) = SF (w h k)

-- | The semantic functor that specifies 'StackFun'.
stackFun :: (a -> b) -> StackFun a b
stackFun f = SF (first f)
{-# INLINE stackFun #-}

evalSF :: StackFun a b -> (a -> b)
evalSF (SF f) = rcounit . f . runit
-- evalSF (SF f) a = fst (f (a,()))
-- evalSF (SF f) a = b
--  where
--    (b,()) = f (a,())

instance Category StackFun where
  id = stackFun id
  -- SF g . SF f = SF (g . f)
  (.) = inSF2 (.)
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance AssociativePCat StackFun where
  lassocP = stackFun lassocP
  rassocP = stackFun rassocP
  {-# INLINE lassocP #-}
  {-# INLINE rassocP #-}

instance MonoidalPCat StackFun where
  first = inSF inRassocP -- okay
  -- first (SF f) = SF (inRassocP f)
  -- first (SF f) = SF (lassocP . f . rassocP)
  -- first (SF f) = SF lassocP . SF f . SF rassocP -- doesn't type-check
  second = secondFirst
  f *** g = second g . first f
  {-# INLINE first #-}
  {-# INLINE second #-}
  {-# INLINE (***) #-}

instance BraidedPCat StackFun where
  swapP = stackFun swapP
  {-# INLINE swapP #-}

instance ProductCat StackFun where
  exl = stackFun exl
  exr = stackFun exr
  dup = stackFun dup
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE dup #-}

instance TerminalCat StackFun where
  it = stackFun it
  {-# INLINE it #-}

instance UnitCat StackFun

instance MonoidalSCat StackFun where
  -- SF f +++ SF g = SF (inDistr (f +++ g))
  (+++) = inSF2 (\ f g -> inDistr (f +++ g))
  {-# INLINE (+++) #-}

-- The validity of this (+++) definition relies on the following fact:
-- 
--   first (f +++ g) = inDistr (first f +++ first g)
-- 
-- See proof in 2018-06-11 notes.

instance BraidedSCat StackFun where
  swapS = stackFun swapS
  {-# INLINE swapS #-}

instance CoproductCat StackFun where
  inl = stackFun inl
  inr = stackFun inr
  jam = stackFun jam
  {-# INLINE inl #-}
  {-# INLINE inr #-}
  {-# INLINE jam #-}

instance DistribCat StackFun where
  distl = stackFun distl
  distr = stackFun distr
  {-# INLINE distl #-}
  {-# INLINE distr #-}

-- instance ClosedCat StackFun where
--   apply = stackFun apply
--   curry f = undefined

{--------------------------------------------------------------------
    Stack programs
--------------------------------------------------------------------}

data Op :: * -> * -> * where
  Negate :: Num a => Op a a
  Add, Sub, Mul :: Num a => Op (a :* a) a
  PowI :: Num a => Op (a :* Int) a
  Swap :: Op (a :* b) (b :* a)
  Exl :: Op (a :* b) a
  Exr :: Op (a :* b) b
  Dup :: Op a (a :* a)
  Const :: Show b => b -> Op a b

deriving instance Show (Op a b)

-- instance Show (Op a b) where
--   show Negate    = "negateC"
--   show Add       = "addC"
--   show Sub       = "subC"
--   show Mul       = "mulC"
--   show PowI      = "powIC"
--   show Swap      = "swapP"
--   show Exl       = "exl"
--   show Exr       = "exr"
--   show Dup       = "dup"
--   show (Const b) = show b

-- TODO: showsPrec for Const

-- Alternatively use Syn

evalOp :: Op a b -> (a -> b)
evalOp Negate    = negateC
evalOp Add       = addC
evalOp Sub       = subC
evalOp Mul       = mulC
evalOp PowI      = powIC
evalOp Swap      = swapP
evalOp Exl       = exl
evalOp Exr       = exr
evalOp Dup       = dup
evalOp (Const b) = const b

data StackOp :: * -> * -> * where
  Pure :: Op a b -> StackOp (a :* z) (b :* z)
  Push :: StackOp ((a :* b) :* z) (a :* (b :* z))
  Pop  :: StackOp (a :* (b :* z)) ((a :* b) :* z)

instance Show (StackOp a b) where
  show (Pure op) = show op
  show Push      = "Push"
  show Pop       = "Pop"

instance Show2 StackOp where show2 = show

evalStackOp :: StackOp u v -> (u -> v)
evalStackOp (Pure f) = first (evalOp f)
evalStackOp Push     = rassocP
evalStackOp Pop      = lassocP

infixr 5 :<
data StackOps :: * -> * -> * where
  Nil  :: StackOps a a
  (:<) :: StackOp a b -> StackOps b c -> StackOps a c

toList :: forall z a b. (forall u v. StackOp u v -> z) -> StackOps a b -> [z]
toList f = go
 where
   go :: StackOps p q -> [z]
   go Nil         = []
   go (op :< ops) = f op : go ops

instance Show (StackOps a b) where
  show = show . toList Exists2

evalStackOps :: StackOps a b -> (a -> b)
evalStackOps Nil          = id
evalStackOps (op :< rest) = evalStackOps rest . evalStackOp op

infixr 5 ++*
(++*) :: StackOps a b -> StackOps b c -> StackOps a c
Nil ++* ops'         = ops'
(op :< ops) ++* ops' = op :< (ops ++* ops')

data StackProg a b = SP (forall z. StackOps (a :* z) (b :* z))

instance Show (StackProg a b) where
  show (SP ops) = show ops

instance Category StackProg where
  id  = SP Nil
  SP g . SP f = SP (f ++* g)

-- stackOp :: StackOp a b -> StackProg a b
-- stackOp op = SP (op :< Nil)

opP :: Op a b -> StackProg a b
opP op = SP (Pure op :< Nil)

-- firstP :: StackProg a c -> StackProg (a :* b) (c :* b)
-- firstP (SP ops) = SP (Push :< ops ++* Pop :< Nil)

-- TODO: tweak StackOps so we can postpone flattening.

instance ProductCat StackProg where
  exl = opP Exl
  exr = opP Exr
  dup = opP Dup

instance MonoidalPCat StackProg where
  -- first  = firstP
  first (SP ops) = SP (Push :< ops ++* Pop :< Nil)
  second = secondFirst
  (***)  = crossSecondFirst

instance Show b => ConstCat StackProg b where
  const b = opP (Const b)

instance TerminalCat     StackProg
instance UnitCat         StackProg
instance AssociativePCat StackProg
instance BraidedPCat     StackProg where swapP = opP Swap
  
-- Alternatively, remove Swap and use default in BraidedPCat, though Swap makes
-- for shorter programs.

instance Num a => NumCat StackProg a where
  negateC = opP Negate
  addC    = opP Add
  subC    = opP Sub
  mulC    = opP Mul
  powIC   = opP PowI

{--------------------------------------------------------------------
    Relate StackProg to StackFun
--------------------------------------------------------------------}

-- The semantic homomorphism used to derive instances for StackProg.
progFun :: StackProg a b -> StackFun a b
progFun (SP ops) = SF (evalStackOps ops)

evalProg :: StackProg a b -> (a -> b)
-- evalProg (SP ops) = rcounit . evalStackOps ops . runit
-- evalProg (SP ops) a = fst (evalStackOps ops (a,()))
evalProg = evalSF . progFun

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

data Exists2 k = forall a b. Exists2 (a `k` b)

instance Show2 k => Show (Exists2 k) where show (Exists2 f) = show2 f

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

-- evalProg t1 (7,5) --> -12
t1 :: StackProg (Int :* Int) Int
t1 = addC . (negateC *** negateC)

-- evalProg t2 7 --> -14
t2 :: StackProg Int Int
t2 = addC . (negateC &&& negateC)
