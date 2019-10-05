{-# LANGUAGE TupleSections #-}
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

unSF :: StackFun a b -> forall z. a :* z -> b :* z
unSF (SF h) = h

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

evalStackFun :: StackFun a b -> (a -> b)
evalStackFun (SF f) = rcounit . f . runit
-- evalStackFun (SF f) a = fst (f (a,()))
-- evalStackFun (SF f) a = b
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
  SF f +++ SF g = SF (undistr . (f +++ g) . distr)
  -- (+++) = inSF2 (\ f g -> inDistr (f +++ g))
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

instance ClosedCat StackFun where
  apply = stackFun apply
  curry sf = stackFun (curry (evalStackFun sf))
  uncurry sf = stackFun (uncurry (evalStackFun sf))
  {-# INLINE apply #-}
  {-# INLINE curry #-}
  {-# INLINE uncurry #-}

{--------------------------------------------------------------------
    Stack programs
--------------------------------------------------------------------}

data Prim :: * -> * -> * where
  Swap :: Prim (a :* b) (b :* a)
  Exl :: Prim (a :* b) a
  Exr :: Prim (a :* b) b
  Dup :: Prim a (a :* a)
  Const :: Show b => b -> Prim a b
  Negate :: Num a => Prim a a
  Add, Sub, Mul :: Num a => Prim (a :* a) a
  PowI :: Num a => Prim (a :* Int) a
  -- Experiment
  -- (:+++) :: StackProg a c -> StackProg b d -> Prim (a :+ b) (c :+ d)
  (:+++) :: StackOps a c -> StackOps b d -> Prim (a :+ b) (c :+ d)
  Apply :: Prim ((a -> b) :* a) b
  Curry :: StackProg (a :* b) c -> Prim a (b -> c)

deriving instance Show (Prim a b)

-- instance Show (Prim a b) where
--   show Swap      = "swapP"
--   show Exl       = "exl"
--   show Exr       = "exr"
--   show Dup       = "dup"
--   show (Const b) = show b
--   show Negate    = "negateC"
--   show Add       = "addC"
--   show Sub       = "subC"
--   show Mul       = "mulC"
--   show PowI      = "powIC"

-- TODO: showsPrec for Const

-- Alternatively use Syn

evalPrim :: Prim a b -> (a -> b)
evalPrim Exl       = exl
evalPrim Exr       = exr
evalPrim Dup       = dup
evalPrim (Const b) = const b
evalPrim Negate    = negateC
evalPrim Add       = addC
evalPrim Sub       = subC
evalPrim Mul       = mulC
evalPrim PowI      = powIC
evalPrim Swap      = swapP
-- evalPrim (f :+++ g) = evalProg f +++ evalProg g
evalPrim (f :+++ g) = evalStackOps f +++ evalStackOps g
evalPrim Apply     = apply
evalPrim (Curry p) = curry (evalProg p)

data StackOp :: * -> * -> * where
  Pure :: Prim a b -> StackOp (a :* z) (b :* z)
  Push :: StackOp ((a :* b) :* z) (a :* (b :* z))
  Pop  :: StackOp (a :* (b :* z)) ((a :* b) :* z)

instance Show (StackOp a b) where
  show (Pure op) = show op
  show Push      = "Push"
  show Pop       = "Pop"

instance Show2 StackOp where show2 = show

evalStackOp :: StackOp u v -> (u -> v)
evalStackOp (Pure f) = first (evalPrim f)
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

data StackProg a b = SP { unSP :: forall z. StackOps (a :* z) (b :* z) }

instance Show (StackProg a b) where
  show (SP ops) = show ops

instance Category StackProg where
  id  = SP Nil
  SP g . SP f = SP (f ++* g)

-- stackOp :: StackOp a b -> StackProg a b
-- stackOp op = SP (op :< Nil)

primProg :: Prim a b -> StackProg a b
primProg p = SP (Pure p :< Nil)

-- firstP :: StackProg a c -> StackProg (a :* b) (c :* b)
-- firstP (SP ops) = SP (Push :< ops ++* Pop :< Nil)

-- TODO: tweak StackOps so we can postpone flattening.

instance ProductCat StackProg where
  exl = primProg Exl
  exr = primProg Exr
  dup = primProg Dup

instance MonoidalPCat StackProg where
  -- first  = firstP
  first (SP ops) = SP (Push :< ops ++* Pop :< Nil)
  second = secondFirst
  (***)  = crossSecondFirst

-- instance MonoidalSCat StackProg where
--   -- SP f +++ SP g = SP (inDistr (f +++ g))
--   SP f +++ SP g = SP (undistr . (f +++ g) . distr)
--   -- (+++) = inSP2 (\ f g -> inDistr (f +++ g))
--   {-# INLINE (+++) #-}

-- SP f :: StackProg a c
-- SP g :: StackProg b d

-- f :: StackOps (a :* z) (c :* z)
-- g :: StackOps (b :* z) (d :* z)

instance Show b => ConstCat StackProg b where
  const b = primProg (Const b)

instance TerminalCat     StackProg
instance UnitCat         StackProg
instance AssociativePCat StackProg
instance BraidedPCat     StackProg where swapP = primProg Swap
  
-- Alternatively, remove Swap and use default in BraidedPCat, though Swap makes
-- for shorter programs.

-- data StackProg a b = SP { unSP :: forall z. StackOps (a :* z) (b :* z) }

instance ClosedCat StackProg where
  apply = primProg Apply
  curry p = primProg (Curry p)

instance Num a => NumCat StackProg a where
  negateC = primProg Negate
  addC    = primProg Add
  subC    = primProg Sub
  mulC    = primProg Mul
  powIC   = primProg PowI

{--------------------------------------------------------------------
    Relate StackProg to StackFun
--------------------------------------------------------------------}

-- The semantic homomorphism used to derive instances for StackProg.
progFun :: StackProg a b -> StackFun a b
progFun (SP ops) = SF (evalStackOps ops)

evalProg :: StackProg a b -> (a -> b)
evalProg = evalStackFun . progFun

-- evalProg (SP ops) = rcounit . evalStackOps ops . runit
-- evalProg (SP ops) a = fst (evalStackOps ops (a,()))

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
