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
(++*) Nil ops          = ops
(++*) (op :< ops) ops' = op :< (ops ++* ops')

data Prog a b = Prog (forall z. StackOps (a :* z) (b :* z))

instance Show (Prog a b) where
  show (Prog ops) = show ops

evalProg :: Prog a b -> (a -> b)
evalProg (Prog ops) = rcounit . evalStackOps ops . runit

instance Category Prog where
  id  = Prog Nil
  Prog g . Prog f = Prog (f ++* g)

-- stackOp :: StackOp a b -> Prog a b
-- stackOp op = Prog (op :< Nil)

opP :: Op a b -> Prog a b
opP op = Prog (Pure op :< Nil)

-- firstP :: Prog a c -> Prog (a :* b) (c :* b)
-- firstP (Prog ops) = Prog (Push :< ops ++* Pop :< Nil)

-- TODO: tweak StackOps so we can postpone flattening.

instance ProductCat Prog where
  exl = opP Exl
  exr = opP Exr
  dup = opP Dup

instance MonoidalPCat Prog where
  -- first  = firstP
  first (Prog ops) = Prog (Push :< ops ++* Pop :< Nil)
  second = secondFirst
  (***)  = crossSecondFirst

instance Show b => ConstCat Prog b where
  const b = opP (Const b)

instance TerminalCat     Prog
instance UnitCat         Prog
instance AssociativePCat Prog
instance BraidedPCat     Prog where swapP = opP Swap
  
-- Alternatively, remove Swap and use default in BraidedPCat, though Swap makes
-- for shorter programs.

instance Num a => NumCat Prog a where
  negateC = opP Negate
  addC    = opP Add
  subC    = opP Sub
  mulC    = opP Mul
  powIC   = opP PowI

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

data Exists2 k = forall a b. Exists2 (a `k` b)

instance Show2 k => Show (Exists2 k) where show (Exists2 f) = show2 f

{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

-- evalProg t1 (7,5) --> -12
t1 :: Prog (Int :* Int) Int
t1 = addC . (negateC *** negateC)

-- evalProg t2 7 --> -14
t2 :: Prog Int Int
t2 = addC . (negateC &&& negateC)
