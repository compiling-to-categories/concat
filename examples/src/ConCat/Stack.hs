{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Variant of ConCat.StackMachine, not generalizing over base categories.

module ConCat.Stack where

import Prelude hiding (id,(.),curry,uncurry)

import ConCat.Misc ((:*),(:+))
import qualified ConCat.Category as C
import ConCat.AltCat

newtype Stack a b = Stack (forall z. a :* z -> b :* z)

-- | The semantic functor that specifies 'Stack'.
stack :: (a -> b) -> Stack a b
stack f = Stack (first f)
{-# INLINE stack #-}

instance Category Stack where
  id = stack id
  Stack g . Stack f = Stack (g . f)
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance AssociativePCat Stack where
  lassocP = stack lassocP
  rassocP = stack rassocP
  {-# INLINE lassocP #-}
  {-# INLINE rassocP #-}

instance MonoidalPCat Stack where
  first (Stack f) = Stack (inRassocP f)
  second = secondFirst
  f *** g = second g . first f
  {-# INLINE first #-}
  {-# INLINE second #-}
  {-# INLINE (***) #-}

instance BraidedPCat Stack where
  swapP = stack swapP
  {-# INLINE swapP #-}

instance ProductCat Stack where
  exl = stack exl
  exr = stack exr
  dup = stack dup
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE dup #-}

instance TerminalCat Stack where
  it = stack it
  {-# INLINE it #-}

instance UnitCat Stack

instance MonoidalSCat Stack where
  Stack f +++ Stack g = Stack (inDistr (f +++ g))
  {-# INLINE (+++) #-}

-- The validity of this (+++) definition relies on the following fact:
-- 
--   first (f +++ g) = inDistr (first f +++ first g)
-- 
-- See proof in 2018-06-11 notes.

instance BraidedSCat Stack where
  swapS = stack swapS
  {-# INLINE swapS #-}

instance CoproductCat Stack where
  inl = stack inl
  inr = stack inr
  jam = stack jam
  {-# INLINE inl #-}
  {-# INLINE inr #-}
  {-# INLINE jam #-}

{--------------------------------------------------------------------
    Concrete operations
--------------------------------------------------------------------}

data Op :: * -> * -> * where
  Negate :: Num a => Op a a
  Add, Sub, Mul :: Num a => Op (a :* a) a
  PowI :: Num a => Op (a :* Int) a
  Swap :: Op (a :* b) (b :* a)
  Exl :: Op (a :* b) a
  Exr :: Op (a :* b) b
  Dup :: Op a (a :* a)

instance Show (Op a b) where
  show Negate = "negateC"
  show Add    = "addC"
  show Sub    = "subC"
  show Mul    = "mulC"
  show PowI   = "powIC"
  show Swap   = "swapP"
  show Exl    = "exl"
  show Exr    = "exr"
  show Dup    = "dup"

-- Alternatively use Syn

evalOp :: Op a b -> (a -> b)
evalOp Negate = negateC
evalOp Add    = addC
evalOp Sub    = subC
evalOp Mul    = mulC
evalOp PowI   = powIC
evalOp Swap   = swapP
evalOp Exl    = exl
evalOp Exr    = exr
evalOp Dup    = dup

-- We can generalize evalOp to yield a `k` b if we parametrize Op by k and add
-- Ok k constraints.

-- If Op is a NumCat but not a Category, then I'll have to move Ok out of Category.
-- I'd like to anyway in preparation for the entailment plugin.
-- Meanwhile, a bogus Category instance.
instance Category Op where
  id  = error "id @ Op: undefined"
  (.) = error "(.) @ Op: undefined"

instance Num a => NumCat Op a where
  negateC = Negate
  addC    = Add
  subC    = Sub
  mulC    = Mul
  powIC   = PowI

instance BraidedPCat Op where
  swapP = Swap

instance ProductCat Op where
  exl = Exl
  exr = Exr
  dup = Dup

data StackOp :: * -> * -> * where
  Pure :: Op a b -> StackOp (a :* z) (b :* z)
  Push :: StackOp ((a :* b) :* z) (a :* (b :* z))
  Pop  :: StackOp (a :* (b :* z)) ((a :* b) :* z)

instance Show (StackOp a b) where
  show (Pure op) = show op
  show Push      = "Push"
  show Pop       = "Pop"

evalStackOp :: StackOp u v -> (u -> v)
evalStackOp (Pure f) = first (evalOp f)
evalStackOp Push     = rassocP
evalStackOp Pop      = lassocP

{--------------------------------------------------------------------
    Function sequences
--------------------------------------------------------------------}

-- Try also removing the category parameter from ConCat.Funs. I don't think this
-- one will be useful and that I will use Ops Op instead.

infixr 5 :<
data Funs :: (* -> * -> *) where
  Nil  :: Funs a a
  (:<) :: (a -> b) -> Funs b c -> Funs a c

evalFuns :: Funs a b -> (a -> b)
evalFuns Nil          = id
evalFuns (op :< rest) = evalFuns rest . op

pureFuns :: (a -> b) -> Funs a b
pureFuns f = f :< Nil

-- instance Show (Funs a b) where
--   show = show . exops

exops :: Funs a b -> [Exists2 (->)]
exops Nil = []
exops (op :< ops) = Exists2 op : exops ops

-- showFuns :: forall k a b. Show2 k => Funs a b -> String
-- showFuns ops = "[" ++ intercalate "," (sh ops) ++ "]"
--  where
--    sh :: forall u v. Funs u v -> [String]
--    sh Nil = []
--    sh (op :< ops) = show2 op : sh ops

instance Category Funs where
  id  = Nil
  (.) = flip (++*)

infixr 5 ++*
(++*) :: Funs a b -> Funs b c -> Funs a c
(++*) Nil ops          = ops
(++*) (op :< ops) ops' = op :< (ops ++* ops')

instance AssociativePCat Funs where
  lassocP = pureFuns lassocP
  rassocP = pureFuns rassocP

instance MonoidalPCat Funs where
  first Nil = Nil
  first (op :< ops) = first op :< first ops
  second = secondFirst
  (***) = crossSecondFirst

instance BraidedPCat Funs where
  swapP = swapP :< Nil

instance ProductCat Funs where
  exl = pureFuns exl
  exr = pureFuns exr
  dup = pureFuns dup

instance TerminalCat Funs where
  it = pureFuns it

instance UnitCat Funs
  
instance Num a => NumCat Funs a where
  negateC = pureFuns negateC
  addC    = pureFuns addC
  subC    = pureFuns subC
  mulC    = pureFuns mulC
  powIC   = pureFuns powIC

-- TODO: Many more instances

{--------------------------------------------------------------------
    Miscellany
--------------------------------------------------------------------}

data Exists2 k = forall a b. Exists2 (a `k` b)

instance Show2 k => Show (Exists2 k) where show (Exists2 f) = show2 f
