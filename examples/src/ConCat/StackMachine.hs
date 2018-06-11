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

import Control.Newtype.Generics

import ConCat.Misc ((:*))
import qualified ConCat.Category as C
import ConCat.AltCat

newtype SM k a b = SM (forall z. Ok k z => (a :* z) `k` (b :* z))

pureSM :: (MonoidalPCat k, Ok2 k a b) => (a `k` b) -> SM k a b
pureSM f = SM (first f)

evalSM :: SM (->) a b -> (a -> b)
evalSM (SM f) a = b where (b,()) = f (a,())

-- TODO: generalize evalSM via categorical language.

-- TODO: Generalize SM to take a category parameter, generalizing (->).

-- TODO: Specify and derive the following instances by saying that pureSM or
-- evalSM is a homomorphism for the classes involved.

instance MonoidalPCat k => Category (SM k) where
  type Ok (SM k) = Ok k
  id = pureSM id
  (.) :: forall a b c. Ok3 k a b c => SM k b c -> SM k a b -> SM k a c
  SM (g :: forall z. Ok k z => (b :* z) `k` (c :* z))
   . SM (f :: forall z. Ok k z => (a :* z) `k` (b :* z)) = SM h
   where
     h :: forall z. Ok k z => (a :* z) `k` (c :* z)
     h = g . f
         <+ okProd @k @a @z
         <+ okProd @k @b @z
         <+ okProd @k @c @z

instance ProductCat k => MonoidalPCat (SM k) where
  first :: forall a b c. Ok3 k a b c => SM k a c -> SM k (a :* b) (c :* b)
  first (SM f) = SM (first f)
                 <+ okProd @k @a @b
                 <+ okProd @k @c @b
  second :: forall a b d. Ok3 k a b d => SM k b d -> SM k (a :* b) (a :* d)
  second g = swapP . first g . swapP
  (***) :: forall a b c d. Ok4 k a b c d => SM k a c -> SM k b d -> SM k (a :* b) (c :* d)
  f *** g = second g . first f
            <+ okProd @k @a @b
            <+ okProd @k @c @b
            <+ okProd @k @c @d

  -- SM f *** SM g = SM h
  --  where
  --    h :: forall z. (a :* b) :* z -> (c :* d) :* z
  --    h ((a,b),z) = ((c'',d),z'')
  --     where
  --       (c,(b' ,z' )) = f (a ,(b,z ))
  --       (d,(c'',z'')) = g (b',(c,z'))

-- TODO: Add BraidedCat with swapP, and weaken the precondition in the
-- MonoidalPCat (SM k) instance above from ProductCat to BraidedCat.

-- instance MonoidalPCat k => MonoidalPCat (SM k) where
--   (***) :: forall a b c d. Ok4 k a b c d => SM k a c -> SM k b d -> SM k (a :* b) (c :* d)
--   SM (f :: forall z. Ok k z => (a :* z) `k` (c :* z))
--    *** SM (g :: forall z. Ok k z => (b :* z) `k` (d :* z))
--    = SM (inRassocP' g . inRassocP' f)
--   -- SM f *** SM g = SM h
--   --  where
--   --    h :: forall z. (a :* b) :* z -> (c :* d) :* z
--   --    h ((a,b),z) = ((c'',d),z'')
--   --     where
--   --       (c,(b' ,z' )) = f (a ,(b,z ))
--   --       (d,(c'',z'')) = g (b',(c,z'))

-- inRassocP' :: ((a :* (b :* z)) `k` (c :* (b :* z))) -> (((a :* b) :* z) `k` ((b :* c) :* z))
-- inRassocP' f = first swapP . lassocP . f . rassocP

-- inRassocP' f = first swapP . inRassocP f

-- rassocP :: (a :* b) :* z -> a :* (b :* z)
-- f       :: a :* (b :* z) -> c :* (b :* z)
-- lassocP :: c :* (b :* z) -> (c :* b) :* z

instance ProductCat k => ProductCat (SM k) where
  exl :: forall a b. Ok2 k a b => SM k (a :* b) a
  exl = pureSM exl <+ okProd @k @a @b
  exr :: forall a b. Ok2 k a b => SM k (a :* b) b
  exr = pureSM exr <+ okProd @k @a @b
  dup :: forall a. Ok k a => SM k a (a :* a)
  dup = pureSM dup <+ okProd @k @a @a

instance (MonoidalPCat k, NumCat k a) => NumCat (SM k) a where
  negateC :: Ok k a => SM k a a
  addC,subC,mulC :: Ok k a => SM k (a :* a) a
  powIC :: Ok2 k a Int => SM k (a :* Int) a
  negateC = pureSM negateC
  addC    = pureSM addC  <+ okProd @k @a @a
  subC    = pureSM subC  <+ okProd @k @a @a
  mulC    = pureSM mulC  <+ okProd @k @a @a
  powIC   = pureSM powIC <+ okProd @k @a @Int

#if 0

-- | Stack machine
data Code :: * -> * -> * where
  Nil  :: Code a a
  (:<) :: Op a b -> Code b c -> Code a c

(++*) :: Code a b -> Code b c -> Code a c
(++*) Nil ops = ops
(++*) (op :< ops) ops' = op :< (ops ++* ops')

data Op :: * -> * -> * where
  Add :: Num a => Op (a :* a) a
  Negate :: Num a => Op a a

evalCode :: Code a b -> a -> b
evalCode Nil = id
evalCode (op :< rest) = evalCode rest . evalOp op

evalOp :: Op a b -> a -> b
evalOp Add = uncurry (+)
evalOp Negate = negate

instance Category Code where
  id = Nil
  (.) = flip (++*)

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
