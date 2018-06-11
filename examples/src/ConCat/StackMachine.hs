{-# LANGUAGE InstanceSigs #-}
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

newtype SM a b = SM (forall z. a :* z -> b :* z)

pureSM :: (a -> b) -> SM a b
pureSM f = SM (first f)

evalSM :: SM a b -> (a -> b)
evalSM (SM f) a = b where (b,()) = f (a,())

-- TODO: Generalize SM to take a category parameter, generalizing (->).

-- TODO: Specify and derive the following instances by saying that pureSM or
-- evalSM is a homomorphism for the classes involved.

instance Category SM where
  id = pureSM id
  SM g . SM f = SM (g . f)

instance MonoidalPCat SM where
  -- SM f *** SM g = SM (inRassocP' g . inRassocP' f)
  (***) :: forall a b c d. SM a c -> SM b d -> SM (a :* b) (c :* d)
  SM f *** SM g = SM h
   where
     h :: forall z. (a :* b) :* z -> (c :* d) :* z

     -- h ((a,b),z) = ((c,d),z'')
     --  where
     --    (c,z' ) = f (a,z)
     --    (d,z'') = g (b,z')

     h ((a,b),z) = ((c'',d),z'')
      where
        (c,(b' ,z' )) = f (a ,(b,z ))
        (d,(c'',z'')) = g (b',(c,z'))

inRassocP' :: (a :* (b :* z) -> c :* (b :* z)) -> ((a :* b) :* z -> (b :* c) :* z)
inRassocP' f = first swapP . lassocP . f . rassocP

-- inRassocP' f = first swapP . inRassocP f

-- rassocP :: (a :* b) :* z -> a :* (b :* z)
-- f       :: a :* (b :* z) -> c :* (b :* z)
-- lassocP :: c :* (b :* z) -> (c :* b) :* z

instance ProductCat SM where
  exl = pureSM exl
  exr = pureSM exr
  dup = pureSM dup

instance Num a => NumCat SM a where
  negateC = pureSM negateC
  addC    = pureSM addC
  subC    = pureSM subC
  mulC    = pureSM mulC
  powIC   = pureSM powIC

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
