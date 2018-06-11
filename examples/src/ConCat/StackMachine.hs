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

pureM :: (a -> b) -> SM a b
pureM f = SM (first f)

evalSM :: SM a b -> (a -> b)
evalSM (SM f) a = b where (b,()) = f (a,())

-- TODO: Generalize SM to take a category parameter, generalizing (->).

-- instance Newtype (SM a b) where
--   type O (SM a b) = forall z. a :* z -> b :* z  -- "illegal polymorphic type"
--   pack f = SM f
--   unpack (SM f) = f

unSM :: SM a b -> (forall z. a :* z -> b :* z)
unSM (SM f) = f

inSM :: ((forall z. a :* z -> b :* z) -> (forall z. c :* z -> d :* z))
     -> SM a b -> SM c d
inSM q (SM f) = SM (q f)

inSM2 :: ((forall z. a :* z -> b :* z) -> (forall z. c :* z -> d :* z) -> (forall z. e :* z -> f :* z))
      -> SM a b -> SM c d -> SM e f
inSM2 q (SM f) (SM g) = SM (q f g)

-- TODO: Specify and derive the following instances by saying that pureM or
-- evalSM is a homomorphism for the classes involved.

instance Category SM where
  id = pureM id
  -- SM g . SM f = SM (g . f)
  (.) = inSM2 (.)

instance MonoidalPCat SM where
  (***) :: forall a b c d. SM a c -> SM b d -> SM (a :* b) (c :* d)

  -- SM f *** SM g = SM h
  --  where
  --    h :: forall z. (a :* b) :* z -> (c :* d) :* z
  --    h ((a,b),z) = ((c'',d),z'')
  --     where
  --       (c,(b' ,z' )) = f (a ,(b,z ))
  --       (d,(c'',z'')) = g (b',(c,z'))

  -- SM f *** SM g = SM (first swapP . lassocP . g . swapP' . f . rassocP)

  -- SM f *** SM g = SM (first swapP . lassocP . g . rassocP . first swapP . lassocP . f . rassocP)

  -- SM f *** SM g = SM (first swapP . inRassocP g . first swapP . inRassocP f)

  SM f *** SM g = SM (inRassocP' g . inRassocP' f)

  -- (***) = inSM2 $ \ f g -> inRassocP' g . inRassocP' f

  -- (***) = inSM2 $ \ f g -> \ ((a,b),z) ->
  --           let (c,(b' ,z' )) = f (a ,(b,z ))
  --               (d,(c'',z'')) = g (b',(c,z'))
  --           in
  --             ((c'',d),z'')

inRassocP' :: (a :* (b :* z) -> c :* (b :* z)) -> ((a :* b) :* z -> (b :* c) :* z)
inRassocP' f = first swapP . lassocP . f . rassocP
-- inRassocP' f = first swapP . inRassocP f

-- rassocP :: (a :* b) :* z -> a :* (b :* z)
-- f       :: a :* (b :* z) -> c :* (b :* z)
-- lassocP :: c :* (b :* z) -> (c :* b) :* z
           

instance ProductCat SM where
  exl = pureM exl
  exr = pureM exr
  dup = pureM dup

instance Num a => NumCat SM a where
  negateC = pureM negateC
  addC    = pureM addC
  subC    = pureM subC
  mulC    = pureM mulC
  powIC   = pureM powIC

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
