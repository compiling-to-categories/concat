{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# LANGUAGE TypeSynonymInstances #-}  -- TEMP
{-# LANGUAGE FlexibleContexts #-} -- TEMP

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

-- | Generalized automatic differentiation

module Tower where

import Prelude hiding (id,(.),curry,uncurry)

import Control.Newtype (Newtype(..))
import Data.MemoTrie (HasTrie)

import Misc
import ConCat hiding ((<~),(~>))
import Additive
import Semimodule
import FLMap

-- Tower of derivative values.
newtype Tower s a b = T { unT :: b :* Tower s a (LMap s a b) }

-- newtype Tower s a b = T (b :* (LMap s a (Tower s a b)))

instance Newtype (Tower s a b) where
  type O (Tower s a b) = b :* Tower s a (LMap s a b)
  pack = T
  unpack = unT

instance OkL2 s a b => Additive (Tower s a b) where
  zero = pack zero
  (^+^) = inNew2 (^+^)

instance OkL2 s a b => Semimodule (Tower s a b) where
  type Scalar (Tower s a b) = s
  (*^) s = inNew ((*^) s)

newtype D s a b = D { unD :: a -> Tower s a b }

instance Newtype (D s a b) where
  type O (D s a b) = a -> Tower s a b
  pack   = D
  unpack = unD

instance OkL2 s a b => Additive (D s a b) where
  zero  = pack zero
  (^+^) = inNew2 (^+^)

instance OkL2 s a b => Semimodule (D s a b) where
  type Scalar (D s a b) = s
  (*^) s = inNew ((*^) s)


linearD :: OkL2 s a b => (a -> b) -> LMap s a b -> D s a b
linearD f f' = D (\ a -> T (f a, T (f', zero)))

instance Category (D s) where
  type Ok (D s) = OkL s
  id  = linearD id id

#if 0

--   D q . D p = D $ \ a ->
--     let (b,p') = p a
--         (c,q') = q b
--     in
--       (c, q' . p')

--   (.) = inD2 $ \ q p -> \ a ->
--     let (b,p') = p a
--         (c,q') = q b
--     in
--       (c, q' . p')

--   (.) = inD2 $ \ q p -> \ a ->
--     let ((c,q'),p') = first q (p a)
--     in
--       (c, q' . p')

--   (.) = inD2 $ \ q p -> \ a ->
--     second (uncurry (.)) (rassocP (first q (p a)))

--   (.) = inD2 $ \ q p -> \ a ->
--     second (uncurry (.)) (rassocP . (first q . p) $ a)

  (.) = inNew2 $ \ q p -> second (uncurry (.)) . rassocP . (first q . p)

--   (.) = inNew2 $ \ q p ->
--     uncurry (.) . rassocP (first q (p a))

-- TODO: rewrite (.) more generally, to see if we can generalize from (->).

instance (ProductCat k, Prod k ~ (:*)) => ProductCat (D k) where
  type Prod (D k) = Prod k
  exl = linearD exl exl
  exr = linearD exr exr

-- TODO: Revisit the Prod k ~ (:*) constraint. Maybe just Prod (D k) = Prod k?

--   (&&&) = inNew2 $ \ p q -> \ a ->
--     let (b,p') = p a
--         (c,q') = q a
--     in
--       ((b,c), p' &&& q')

--   D p &&& D q = D $ \ a ->
--     let (b,p') = p a
--         (c,q') = q a
--     in
--       ((b,c), p' &&& q')


--   (&&&) = inNew2 $ \ p q -> \ a ->
--     let ((b,p'),(c,q')) = (p &&& q) a in
--       ((b,c), p' &&& q')

--   (&&&) = inNew2 $ \ p q -> \ a ->
--     let (bc,(p',q')) = (transposeP . (p &&& q)) a in
--       (bc, p' &&& q')

  (&&&) = inNew2 $ \ p q -> second (uncurry (&&&)) . transposeP . (p &&& q)

dFun :: D k a b -> (a -> b)
dFun = (fmap.fmap) fst unpack

dDer :: D k a b -> a -> a `k` b
dDer = (fmap.fmap) snd unpack

type DL s = D (LMap s)

-- instance ApplyToCat (D k a b) where
--   ...  

applyDTo :: OkL2 s a b => a -> LMap s (DL s a b) b
applyDTo a = linear (($ a) . dFun)
-- applyDTo a = applyTo a . linear dFun

applyD :: OkL2 s a b => DL s a b :* a -> b :* LMap s (DL s a b :* a) b
applyD (D h,a) = (b, applyDTo a ||| dfa)
 where
   (b,dfa) = h a

-- instance ClosedCat (DL s) where
--   type Exp (DL s) = DL s
--   apply = D applyD

--   curry   :: Ok3 k a b c => (Prod k a b `k` c) -> (a `k` Exp k b c)
--   uncurry :: Ok3 k a b c => (a `k` Exp k b c)  -> (Prod k a b `k` c)

type DL' s a b = D' (LMap s) a b

-- -- foo :: DL' s (a :* b) c -> a -> LMap s b (LMap s b c)
-- foo :: OkL3 s a b c => DL' s (a :* b) c -> a -> (c :* LMap s b (LMap s b c)
-- foo g = \ a -> (. inr) . curry g a

-- g :: a :* b -> c :* (a :* b :-* c)
-- a :: a
-- curry g :: a -> b -> c :* (a :* b :-* c)
-- curry g a :: b -> c :* (a :* b :-* c)

-- want :: D' k a (D' k b c)
--      :: a -> D' k b c :* (a :-* D' k b c)
--      :: a -> (b -> c :* (b :-* c)) :* (a :-* (b -> c :* (b :-* c)))

foo1 :: OkL3 s a b c => DL' s (a :* b) c -> a -> (b -> c :* LMap s b c)
foo1 g a b = (c,abc . inr)
 where
   (c,abc) = g (a,b)

-- Because we're fixing a, use inr so that da = 0

-- foo2 :: OkL3 s a b c => DL' s (a :* b) c -> a -> (LMap s a (b -> c :* LMap s b c))
-- foo2 g a = undefined


-- type D' k a b = a -> b :* (a `k` b)

-- newtype D k a b = D { getD :: D' k a b }

-- curryD :: DL s (a :* b) c -> DL s a (DL s b c)
-- curryD (D g) = D (\ a -> D (second (. inr) . curry g a))

-- g :: a :* b -> c :* (a :* b :-* c)
-- a :: a
-- curry g :: a -> b -> c :* (a :* b :-* c)
-- curry g a :: b -> c :* (a :* b :-* c)

-- second (. inr) . curry g a :: b -> c :* (b :-* c)

-- uncurry :: Ok3 k a b c => (a `k` Exp k b c)  -> (Prod k a b `k` c)

-- uncurry :: (a ~> (b :=> c)) -> (a :* b ~> c)

#endif
