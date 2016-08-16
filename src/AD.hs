{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

-- | Generalized automatic differentiation

module AD where

import Prelude hiding (id,(.),curry,uncurry)

import Control.Newtype (Newtype(..))

import Misc
import ConCat hiding ((<~),(~>))
import LMap

type D' k a b = a -> b :* (a `k` b)

newtype D k a b = D { getD :: D' k a b }

instance Newtype (D k a b) where
  type O (D k a b) = D' k a b
  pack   = D
  unpack = getD

linearD :: (a -> b) -> (a `k` b) -> D k a b
linearD f f' = D (f &&& konst f')

-- -- linearD' :: (forall cat. Category cat => a `cat` b) -> Category k => D k a b
-- linearD' :: (forall cat a' b'. (Category cat, Ok k a', Ok k b') => a' `cat` b')
--          -> (Ok k a, Ok k b) => Category k => D k a b
-- linearD' f = D (f &&& const f)

instance Category k => Category (D k) where
  type Ok (D k) = Ok k
  id  = linearD id id

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

-- instance Closed (D k) where
--   apply = 

-- type D' k a b = a -> b :* (a `k` b)
-- newtype D k a b = D { getD :: D' k a b }

-- applyD' :: D' k ((a -> b) :* a) b
-- applyD' = apply &&& applyD

-- applyD :: D' (LMap s) a b :* a -> LMap s ((a -> b) :* a) b
-- applyD (ff,a) 

-- applyD (f,a) (df,da) = deriv f a da ^+^ df a

