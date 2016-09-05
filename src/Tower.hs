{-# LANGUAGE TupleSections #-}
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

{--------------------------------------------------------------------
    Tower of derivative values
--------------------------------------------------------------------}

type Tower s a b = b :* MT s a b

newtype MT s a b = MT (LMap s a (Tower s a b))

instance Newtype (MT s a b) where
  type O (MT s a b) = LMap s a (Tower s a b)
  pack m = MT m
  unpack (MT m) = m

-- TODO: MT as a newtype with a Category instance, and
-- Tower s a b = b :* MT s a b.

instance OkL2 s a b => Additive (MT s a b) where
  zero = pack zero
  (^+^) = inNew2 (^+^)

instance OkL2 s a b => Semimodule (MT s a b) where
  type Scalar (MT s a b) = s
  (*^) s = inNew ((*^) s)

linearT :: OkL2 s a b => LMap s a b -> MT s a b
linearT f = pack (f &&& zero)

(@.) :: OkL3 s a b c => MT s b c -> MT s a b -> MT s a c
(@.) = inNew2 $ \ bc ab -> second comp . rassocP . first bc . ab

-- MT bc @. MT ab = MT (second comp . rassocP . first bc . ab)

comp :: OkL3 s a b c => LMap s (MT s b c :* MT s a b) (MT s a c)
comp = linear (uncurry (@.))

-- TODO: prove that uncurry (@.) is linear. Hm. Seems more likely bilinear.

#if 0

type T a b = b :* (a +> b)

type a +> b = a :-* T a b

newtype MT a b = MT (a +> b)

ab          :: a +> b
first bc    :: b :* (a +> b)               :-* T b c :* (a +> b)
rassocP     :: T b c :* (a +> b)           :-* c :* ((b +> c) :* (a +> b))
second comp :: c :* ((b +> c) :* (a +> b)) :-* c :* (a +> c)

#endif

instance Category (MT s) where
  type Ok (MT s) = OkL s
  id  = linearT id
  (.) = (@.)

instance ProductCat (MT s) where
  type Prod (MT s) = (:*)
  exl   = linearT exl
  exr   = linearT exr
  (&&&) = inNew2 $ \ ac ad -> second fork . transposeP . (ac &&& ad)

fork :: OkL3 s a c d => LMap s (MT s a c :* MT s a d) (MT s a (c :* d))
fork = linear (uncurry (&&&))

#if 0
ac :: a +> c
ad :: a +> d

ac &&& ad   :: a   :-* T a c :* T a d
            == a   :-* (c :* (a +> c)) :* (d :* (a +> d))
transposeP  :: ... :-* (c :* d) :* ((a +> c) :* (a +> d))
second fork :: ... :-* (c * d) :* (a +> (c :* d))
#endif

instance CoproductCat (MT s) where
  type Coprod (MT s) = (:*)
  inl   = linearT inl
  inr   = linearT inr

--   (|||) = inNew2 $ \ ac bc -> ...

#if 0
ac :: a +> c
   == a :-* T a c
   == a :-* c :* (a +> c)
bc :: b +> c
   == b :-* T b c
   == b :-* c :* (b +> c)



inl :: a :-* a :* b



second (inl) . ac :: a :-* c :* 

ac ||| bc   :: a :* b :-* T (a :* b) c
            == a   :-* (c :* (a +> c)) :* (d :* (a +> d))
transposeP  :: ... :-* (c :* d) :* ((a +> c) :* (a +> d))
second fork :: ... :-* (c * d) :* (a +> (c :* d))
#endif

{--------------------------------------------------------------------
    Differentiable functions
--------------------------------------------------------------------}

newtype D s a b = D (a -> Tower s a b)

instance Newtype (D s a b) where
  type O (D s a b) = a -> Tower s a b
  pack f = D f
  unpack (D f) = f

instance OkL2 s a b => Additive (D s a b) where
  zero  = pack zero
  (^+^) = inNew2 (^+^)

instance OkL2 s a b => Semimodule (D s a b) where
  type Scalar (D s a b) = s
  (*^) s = inNew ((*^) s)

constT :: OkL2 s a b => b -> Tower s a b
constT = (,zero)

linearD :: OkL2 s a b => LMap s a b -> D s a b
linearD f = D (\ a -> (f $@ a, linearT f))

-- linearD f = D (pack . (lapply f &&& const (constT f)))

instance Category (D s) where
  type Ok (D s) = OkL s
  id = linearD id
  (.) = inNew2 $ \ q p -> second (uncurry (.)) . rassocP . first q . p

--   D q . D p = D $ \ a ->
--     let (b,p') = p a
--         (c,q') = q b
--     in
--       (c, q' . p')

--   (.) = inNew2 $ \ q p -> \ a ->
--     let (b,p') = p a
--         (c,q') = q b
--     in
--       (c, q' . p')

--   (.) = inNew2 $ \ q p -> \ a ->
--     let ((c,q'),p') = first q (p a)
--     in
--       (c, q' . p')

--   (.) = inNew2 $ \ q p -> \ a ->
--     second (uncurry (.)) (rassocP (first q (p a)))

--   (.) = inNew2 $ \ q p -> \ a ->
--     second (uncurry (.)) (rassocP . (first q . p) $ a)

-- TODO: rewrite (.) more generally, to see if we can generalize from (->).

-- instance (ProductCat k, Prod k ~ (:*)) => ProductCat (D k) where
--   type Prod (D k) = Prod k
--   exl = linearD exl exl
--   exr = linearD exr exr

-- TODO: Revisit the Prod k ~ (:*) constraint. Maybe just Prod (D k) = Prod k?

instance ProductCat (D s) where
  type Prod (D s) = (:*)
  exl = linearD exl
  exr = linearD exr
  (&&&) = inNew2 $ \ ab bc -> second (uncurry (&&&)) . transposeP . (ab &&& bc)

--   (&&&) = inNew2 $ \ ab bc -> \ a ->
--     let (b,ab') = ab a
--         (c,bc') = bc a
--     in
--       ((b,c), ab' &&& bc')

--   D ab &&& D bc = D $ \ a ->
--     let (b,ab') = ab a
--         (c,bc') = bc a
--     in
--       ((b,c), ab' &&& bc')

--   (&&&) = inNew2 $ \ ab bc -> \ a ->
--     let ((b,ab'),(c,bc')) = (ab &&& bc) a in
--       ((b,c), ab' &&& bc')

--   (&&&) = inNew2 $ \ ab bc -> \ a ->
--     let (bc,(ab',bc')) = (transposeP . (ab &&& bc)) a in
--       (bc, ab' &&& bc')

#if 0

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

#if 0

{--------------------------------------------------------------------
    Generalization
--------------------------------------------------------------------}

type T k a b = Prod k b (M k a b)

newtype M k a b = M (a `k` T k a b)

instance Newtype (M k a b) where
  type O (M k a b) = a `k` T k a b
  pack m = M m
  unpack (M m) = m

instance Ok2 k a b => Additive (M k a b) where
  zero = pack zero
  (^+^) = inNew2 (^+^)

instance Ok2 k a b => Semimodule (M k a b) where
  type Scalar (M k a b) = Scalar a
  (*^) s = inNew ((*^) s)

(.@.) :: (Category k, Ok3 k a b c) => M k b c -> M k a b -> M k a c
(.@.) = inNew2 $ \ bc ab -> second comp' . rassocP . first bc . ab
          -- <+ inOp @(Prod k) @(Ok k) @a @b

comp' :: Ok3 k a b c => (Prod k (M k b c) (M k a b)) `k` M k a c
comp' = undefined -- linear (uncurry (.@.))

-- linearT :: Ok2 k a b => LMap s a b -> M k a b
-- linearT f = pack (f &&& zero)

instance Category k => Category (M k) where
  type Ok (M k) = Ok k
  id  = undefined -- linearT id
  (.) = (.@.)

#endif
