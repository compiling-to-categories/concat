{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DefaultSignatures #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

-- | Constrained categories

module ConCat where

import Prelude hiding (id,(.),curry,uncurry)
import qualified Prelude as P
import Control.Arrow (Kleisli(..),arr)
import qualified Control.Arrow as A
import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import Data.Proxy (Proxy)

import Control.Newtype (pack,unpack)
import GHC.Types (Constraint)

import Data.Constraint hiding ((&&&),(***),(:=>))
import qualified Data.Constraint as C

import Misc hiding ((<~),(~>))

{--------------------------------------------------------------------
    Constraint utilities
--------------------------------------------------------------------}

-- first for entailment
firstC :: (a :- b) -> ((a,c) :- (b,c))
firstC f = Sub (Dict \\ f)

-- second for entailment
secondC :: (c :- d) -> ((a,c) :- (a,d))
secondC g = Sub (Dict \\ g)

infixl 1 <+
-- | Synonym for '(\\)'
(<+) :: a => (b => r) -> (a :- b) -> r
(<+) = (\\)

lassocC :: (a,(b,c)) :- ((a,b),c)
lassocC = secondC weaken1 C.&&& (weaken2 `trans` weaken2)

rassocC :: ((a,b),c) :- (a,(b,c))
rassocC = (weaken1 `trans` weaken1) C.&&& firstC weaken2

{--------------------------------------------------------------------
    Constraints with product consequences
--------------------------------------------------------------------}

type UnitCon con = con ()

class OpCon op (con :: * -> Constraint) where
  inOp :: (con a, con b) :- con (a `op` b)
  -- exOp :: con (a `op` b) :- (con a, con b)

-- Hm. I have no more uses of `exProd`. Consider removing it.

inOpL :: OpCon op con => ((con a,con b),con c) :- con ((a `op` b) `op` c)
inOpL = inOp `trans` firstC  inOp

inOpR :: OpCon op con => (con a,(con b,con c)) :- con (a `op` (b `op` c))
inOpR = inOp `trans` secondC inOp

inOpL' :: OpCon op con =>
           ((con a,con b),con c) :- (con (a `op` b), con ((a `op` b) `op` c))
inOpL' = secondC inOp `trans` rassocC `trans` firstC (contract `trans` inOp)

-- ((con a,con b),con c)
-- (con (a `op` b),con c)
-- ((con (a `op` b),con (a `op` b)),con c)
-- (con (a `op` b),(con (a `op` b),con c))
-- (con (a `op` b),con ((a `op` b) `op` c))

inOpR' :: OpCon op con => (con a,(con b,con c)) :- (con (a `op` (b `op` c)), con (b `op` c))
inOpR' = firstC inOp `trans` lassocC `trans` secondC (contract `trans` inOp)

-- (con a,(con b,con c))
-- (con a,con (b `op` c))
-- (con a,(con (b `op` c),con (b `op` c)))
-- ((con a,con (b `op` c)),con (b `op` c))
-- (con (a `op` (b `op` c)),con (b `op` c))

-- exProdL :: OpCon op con => con ((a `op` b) `op` c) :- ((con a,con b),con c)
-- exProdL = firstC  exProd `trans` exProd

-- exProdR :: OpCon op con => con (a `op` (b `op` c)) :- (con a,(con b,con c))
-- exProdR = secondC exProd `trans` exProd

instance OpCon op Yes where
  -- unit   = Sub Dict
  inOp = Sub Dict
  -- exProd = Sub Dict

{--------------------------------------------------------------------
    Categories
--------------------------------------------------------------------}

class Category (k :: u -> u -> *) where
  type Ok k :: u -> Constraint
  type Ok k = Yes
  id  :: Ok k a => a `k` a
  infixr 9 .
  (.) :: (Ok k a, Ok k b, Ok k c) =>
         b `k` c -> a `k` b -> a `k` c

type CatOk k ok = (Category k, ok ~ Ok k)

infixl 1 <~
infixr 1 ~>
-- | Add post- and pre-processing
(<~) :: (Category k, Ok k a, Ok k b, Ok k a', Ok k b') =>
        (b `k` b') -> (a' `k` a) -> ((a `k` b) -> (a' `k` b'))
(h <~ f) g = h . g . f

-- -- Alternatively,
-- 
-- (<~) :: (CatOk k ok, ok a, ok b, ok a', ok b') =>
--         (b `k` b') -> (a' `k` a) -> ((a `k` b) -> (a' `k` b'))

-- | Add pre- and post-processing
(~>) :: (Category k, Ok k a, Ok k b, Ok k a', Ok k b') =>
        (a' `k` a) -> (b `k` b') -> ((a `k` b) -> (a' `k` b'))
f ~> h = h <~ f

instance Category (->) where
  id  = P.id
  (.) = (P..)

instance Monad m => Category (Kleisli m) where
  id  = Kleisli return
  (.) = inNew2 (<=<)

{--------------------------------------------------------------------
    Products
--------------------------------------------------------------------}

-- Experiment:
#define InProd inOp @(Prod k) @(Ok k)

infixr 3 ***, &&&

-- | Category with product.
class (OpCon (Prod k) (Ok k), Category k) => ProductCat k where
  type Prod k :: * -> * -> *
  type Prod k = (:*)
  exl :: (Ok k a, Ok k b) => Prod k a b `k` a
  exr :: (Ok k a, Ok k b) => Prod k a b `k` b
  dup :: (Ok k a) => a `k` Prod k a a
  dup = id &&& id
  swapP :: forall a b. (Ok k a, Ok k b) => Prod k a b `k` Prod k b a
  swapP =  exr &&& exl  <+ InProd @a @b
                           -- inOp @(Prod k) @(Ok k) @a @b
  (***) :: forall a b c d. (Ok k a, Ok k b, Ok k c, Ok k d) =>
           (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
  f *** g = f . exl &&& g . exr  <+ inOp @(Prod k) @(Ok k) @a @b
  (&&&) :: forall a c d. (Ok k a, Ok k c, Ok k d) =>
           (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)
  f &&& g = (f *** g) . dup
    <+ inOp @(Prod k) @(Ok k) @a @a
    <+ inOp @(Prod k) @(Ok k) @c @d
  first :: forall a a' b. (Ok k a, Ok k b, Ok k a') =>
           (a `k` a') -> (Prod k a b `k` Prod k a' b)
  first = (*** id)
  second :: forall a b b'. (Ok k a, Ok k b, Ok k b') =>
            (b `k` b') -> (Prod k a b `k` Prod k a b')
  second =  (id ***)
  lassocP :: forall a b c. (Ok k a, Ok k b, Ok k c)
          => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c
  lassocP = second exl &&& (exr . exr)
    <+ inOp   @(Prod k) @(Ok k) @a @b
    <+ inOpR' @(Prod k) @(Ok k) @a @b @c
  rassocP :: forall a b c. (Ok k a, Ok k b, Ok k c)
          => Prod k (Prod k a b) c `k` Prod k a (Prod k b c)
  rassocP =  (exl . exl) &&& first  exr
    <+ inOp   @(Prod k) @(Ok k) @b @c
    <+ inOpL' @(Prod k) @(Ok k) @a @b @c
  {-# MINIMAL exl, exr, ((&&&) | ((***), dup)) #-}

-- TODO: reconcile differences between lassocP/rassocP and lassocS/rassocS

-- TODO: find some techniques for prettifying type operators.

-- Alternatively:
-- 
--   lassocP = second exl &&& (exr . exr)
--     <+ (inOp :: (Ok k b, Ok k c) :- Ok k Prod k b c)
--   rassocP =  (exl . exl) &&& first  exr
--     <+ (inOp :: (Ok k a, Ok k b) :- Ok k Prod k a b)

type ProdOk k ok = (ProductCat k, ok ~ Ok k)

instance ProductCat (->) where
  exl        = fst
  exr        = snd
  (&&&)      = (A.&&&)
  (***)      = (A.***)
  first      = A.first
  second     = A.second
  lassocP    = \ (a,(b,c)) -> ((a,b),c)
  rassocP    = \ ((a,b),c) -> (a,(b,c))
  
-- | Apply to both parts of a product
twiceP :: (ProductCat k, Ok k a, Ok k c) =>
          (a `k` c) -> Prod k a a `k` (Prod k c c)
twiceP f = f *** f

-- Why doesn't the PRO macro get expanded in the next two definitions?
-- "Not in scope: type constructor or class ‘PRO’"

-- | Operate on left-associated form
inLassocP :: forall k a b c a' b' c'.
             ProductCat k =>
             (Ok k a, Ok k b, Ok k c, Ok k a', Ok k b', Ok k c') =>
             Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
          -> Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))
inLassocP = rassocP <~ lassocP
              <+ inOpL @(Prod k) @(Ok k) @a  @b  @c
              <+ inOpL @(Prod k) @(Ok k) @a' @b' @c'
              <+ inOpR @(Prod k) @(Ok k) @a  @b  @c
              <+ inOpR @(Prod k) @(Ok k) @a' @b' @c'

-- | Operate on right-associated form
inRassocP :: forall a b c a' b' c' k.
             ProductCat k =>
             (Ok k a, Ok k b, Ok k c, Ok k a', Ok k b', Ok k c') =>
             Prod k a (Prod k b c) `k` (Prod k a' (Prod k b' c'))
          -> Prod k (Prod k a b) c `k` Prod k (Prod k a' b') c'
inRassocP = lassocP <~ rassocP
              <+ inOpL @(Prod k) @(Ok k) @a  @b  @c
              <+ inOpL @(Prod k) @(Ok k) @a' @b' @c'
              <+ inOpR @(Prod k) @(Ok k) @a  @b  @c
              <+ inOpR @(Prod k) @(Ok k) @a' @b' @c'

transposeP :: forall k a b c d. (ProductCat k, Ok k a, Ok k b, Ok k c, Ok k d)
           => Prod k (Prod k a b) (Prod k c d) `k` Prod k (Prod k a c) (Prod k b d)
transposeP = (exl.exl &&& exl.exr) &&& (exr.exl &&& exr.exr)
  <+ inOp @(Prod k) @(Ok k) @(Prod k a b) @(Prod k c d)
  <+ inOp @(Prod k) @(Ok k) @c @d
  <+ inOp @(Prod k) @(Ok k) @a @b
  <+ inOp @(Prod k) @(Ok k) @b @d
  <+ inOp @(Prod k) @(Ok k) @a @c

-- transposeS :: CoproductCat k => ((p :+ q) :+ (r :+ s)) `k` ((p :+ r) :+ (q :+ s))
-- transposeS = (inl.inl ||| inr.inl) ||| (inl.inr ||| inr.inr)

-- class Ok k () => TerminalCat k where
--   it :: Ok k a => a `k` Unit

instance Monad m => ProductCat (Kleisli m) where
  type Prod (Kleisli m) = (:*)
  exl   = arr exl
  exr   = arr exr
  dup   = arr dup
  (***) = inNew2 crossA

crossA :: Applicative m => (a -> m c) -> (b -> m d) -> (a :* b -> m (c :* d))
(f `crossA` g) (a,b) = liftA2 (,) (f a) (g b)

{--------------------------------------------------------------------
    Coproducts
--------------------------------------------------------------------}

infixr 2 +++, |||

-- | Category with coproduct.
class (OpCon (Coprod k) (Ok k), Category k) => CoproductCat k where
  type Coprod k :: * -> * -> *
  type Coprod k = (:+)
  inl :: (Ok k a, Ok k b) => a `k` Coprod k a b
  inr :: (Ok k a, Ok k b) => b `k` Coprod k a b
  jam :: (Ok k a) => Coprod k a a `k` a
  jam = id ||| id
  swapS :: forall a b. (Ok k a, Ok k b) => Coprod k a b `k` Coprod k b a
  swapS =  inr ||| inl  <+ inOp @(Coprod k) @(Ok k) @b @a
  (+++) :: forall a b c d. (Ok k a, Ok k b, Ok k c, Ok k d) =>
           (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b)
  f +++ g = inl . f ||| inr . g  <+ inOp @(Coprod k) @(Ok k) @a @b
  (|||) :: forall a c d. (Ok k a, Ok k c, Ok k d) =>
           (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a)
  f ||| g = jam . (f +++ g)
    <+ inOp @(Coprod k) @(Ok k) @a @a
    <+ inOp @(Coprod k) @(Ok k) @c @d
  left :: forall a a' b. (Ok k a, Ok k b, Ok k a') =>
          (a `k` a') -> (Coprod k a b `k` Coprod k a' b)
  left = (+++ id)
  right :: forall a b b'. (Ok k a, Ok k b, Ok k b') =>
           (b `k` b') -> (Coprod k a b `k` Coprod k a b')
  right = (id +++)
  lassocS :: forall a b c. (Ok k a, Ok k b, Ok k c)
          => Coprod k a (Coprod k b c) `k` Coprod k (Coprod k a b) c
  lassocS = inl.inl ||| (inl.inr ||| inr)
    <+ inOpL' @(Coprod k) @(Ok k) @a @b @c
    <+ inOpR' @(Coprod k) @(Ok k) @a @b @c
  rassocS :: forall a b c. (Ok k a, Ok k b, Ok k c)
          => Coprod k (Coprod k a b) c `k` Coprod k a (Coprod k b c)
  rassocS = (inl ||| inr.inl) ||| inr.inr
    <+ inOpR' @(Coprod k) @(Ok k) @a @b @c
    <+ inOpL' @(Coprod k) @(Ok k) @a @b @c

{--------------------------------------------------------------------
    Exponentials
--------------------------------------------------------------------}

class ProductCat k => ClosedCat k where
  type Exp k :: * -> * -> *
--   apply   :: (Ok k a, Ok k b        ) => Prod k (Exp k a b) a `k` b
  curry   :: (Ok k a, Ok k b, Ok k c) => (Prod k a b `k` c) -> (a `k` Exp k b c)
  uncurry :: (Ok k a, Ok k b, Ok k c) => (a `k` Exp k b c) -> (Prod k a b `k` c)

  apply   :: (Ok k a, Ok k b, p ~ Prod k, e ~ Exp k) => ((a `e` b) `p` a) `k` b

instance ClosedCat (->) where
  type Exp (->) = (->)
  apply (f,a) = f a
  curry       = P.curry
  uncurry     = P.uncurry

applyK   ::            Kleisli m (Kleisli m a b :* a) b
curryK   :: Monad m => Kleisli m (a :* b) c -> Kleisli m a (Kleisli m b c)
uncurryK :: Monad m => Kleisli m a (Kleisli m b c) -> Kleisli m (a :* b) c

applyK   = pack (apply . first unpack)
curryK   = inNew $ \ h -> return . pack . curry h
uncurryK = inNew $ \ f -> \ (a,b) -> f a >>= ($ b) . unpack

instance Monad m => ClosedCat (Kleisli m) where
  type Exp (Kleisli m) = Kleisli m
  apply   = applyK
  curry   = curryK
  uncurry = uncurryK

{--------------------------------------------------------------------
    Other
--------------------------------------------------------------------}

class TerminalCat k where
  it :: (Ok k a, Ok k ()) => a `k` Unit

instance TerminalCat (->) where it = const ()

-- | Categories with constant arrows (generalized elements)
class ConstCat k where
  konst :: forall a b. (Ok k a, Ok k b) => b -> (a `k` b)

instance ConstCat (->) where konst = const
