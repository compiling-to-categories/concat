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

-- | Constrained categories

module ConCat where

import Prelude hiding (id,(.),curry,uncurry)
import qualified Prelude as P
import Control.Arrow (Kleisli)
import qualified Control.Arrow as A

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

class ProdCon (con :: * -> Constraint) where
  inProd :: (con a, con b) :- con (a :* b)
  -- exProd :: con (a :* b) :- (con a, con b)

-- Hm. I have no more uses of `exProd`. Consider removing it.

inProdL :: ProdCon con => ((con a,con b),con c) :- con ((a,b),c)
inProdL = inProd `trans` firstC  inProd

inProdR :: ProdCon con => (con a,(con b,con c)) :- con (a,(b,c))
inProdR = inProd `trans` secondC inProd

inProdL' :: ProdCon con =>
           ((con a,con b),con c) :- (con (a,b), con ((a,b),c))
inProdL' = secondC inProd `trans` rassocC `trans` firstC (contract `trans` inProd)

-- ((con a,con b),con c)
-- (con (a,b),con c)
-- ((con (a,b),con (a,b)),con c)
-- (con (a,b),(con (a,b),con c))
-- (con (a,b),con ((a,b),c))

inProdR' :: ProdCon con => (con a,(con b,con c)) :- (con (a,(b,c)), con (b,c))
inProdR' = firstC inProd `trans` lassocC `trans` secondC (contract `trans` inProd)

-- (con a,(con b,con c))
-- (con a,con (b,c))
-- (con a,(con (b,c),con (b,c)))
-- ((con a,con (b,c)),con (b,c))
-- (con (a,(b,c)),con (b,c))

-- exProdL :: ProdCon con => con ((a,b),c) :- ((con a,con b),con c)
-- exProdL = firstC  exProd `trans` exProd

-- exProdR :: ProdCon con => con (a,(b,c)) :- (con a,(con b,con c))
-- exProdR = secondC exProd `trans` exProd

instance ProdCon Yes where
  -- unit   = Sub Dict
  inProd = Sub Dict
  -- exProd = Sub Dict

{--------------------------------------------------------------------
    Category classes
--------------------------------------------------------------------}

infixr 9 .

class Category (k :: u -> u -> *) where
  type Ok k :: u -> Constraint
  type Ok k = Yes
  id  :: Ok k a => a `k` a
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

infixr 3 ***, &&&

-- | Category with product.
-- TODO: Generalize '(:*)' to an associated type.
class (ProdCon (Ok k), Category k) => ProductCat k where
  exl :: (Ok k a, Ok k b) => (a :* b) `k` a
  exr :: (Ok k a, Ok k b) => (a :* b) `k` b
  dup :: Ok k a => a `k` (a :* a)
  dup = id &&& id
  swapP :: forall a b. (Ok k a, Ok k b) => (a :* b) `k` (b :* a)
  swapP =  exr &&& exl  <+ inProd @(Ok k) @a @b
  (***) :: forall a b c d. (Ok k a, Ok k b, Ok k c, Ok k d) =>
           (a `k` c) -> (b `k` d) -> ((a :* b) `k` (c :* d))
  f *** g = f . exl &&& g . exr  <+ inProd @(Ok k) @a @b
  (&&&) :: forall a c d. (Ok k a, Ok k c, Ok k d) =>
           (a `k` c) -> (a `k` d) -> (a `k` (c :* d))
  f &&& g = (f *** g) . dup
    <+ inProd @(Ok k) @a @a
    <+ inProd @(Ok k) @c @d
  first :: forall a a' b. (Ok k a, Ok k b, Ok k a') =>
           (a `k` a') -> ((a :* b) `k` (a' :* b))
  first = (*** id)
  second :: forall a b b'. (Ok k a, Ok k b, Ok k b') =>
            (b `k` b') -> ((a :* b) `k` (a :* b'))
  second =  (id ***)
  lassocP :: forall a b c. (Ok k a, Ok k b, Ok k c)
          => (a :* (b :* c)) `k` ((a :* b) :* c)
  lassocP = second exl &&& (exr . exr)
    <+ inProd   @(Ok k) @a @b
    <+ inProdR' @(Ok k) @a @b @c
  rassocP :: forall a b c. (Ok k a, Ok k b, Ok k c)
          => ((a :* b) :* c) `k` (a :* (b :* c))
  rassocP =  (exl . exl) &&& first  exr
    <+ inProd   @(Ok k) @b @c
    <+ inProdL' @(Ok k) @a @b @c
  {-# MINIMAL exl, exr, ((&&&) | ((***), dup)) #-}

-- TODO: tweak inProdL to generate both con (a :* b) and con ()

-- Alternatively:
-- 
--   lassocP = second exl &&& (exr . exr)
--     <+ (inProd :: (Ok k b, Ok k c) :- Ok k (b :* c))
--   rassocP =  (exl . exl) &&& first  exr
--     <+ (inProd :: (Ok k a, Ok k b) :- Ok k (a :* b))

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
          (a `k` c) -> ((a :* a) `k` (c :* c))
twiceP f = f *** f

-- | Operate on left-associated form
inLassocP :: forall k a b c a' b' c'.
             ProductCat k =>
             (Ok k a, Ok k b, Ok k c, Ok k a', Ok k b', Ok k c') =>
             (((a :* b) :* c) `k` ((a' :* b') :* c'))
          -> ((a :* (b :* c)) `k` (a' :* (b' :* c')))
inLassocP = rassocP <~ lassocP
              <+ inProdL @(Ok k) @a  @b  @c
              <+ inProdL @(Ok k) @a' @b' @c'
              <+ inProdR @(Ok k) @a  @b  @c
              <+ inProdR @(Ok k) @a' @b' @c'

-- | Operate on right-associated form
inRassocP :: forall a b c a' b' c' k.
             ProductCat k =>
             (Ok k a, Ok k b, Ok k c, Ok k a', Ok k b', Ok k c') =>
             ((a :* (b :* c)) `k` (a' :* (b' :* c')))
          -> (((a :* b) :* c) `k` ((a' :* b') :* c'))
inRassocP = lassocP <~ rassocP
              <+ inProdL @(Ok k) @a  @b  @c
              <+ inProdL @(Ok k) @a' @b' @c'
              <+ inProdR @(Ok k) @a  @b  @c
              <+ inProdR @(Ok k) @a' @b' @c'

transposeP :: forall k a b c d. (ProductCat k, Ok k a, Ok k b, Ok k c, Ok k d)
           => ((a :* b) :* (c :* d)) `k` ((a :* c) :* (b :* d))
transposeP = (exl.exl &&& exl.exr) &&& (exr.exl &&& exr.exr)
  <+ inProd @(Ok k) @(a :* b) @(c :* d)
  <+ inProd @(Ok k) @c @d
  <+ inProd @(Ok k) @a @b
  <+ inProd @(Ok k) @b @d
  <+ inProd @(Ok k) @a @c

-- transposeS :: CoproductCat k => ((p :+ q) :+ (r :+ s)) `k` ((p :+ r) :+ (q :+ s))
-- transposeS = (inl.inl ||| inr.inl) ||| (inl.inr ||| inr.inr)

-- class Ok k () => TerminalCat k where
--   it :: Ok k a => a `k` Unit

class TerminalCat k where
  it :: (Ok k a, Ok k ()) => a `k` Unit

instance TerminalCat (->) where it = const ()

-- | Categories with constant arrows (generalized elements)
class ConstCat k where
  konst :: forall a b. (Ok k a, Ok k b) => b -> (a `k` b)

instance ConstCat (->) where konst = const


class ProductCat k => ClosedCat k where
  apply   :: ((a :=> b) :* a) `k` b
  curry   :: ((a :* b) `k` c) -> (a `k` (b :=> c))
  uncurry :: (a `k` (b :=> c)) -> ((a :* b) `k` c)

instance ClosedCat (->) where
  apply (f,a) = f a
  curry       = P.curry
  uncurry     = P.uncurry

applyK   ::            Kleisli m (Kleisli m a b :* a) b
curryK   :: Monad m => Kleisli m (a :* b) c -> Kleisli m a (Kleisli m b c)
uncurryK :: Monad m => Kleisli m a (Kleisli m b c) -> Kleisli m (a :* b) c

applyK   = pack (apply . first unpack)
curryK   = inNew $ \ h -> return . pack . curry h
uncurryK = inNew $ \ f -> \ (a,b) -> f a >>= ($ b) . unpack
