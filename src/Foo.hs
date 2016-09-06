{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Tries as category

module TrieCat where

import Prelude hiding (id,(.),curry,uncurry)
import qualified Prelude as P
import Control.Arrow (Kleisli(..),arr)
import qualified Control.Arrow as A
import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import qualified Control.Category as Cat
-- import Data.Constraint (Dict(..),(:-)(..))
import Control.Newtype
import GHC.Types (Constraint)
import Data.MemoTrie

import Data.VectorSpace
import Data.LinearMap
import Data.Basis

import Data.Constraint hiding ((&&&),(***),(:=>))
import qualified Data.Constraint as C

import Misc hiding ((<~))
-- import ConCat

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- type C1 (con :: u -> Constraint) a = con a

-- type C2 con a b         = (C1 con a, con b)

type C2 (con :: u -> Constraint) a b = (con a, con b)

type C3 con a b c       = (C2 con a b, con c)
type C4 con a b c d     = (C3 con a b c, con d)
type C5 con a b c d e   = (C4 con a b c d, con e)
type C6 con a b c d e f = (C5 con a b c d e, con f)

type Ok2 k a b         = C2 (Ok k) a b
type Ok3 k a b c       = C3 (Ok k) a b c
type Ok4 k a b c d     = C4 (Ok k) a b c d
type Ok5 k a b c d e   = C5 (Ok k) a b c d e
type Ok6 k a b c d e f = C6 (Ok k) a b c d e f


infixr 1 |-
type (|-) = (:-)

infixl 1 <+
-- | Synonym for '(\\)'
(<+) :: (b => r) -> (a :- b) -> (a => r)
(<+) = (\\)

-- (<+) :: a => (b => r) -> (a :- b) -> r

-- Experiment with a flipped (<+). entail p . entail q
entail :: (a :- b) -> (b => r) -> (a => r)
entail = flip (<+)

-- first for entailment
firstC :: (a :- b) -> ((a,c) :- (b,c))
firstC f = Sub (Dict <+ f)

-- second for entailment
secondC :: (c :- d) -> ((a,c) :- (a,d))
secondC g = Sub (Dict <+ g)

lassocC :: (a,(b,c)) :- ((a,b),c)
lassocC = secondC weaken1 C.&&& (weaken2 `trans` weaken2)

rassocC :: ((a,b),c) :- (a,(b,c))
rassocC = (weaken1 `trans` weaken1) C.&&& firstC weaken2

{--------------------------------------------------------------------
    Category
--------------------------------------------------------------------}

class Category (k :: u -> u -> *) where
  type Ok k :: u -> Constraint
  type Ok k = Yes
  id  :: Ok k a => a `k` a
  infixr 9 .
  (.) :: Ok3 k a b c => b `k` c -> a `k` b -> a `k` c
#if 1
  -- Defaults experiment
  default id :: Cat.Category k => a `k` a
  id = Cat.id
  default (.) :: Cat.Category k => b `k` c -> a `k` b -> a `k` c
  (.) = (Cat..)
#endif

instance Category (->) where
  id  = P.id
  (.) = (P..)

instance Monad m => Category (Kleisli m) where
  id  = pack return
  (.) = inNew2 (<=<)

infixl 1 <~
infixr 1 ~>
-- | Add post- and pre-processing
(<~) :: (Category k, Ok4 k a b a' b') =>
        (b `k` b') -> (a' `k` a) -> ((a `k` b) -> (a' `k` b'))
(h <~ f) g = h . g . f

-- | Add pre- and post-processing
(~>) :: (Category k, Ok4 k a b a' b') =>
        (a' `k` a) -> (b `k` b') -> ((a `k` b) -> (a' `k` b'))
f ~> h = h <~ f

{--------------------------------------------------------------------
    Products
--------------------------------------------------------------------}

infixr 3 ***, &&&

#if 0

-- | Category with product.
-- TODO: Generalize '(:*)' to an associated type.
class Category k => ProductCat k where
  exl :: Ok2 k a b => (a :* b) `k` a
  exr :: Ok2 k a b => (a :* b) `k` b
--   dup :: Ok k a => a `k` (a :* a)
--   dup = id &&& id
--   swapP :: Ok2 k a => (a :* b) `k` (b :* a)
--   swapP =  exr &&& exl
--   (***) :: (a `k` c) -> (b `k` d) -> ((a :* b) `k` (c :* d))
--   f@OK *** g@OK = f . exl &&& g . exr
  (&&&) :: Ok3 k a c d => a `k` c -> a `k` d -> a `k` (c :* d)
--   f@OK &&& g = (f *** g) . dup
--   first :: Ok k b => (a `k` a') -> ((a :* b) `k` (a' :* b))
--   first = (*** id)
--   second :: Ok k a => (b `k` b') -> ((a :* b) `k` (a :* b'))
--   second =  (id ***)
--   lassocP :: forall a b c. Ok3 k a b c
--           => (a :* (b :* c)) `k` ((a :* b) :* c)
--   lassocP | OKAY <- okayProd :: OD k (b :* c)
--           = second exl &&& (exr . exr)
--   rassocP :: forall a b c. Ok3 k a b c
--           => ((a :* b) :* c) `k` (a :* (b :* c))
--   rassocP | OKAY <- okayProd :: OD k (a :* b)
--           =  (exl . exl) &&& first  exr

-- infixr 2 +++, |||

#elif 1

inO :: forall op con a b r. OpCon op con => (con (a `op` b) => r) -> (C2 con a b => r)
inO = (\\ inOp @op @con @a @b)

inOL :: forall op con a b c r. OpCon op con
     => (con ((a `op` b) `op` c) => r) -> (C3 con a b c => r)
inOL r = inO @op @con @a @b $ inO @op @con @(a `op` b) @c $ r
-- inOL = inP @con @a @b . inP @con @(a :* b) @c -- nope

-- inOR :: forall con a b c r. (ProdCon con,C3 con a b c) => (con (a :* (b :* c)) => r) -> r
-- inOR = (\\ inProdR @con @a @b @c)

inOR :: forall op con a b c r. OpCon op con
     => (con (a `op` (b `op` c)) => r) -> (C3 con a b c => r)
inOR r = inO @op @con @b @c $ inO @op @con @a @(b `op` c) $ r
-- inOR = inO @op @con @b @c . inO @op @con @a @(b `op` c) -- nope


inOLR :: forall op con a b c r. OpCon op con
     => (con (a `op` (b `op` c)) => con ((a `op` b) `op` c) => r)
     -> (C3 con a b c => r)
inOLR r = inOL @op @con @a @b @c $ inOR @op @con @a @b @c $ r

-- | Category with product.
-- TODO: Generalize '(:*)' to an associated type.
class (Category k, OpCon (:*) (Ok k)) => ProductCat (k {-:: u -> u -> *-}) where
  exl :: Ok2 k a b => (a :* b) `k` a
  exr :: Ok2 k a b => (a :* b) `k` b
  dup :: Ok k a => a `k` (a :* a)
  dup = id &&& id
  swapP :: forall a b. Ok2 k a b => (a :* b) `k` (b :* a)
  swapP =  exr &&& exl  <+ inOp @(:*) @(Ok k) @a @b
  (***) :: forall a b c d. Ok4 k a b c d
        => a `k` c -> b `k` d -> (a :* b) `k` (c :* d)
  f *** g = f . exl &&& g . exr
    <+ inOp @(:*) @(Ok k) @a @b
--   f *** g = inP @(Ok k) @a @b (f . exl &&& g . exr)
  (&&&) :: forall a c d. Ok3 k a c d
        => a `k` c -> a `k` d -> a `k` (c :* d)
  f &&& g = (f *** g) . dup
    <+ inOp @(:*) @(Ok k) @a @a
    <+ inOp @(:*) @(Ok k) @c @d
--   f &&& g = (f *** g) . dup
--     <+ (inOp @(:*) @(Ok k) @a @a C.*** inOp @(:*) @(Ok k) @c @d)
  first :: Ok3 k a b a' => (a `k` a') -> ((a :* b) `k` (a' :* b))
  first = (*** id)
  second :: Ok3 k a b b' => (b `k` b') -> ((a :* b) `k` (a :* b'))
  second =  (id ***)
  lassocP :: forall a b c. Ok3 k a b c
          => (a :* (b :* c)) `k` ((a :* b) :* c)
  lassocP = second exl &&& (exr . exr)
--     <+ inOp @(:*) @(Ok k) @a @(b :* c)
--     <+ inOp @(:*) @(Ok k) @b @c
--     <+ inOp @(:*) @(Ok k) @a @b
    <+ inOp   @(:*)   @(Ok k) @a @b
    <+ inOpR' @(:*) @(Ok k) @a @b @c
  rassocP :: forall a b c. Ok3 k a b c
          => ((a :* b) :* c) `k` (a :* (b :* c))
  rassocP =  (exl . exl) &&& first  exr
--     <+ inProd   @(Ok k) @b @c
--     <+ inOpL' @(Ok k) @a @b @c
    <+ inOp @(:*) @(Ok k) @(a :* b) @c
    <+ inOp @(:*) @(Ok k) @b @c
    <+ inOp @(:*) @(Ok k) @a @b
  {-# MINIMAL exl, exr, ((&&&) | ((***), dup)) #-}
#else
infixr 3 ***, &&&

-- | Category with product.
class Category k => ProductCat k where
  type Prod k :: * -> * -> *
  type Prod k = (:*)
  exl :: Ok2 k a b => Prod k a b `k` a
  exr :: Ok2 k a b => Prod k a b `k` b
  dup :: Ok k a => a `k` Prod k a a
  dup = id &&& id
  swapP :: forall a b. Ok2 k a b => Prod k a b `k` Prod k b a
  swapP =  exr &&& exl  <+ InProd @a @b
                           -- inOp @(:*) @(Ok k) @a @b
  (***) :: forall a b c d. Ok4 k a b c d =>
           (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
  f *** g = f . exl &&& g . exr  <+ inOp @(:*) @(Ok k) @a @b
  (&&&) :: forall a c d. Ok3 k a c d =>
           (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)
  f &&& g = (f *** g) . dup
    <+ inOp @(:*) @(Ok k) @a @a
    <+ inOp @(:*) @(Ok k) @c @d
  first :: forall a a' b. Ok3 k a b a' =>
           (a `k` a') -> (Prod k a b `k` Prod k a' b)
  first = (*** id)
  second :: forall a b b'. Ok3 k a b b' =>
            (b `k` b') -> (Prod k a b `k` Prod k a b')
  second =  (id ***)
  lassocP :: forall a b c. Ok3 k a b c
          => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c
  lassocP = second exl &&& (exr . exr)
    <+ inOp   @(Prod k) @(Ok k) @a @b
    <+ inOpR' @(Prod k) @(Ok k) @a @b @c
  rassocP :: forall a b c. Ok3 k a b c
          => Prod k (Prod k a b) c `k` Prod k a (Prod k b c)
  rassocP =  (exl . exl) &&& first  exr
    <+ inOp   @(Prod k) @(Ok k) @b @c
    <+ inOpL' @(Prod k) @(Ok k) @a @b @c
  {-# MINIMAL exl, exr, ((&&&) | ((***), dup)) #-}
#endif

-- | Operate on left-associated form
inLassocP :: forall k a b c a' b' c'. (ProductCat k, Ok6 k a b c a' b' c')
          => ((a :* b) :* c) `k` ((a' :* b') :* c')
          -> (a :* (b :* c)) `k` (a' :* (b' :* c'))

-- inLassocP = inOLR @(:*) @(Ok k) @a  @b  @c  $
--             inOLR @(:*) @(Ok k) @a' @b' @c' $
--             rassocP <~ lassocP

inLassocP = rassocP <~ lassocP
              <+ (inOpLR @(:*) @(Ok k) @a  @b  @c C.***
                  inOpLR @(:*) @(Ok k) @a' @b' @c')

-- inLassocP = rassocP <~ lassocP
--               <+ inOpL @(:*) @(Ok k) @a  @b  @c
--               <+ inOpL @(:*) @(Ok k) @a' @b' @c'
--               <+ inOpR @(:*) @(Ok k) @a  @b  @c
--               <+ inOpR @(:*) @(Ok k) @a' @b' @c'

-- inLassocP = rassocP <~ lassocP
--               <+ inOp @(:*) @(Ok k) @(a' :* b') @c' <+ inOp @(:*) @(Ok k) @a' @b'
--               <+ inOp @(:*) @(Ok k) @(a  :* b ) @c  <+ inOp @(:*) @(Ok k) @a  @b
--               <+ inOp @(:*) @(Ok k) @a' @(b' :* c') <+ inOp @(:*) @(Ok k) @b' @c'
--               <+ inOp @(:*) @(Ok k) @a  @(b  :* c ) <+ inOp @(:*) @(Ok k) @b  @c


-- | Operate on right-associated form
inRassocP :: forall k a b c a' b' c'. (ProductCat k, Ok6 k a b c a' b' c')
          => (a :* (b :* c)) `k` (a' :* (b' :* c'))
          -> ((a :* b) :* c) `k` ((a' :* b') :* c')

inRassocP = inOLR @(:*) @(Ok k) @a  @b  @c  $
            inOLR @(:*) @(Ok k) @a' @b' @c' $
            lassocP <~ rassocP

-- inRassocP = lassocP <~ rassocP
--               <+ inOpLR @(:*) @(Ok k) @a  @b  @c
--               <+ inOpLR @(:*) @(Ok k) @a' @b' @c'

-- inRassocP = lassocP <~ rassocP
--               <+ (inOpLR @(:*) @(Ok k) @a  @b  @c C.***
--                   inOpLR @(:*) @(Ok k) @a' @b' @c')

-- inRassocP = inAssocs @(:*) @(Ok k) @a  @b  @c  $
--             inAssocs @(:*) @(Ok k) @a' @b' @c' $
--             lassocP <~ rassocP

-- inRassocP = lassocP <~ rassocP
--               <+ inOpL @(:*) @(Ok k) @a  @b  @c
--               <+ inOpL @(:*) @(Ok k) @a' @b' @c'
--               <+ inOpR @(:*) @(Ok k) @a  @b  @c
--               <+ inOpR @(:*) @(Ok k) @a' @b' @c'

-- inRassocP = lassocP <~ rassocP
--               <+ inOp @(:*) @(Ok k) @a' @(b' :* c') <+ inOp @(:*) @(Ok k) @b' @c'
--               <+ inOp @(:*) @(Ok k) @a  @(b  :* c ) <+ inOp @(:*) @(Ok k) @b  @c
--               <+ inOp @(:*) @(Ok k) @(a' :* b') @c' <+ inOp @(:*) @(Ok k) @a' @b'
--               <+ inOp @(:*) @(Ok k) @(a  :* b ) @c  <+ inOp @(:*) @(Ok k) @a  @b

inAssocs :: forall op con a b c r.
             (OpCon op con, C3 con a b c) =>
             (C2 con ((a `op` b) `op` c) (a `op` (b `op` c)) => r) -> r
-- inAssocs = inOL @op @con @a @b @c . inOR @op @con @a @b @c
-- inAssocs r = inOL @op @con @a @b @c (inOR @op @con @a @b @c r)
inAssocs r = inOL @op @con @a @b @c (inOR @op @con @a @b @c r)

instance ProductCat (->) where
  exl        = fst
  exr        = snd
  (&&&)      = (A.&&&)
--   (***)      = (A.***)
--   first      = A.first
--   second     = A.second
--   lassocP    = \ (a,(b,c)) -> ((a,b),c)
--   rassocP    = \ ((a,b),c) -> (a,(b,c))

instance Monad m => ProductCat (Kleisli m) where
  exl   = arr fst
  exr   = arr snd
  (&&&) = (A.&&&)

infixr 2 +++, |||

#if 0
-- | Category with coproduct.
class Category k => CoproductCat k where
  inl :: Ok2 k a b => a `k` (a :+ b)
  inr :: Ok2 k a b => b `k` (a :+ b)
  (|||) :: forall a c d. Ok3 k a c d =>
           c `k` a -> d `k` a -> (c :+ d) `k` a
#else

-- | Category with coproduct.
class (OpCon (:+) (Ok k), Category k) => CoproductCat k where
  inl :: Ok2 k a b => a `k` (a :+ b)
  inr :: Ok2 k a b => b `k` (a :+ b)
  jam :: Ok k a => (a :+ a) `k` a
  jam = id ||| id
  swapS :: forall a b. Ok2 k a b => (a :+ b) `k` (b :+ a)
  swapS =  inr ||| inl  <+ inOp @(:+) @(Ok k) @b @a
  (+++) :: forall a b c d. Ok4 k a b c d
        => (c `k` a) -> (d `k` b) -> ((c :+ d) `k` (a :+ b))
  f +++ g = inl . f ||| inr . g  <+ inOp @(:+) @(Ok k) @a @b
  (|||) :: forall a c d. Ok3 k a c d
        => (c `k` a) -> (d `k` a) -> ((c :+ d) `k` a)
  f ||| g = jam . (f +++ g)
    <+ inOp @(:+) @(Ok k) @a @a
    <+ inOp @(:+) @(Ok k) @c @d
  left :: forall a a' b. Ok3 k a b a'
       => (a `k` a') -> ((a :+ b) `k` (a' :+ b))
  left = (+++ id)
  right :: forall a b b'. Ok3 k a b b'
        => (b `k` b') -> ((a :+ b) `k` (a :+ b'))
  right = (id +++)
  lassocS :: forall a b c. Ok3 k a b c
          => (a :+ (b :+ c)) `k` ((a :+ b) :+ c)
  lassocS = inl.inl ||| (inl.inr ||| inr)
    <+ inOp @(:+) @(Ok k) @(a :+ b) @c
    <+ inOp @(:+) @(Ok k) @b @c
    <+ inOp @(:+) @(Ok k) @a @b
  rassocS :: forall a b c. Ok3 k a b c
          => ((a :+ b) :+ c) `k` (a :+ (b :+ c))
  rassocS = (inl ||| inr.inl) ||| inr.inr
    <+ inOp @(:+) @(Ok k) @a @(b :+ c)
    <+ inOp @(:+) @(Ok k) @b @c
    <+ inOp @(:+) @(Ok k) @a @b
  {-# MINIMAL inl, inr, ((|||) | ((|||), jam)) #-}

-- | Operate on left-associated form
inLassocS :: forall k a b c a' b' c'.
             (CoproductCat k, Ok6 k a b c a' b' c') =>
             ((a :+ b) :+ c) `k` ((a' :+ b') :+ c')
          -> (a :+ (b :+ c)) `k` (a' :+ (b' :+ c'))
inLassocS = rassocS <~ lassocS
              <+ ( inOpLR @(:+) @(Ok k) @a  @b  @c C.***
                   inOpLR @(:+) @(Ok k) @a' @b' @c' )

-- | Operate on right-associated form
inRassocS :: forall k a b c a' b' c'.
             (CoproductCat k, Ok6 k a b c a' b' c') =>
             (a :+ (b :+ c)) `k` (a' :+ (b' :+ c'))
          -> ((a :+ b) :+ c) `k` ((a' :+ b') :+ c')
inRassocS = lassocS <~ rassocS
              <+ ( inOpLR @(:+) @(Ok k) @a  @b  @c C.***
                   inOpLR @(:+) @(Ok k) @a' @b' @c' )

#endif

instance CoproductCat (->) where
  inl        = Left
  inr        = Right
  (|||)      = (A.|||)

--   (+++)      = (A.+++)
--   first      = A.first
--   second     = A.second
--   lassocP    = \ (a,(b,c)) -> ((a,b),c)
--   rassocP    = \ ((a,b),c) -> (a,(b,c))

instance Monad m => CoproductCat (Kleisli m) where
  inl   = arr Left
  inr   = arr Right
  (|||) = (A.|||)

{--------------------------------------------------------------------
    Memo trie functors
--------------------------------------------------------------------}

instance Category (:->:) where
  type Ok (:->:) = HasTrie
  id = idTrie
  (.) = (@.@)

instance ProductCat (:->:) where
  exl   = trie exl
  exr   = trie exr
  (&&&) = inTrie2 (&&&)

instance CoproductCat (:->:) where
  inl   = trie inl
  inr   = trie inr
  (|||) = inTrie2 (|||)

instance OpCon (:*) HasTrie where inOp = Sub Dict
instance OpCon (:+) HasTrie where inOp = Sub Dict

-- instance ProdCon HasTrie where inOp @(:*) = inOp

#if 0
instance OpCon (:->:) HasTrie where -- inOp = Sub Dict

instance ClosedCat (:->:) where
  type Exp (:->:) = (:->:)
  apply :: forall a b. Ok2 (:->:) a b => Exp (:->:) a b :* a :->: b
  apply = trie (apply . first untrie)
    <+ inOp @(Exp (:->:)) @(Ok (:->:)) @a @b
  curry = unpack
  uncurry = pack

  -- apply = (pack.trie) (\ (Memod t, a) -> untrie t a)
#endif

{--------------------------------------------------------------------
    Linear maps
--------------------------------------------------------------------}

#if 0

-- (*.*) :: ( HasBasis u, HasTrie (Basis u)
--         , HasBasis v, HasTrie (Basis v)
--         , VectorSpace w, Scalar v ~ Scalar w )

class    (VectorSpace a, HasBasis a, HasTrie (Basis a)) => OkL a
instance (VectorSpace a, HasBasis a, HasTrie (Basis a)) => OkL a

instance Category (:-*) where
  type Ok (:-*) = OkL
  id  = idL
  (.) = (*.*)

#else

class    (VectorSpace a, Scalar a ~ s, HasBasis a, HasTrie (Basis a)) => OkL s a
instance (VectorSpace a, Scalar a ~ s, HasBasis a, HasTrie (Basis a)) => OkL s a

type OkL2 s a b = C2 (OkL s) a b

-- | Linear map over a given scalar field
data LMap s a b = OkL2 s a b => LMap (a :-* b)

-- Needs ExistentialQuantification

instance OkL2 s a b => Newtype (LMap s a b) where
  type O (LMap s a b) = a :-* b
  pack t = LMap t
  unpack (LMap t) = t

instance Category (LMap s) where
  type Ok (LMap s) = OkL s
  id  = pack idL
  (.) = inNew2 (*.*)

-- instance ProdCon (OkL s) where inOp @(:*) = Sub Dict
instance OpCon (:*) (OkL s) where inOp = Sub Dict

-- fstL  :: Ok2 (LMap s) a b => a :* b :-* a
-- sndL  :: Ok2 (LMap s) a b => a :* b :-* b
-- forkL :: Ok3 (LMap s) a c d => (a :-* c) -> (a :-* d) -> (a :-* c :* d)

instance ProductCat (LMap s) where
  exl   = pack exlL
  exr   = pack exrL
  (&&&) = inNew2 forkL

#endif

{--------------------------------------------------------------------
    Entailment
--------------------------------------------------------------------}

-- instance Category (:-) where
--   id = Sub Dict
--   g . f = Sub $ Dict <+ g <+ f

instance Category (:-) where
  id  = refl
  (.) = trans

-- instance ProductCat (:-) where
--   exl = weaken1
--   exr = weaken2
--   dup = contract
--   (&&&) = (C.&&&)
--   (***) = (C.***)

{--------------------------------------------------------------------
    OpCon
--------------------------------------------------------------------}

class OpCon op con where
  inOp :: (con a, con b) :- con (a `op` b)

instance OpCon op Yes where inOp = Sub Dict

inOpL :: OpCon op con => ((con a,con b),con c) :- con ((a `op` b) `op` c)
inOpL = inOp . firstC  inOp

inOpR :: OpCon op con => (con a,(con b,con c)) :- con (a `op` (b `op` c))
inOpR = inOp . secondC inOp

inOpL' :: OpCon op con
       => ((con a,con b),con c) :- (con (a `op` b), con ((a `op` b) `op` c))
inOpL' = secondC inOp `trans` rassocC `trans` firstC (contract `trans` inOp)

-- ((con a,con b),con c)
-- (con (a `op` b),con c)
-- ((con (a `op` b),con (a `op` b)),con c)
-- (con (a `op` b),(con (a `op` b),con c))
-- (con (a `op` b),con ((a `op` b) `op` c))

inOpR' :: OpCon op con
       => (con a,(con b,con c)) :- (con (a `op` (b `op` c)), con (b `op` c))
inOpR' = firstC inOp `trans` lassocC `trans` secondC (contract `trans` inOp)

inOpLR :: forall op con a b c. OpCon op con =>
  (((con a,con b),con c),(con a,(con b,con c)))
  :- (con ((a `op` b) `op` c), con (a `op` (b `op` c)))
inOpLR = inOpL C.*** inOpR

#if 0
type ProdCon' = OpCon (:*)

inProd' :: ProdCon' con => (con a, con b) :- con (a :* b)
inProd' = inOp

inOpL'' :: ProdCon' con => ((con a,con b),con c) :- con ((a :* b) :* c)
inOpL'' = inOpL

inOpR'' :: ProdCon' con => (con a,(con b,con c)) :- con (a :* (b :* c))
inOpR'' = inOpR
#endif


class ProductCat k => ClosedCat k where
  apply   :: Ok2 k a b   => ((a -> b) :* a) `k` b
  curry   :: Ok3 k a b c => ((a :* b) `k` c) -> (a `k` (b -> c))
  uncurry :: Ok3 k a b c => (a `k` (b -> c)) -> ((a :* b) `k` c)

instance ClosedCat (->) where
  apply = \ (f,a) -> f a
  curry = P.curry
  uncurry = P.uncurry

-- instance Monad m => ClosedCat (Kleisli m) where
--   apply = arr apply
--   -- curry f = ???
--   uncurry g = pack (\ (a,b) -> ($ b) <$> unpack g a)

applyK   ::            Kleisli m (Kleisli m a b :* a) b
curryK   :: Monad m => Kleisli m (a :* b) c -> Kleisli m a (Kleisli m b c)
uncurryK :: Monad m => Kleisli m a (Kleisli m b c) -> Kleisli m (a :* b) c

applyK   = pack (apply . first unpack)
curryK   = inNew $ \ h -> return . pack . curry h
uncurryK = inNew $ \ f -> \ (a,b) -> f a >>= ($ b) . unpack

