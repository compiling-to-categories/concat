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

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Tries as category

module TrieCat where

import Prelude hiding (id,(.))
import qualified Prelude as P
import Control.Arrow (Kleisli(..),arr)
import qualified Control.Arrow as A
import Control.Applicative (liftA2)
import Control.Monad ((<=<))
-- import Control.Category
-- import Data.Constraint (Dict(..),(:-)(..))
import Control.Newtype
import GHC.Types (Constraint)
import Data.MemoTrie

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

instance Category (->) where
  id  = P.id
  (.) = (P..)

instance Monad m => Category (Kleisli m) where
  id  = pack return
  (.) = inNew2 (<=<)

instance Category (:-) where
  id = Sub Dict
  g . f = Sub $ Dict <+ g <+ f

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
infixr 3 ***, &&&

-- class OkProd k where
--   inProd :: (Ok k a, Ok k b) => Ok k (a :* b)

-- class OkProd k where
--   inProd :: (Ok k a, Ok k b) => Dict (Ok k (a :* b))

-- class ProdCon con where
--   inProd :: (con a, con b) => Dict (con (a :* b))

-- class OkProd k where
--   inProd :: (Ok k a, Ok k b) :- Ok k (a :* b)

class ProdCon con where
  inProd :: (con a, con b) :- con (a :* b)

instance ProdCon Yes where inProd = Sub Dict

inProdL :: ProdCon con => ((con a,con b),con c) :- con ((a :* b) :* c)
inProdL = inProd `trans` firstC  inProd

inProdR :: ProdCon con => (con a,(con b,con c)) :- con (a :* (b :* c))
inProdR = inProd `trans` secondC inProd

inProdL' :: ProdCon con =>
           ((con a,con b),con c) :- (con (a :* b), con ((a :* b) :* c))
inProdL' = secondC inProd `trans` rassocC `trans` firstC (contract `trans` inProd)

-- ((con a,con b),con c)
-- (con (a :* b),con c)
-- ((con (a :* b),con (a :* b)),con c)
-- (con (a :* b),(con (a :* b),con c))
-- (con (a :* b),con ((a :* b) :* c))

inProdR' :: ProdCon con => (con a,(con b,con c)) :- (con (a :* (b :* c)), con (b :* c))
inProdR' = firstC inProd `trans` lassocC `trans` secondC (contract `trans` inProd)

-- q :: ProdCon con => (con ((a :* b) :* c) => r) -> (((con a,con b),con c) => r)
-- q r = r <+ inProdL

-- q :: ProdCon con => (con ((a :* b) :* c) => r) -> (((con a,con b),con c) => r)
-- q r = r <+ inProdL


-- inPL :: ProdCon con => (con ((a :* b) :* c) => r) -> (((con a,con b),con c) => r)
-- inPL r = r <+ inProdL
-- -- inPL = entail inProdL

-- inP :: forall con a b r. (ProdCon con, con a, con b) => (con (a :* b) => r) -> r

inP :: forall con a b r. ProdCon con => (con (a :* b) => r) -> (C2 con a b => r)

inP = (\\ inProd @con @a @b)

-- inP :: forall con r a b. ProdCon con => (con (a :* b) => r) -> ((con a, con b) => r)

-- inP = undefined

-- inP r | Sub Dict <- inProd @con @a @b = r


-- inPL :: forall con a b c r. (ProdCon con,C3 con a b c) => (con ((a :* b) :* c) => r) -> r
-- inPL r = inP @con @a @b $ inP @con @(a :* b) @c $ r
-- -- inPL = (\\ inProdL @con @a @b @c)

inPL :: forall con a b c r. ProdCon con
     => (con ((a :* b) :* c) => r) -> (C3 con a b c => r)
inPL r = inP @con @a @b $ inP @con @(a :* b) @c $ r
-- inPL = inP @con @a @b . inP @con @(a :* b) @c -- nope

-- inProdL :: ProdCon con => ((con a,con b),con c) :- con ((a :* b) :* c)
-- inProdL = inProd `trans` firstC  inProd

-- inPR :: forall con a b c r. (ProdCon con,C3 con a b c) => (con (a :* (b :* c)) => r) -> r
-- inPR = (\\ inProdR @con @a @b @c)

inPR :: forall con a b c r. ProdCon con
     => (con (a :* (b :* c)) => r) -> (C3 con a b c => r)
inPR r = inP @con @b @c $ inP @con @a @(b :* c) $ r
-- inPR = inP @con @b @c . inP @con @a @(b :* c) -- nope


inPLR :: forall con a b c r. ProdCon con
     => (con (a :* (b :* c)) => con ((a :* b) :* c) => r)
     -> (C3 con a b c => r)
inPLR r = inPL @con @a @b @c $ inPR @con @a @b @c $ r


{--------------------------------------------------------------------
    Categories
--------------------------------------------------------------------}

-- | Category with product.
-- TODO: Generalize '(:*)' to an associated type.
class (Category k, ProdCon (Ok k)) => ProductCat k where
  exl :: Ok2 k a b => (a :* b) `k` a
  exr :: Ok2 k a b => (a :* b) `k` b
  dup :: Ok k a => a `k` (a :* a)
  dup = id &&& id
  swapP :: forall a b. Ok2 k a b => (a :* b) `k` (b :* a)
  swapP =  exr &&& exl  <+ inProd @(Ok k) @a @b
  (***) :: forall a b c d. Ok4 k a b c d
        => a `k` c -> b `k` d -> (a :* b) `k` (c :* d)
  f *** g = f . exl &&& g . exr
    <+ inProd @(Ok k) @a @b
--   f *** g = inP @(Ok k) @a @b (f . exl &&& g . exr)
  (&&&) :: forall a c d. Ok3 k a c d
        => a `k` c -> a `k` d -> a `k` (c :* d)
  f &&& g = (f *** g) . dup
    <+ inProd @(Ok k) @a @a
    <+ inProd @(Ok k) @c @d
--   f &&& g = (f *** g) . dup
--     <+ (inProd @(Ok k) @a @a C.*** inProd @(Ok k) @c @d)
  first :: Ok3 k a b a' => (a `k` a') -> ((a :* b) `k` (a' :* b))
  first = (*** id)
  second :: Ok3 k a b b' => (b `k` b') -> ((a :* b) `k` (a :* b'))
  second =  (id ***)
  lassocP :: forall a b c. Ok3 k a b c
          => (a :* (b :* c)) `k` ((a :* b) :* c)
  lassocP = second exl &&& (exr . exr)
--     <+ inProd @(Ok k) @a @(b :* c)
--     <+ inProd @(Ok k) @b @c
--     <+ inProd @(Ok k) @a @b
    <+ inProd   @(Ok k) @a @b
    <+ inProdR' @(Ok k) @a @b @c
  rassocP :: forall a b c. Ok3 k a b c
          => ((a :* b) :* c) `k` (a :* (b :* c))
  rassocP =  (exl . exl) &&& first  exr
--     <+ inProd   @(Ok k) @b @c
--     <+ inProdL' @(Ok k) @a @b @c
    <+ inProd @(Ok k) @(a :* b) @c
    <+ inProd @(Ok k) @b @c
    <+ inProd @(Ok k) @a @b
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
                           -- inProd @(Ok k) @a @b
  (***) :: forall a b c d. Ok4 k a b c d =>
           (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d)
  f *** g = f . exl &&& g . exr  <+ inProd @(Ok k) @a @b
  (&&&) :: forall a c d. Ok3 k a c d =>
           (a `k` c) -> (a `k` d) -> (a `k` Prod k c d)
  f &&& g = (f *** g) . dup
    <+ inProd @(Ok k) @a @a
    <+ inProd @(Ok k) @c @d
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
inLassocP :: forall k a b c a' b' c'.
             (ProductCat k, Ok6 k a b c a' b' c') =>
             ((a :* b) :* c) `k` ((a' :* b') :* c')
          -> (a :* (b :* c)) `k` (a' :* (b' :* c'))

inLassocP = inPLR @(Ok k) @a  @b  @c  $
            inPLR @(Ok k) @a' @b' @c' $
            rassocP <~ lassocP

-- inLassocP = rassocP <~ lassocP
--               <+ (inProdLR @(Ok k) @a  @b  @c C.***
--                   inProdLR @(Ok k) @a' @b' @c')

-- inLassocP = rassocP <~ lassocP
--               <+ inProdL @(Ok k) @a  @b  @c
--               <+ inProdL @(Ok k) @a' @b' @c'
--               <+ inProdR @(Ok k) @a  @b  @c
--               <+ inProdR @(Ok k) @a' @b' @c'

--               <+ inProd @(Ok k) @(a' :* b') @c' <+ inProd @(Ok k) @a' @b'
--               <+ inProd @(Ok k) @(a  :* b ) @c  <+ inProd @(Ok k) @a  @b
--               <+ inProd @(Ok k) @a' @(b' :* c') <+ inProd @(Ok k) @b' @c'
--               <+ inProd @(Ok k) @a  @(b  :* c ) <+ inProd @(Ok k) @b  @c


-- | Operate on left-associated form
inRassocP :: forall k a b c a' b' c'.
             (ProductCat k, Ok6 k a b c a' b' c') =>
             (a :* (b :* c)) `k` (a' :* (b' :* c'))
          -> ((a :* b) :* c) `k` ((a' :* b') :* c')

inRassocP = inPLR @(Ok k) @a  @b  @c  $
            inPLR @(Ok k) @a' @b' @c' $
            lassocP <~ rassocP

-- inRassocP = lassocP <~ rassocP
--               <+ inProdLR @(Ok k) @a  @b  @c
--               <+ inProdLR @(Ok k) @a' @b' @c'

-- inRassocP = lassocP <~ rassocP
--               <+ (inProdLR @(Ok k) @a  @b  @c C.***
--                   inProdLR @(Ok k) @a' @b' @c')

-- inRassocP = inAssocs @(Ok k) @a  @b  @c  $
--             inAssocs @(Ok k) @a' @b' @c' $
--             lassocP <~ rassocP

-- inRassocP = lassocP <~ rassocP
--               <+ inProdL @(Ok k) @a  @b  @c
--               <+ inProdL @(Ok k) @a' @b' @c'
--               <+ inProdR @(Ok k) @a  @b  @c
--               <+ inProdR @(Ok k) @a' @b' @c'

--               <+ inProd @(Ok k) @a' @(b' :* c') <+ inProd @(Ok k) @b' @c'
--               <+ inProd @(Ok k) @a  @(b  :* c ) <+ inProd @(Ok k) @b  @c
--               <+ inProd @(Ok k) @(a' :* b') @c' <+ inProd @(Ok k) @a' @b'
--               <+ inProd @(Ok k) @(a  :* b ) @c  <+ inProd @(Ok k) @a  @b

inAssocs :: forall con a b c r.
             (ProdCon con, C3 con a b c) =>
             (C2 con ((a :* b) :* c) (a :* (b :* c)) => r) -> r
-- inAssocs = inPL @con @a @b @c . inPR @con @a @b @c
-- inAssocs r = inPL @con @a @b @c (inPR @con @a @b @c r)
inAssocs r = inPL @con @a @b @c (inPR @con @a @b @c r)

-- inAssocs r =  r <+ inProdL @con @a @b @c
--                 <+ inProdR @con @a @b @c

inProdLR :: ProdCon con =>
  (((con a,con b),con c),(con a,(con b,con c)))
  :- (con ((a :* b) :* c), con (a :* (b :* c)))
inProdLR = inProdL C.*** inProdR



-- inProdL :: ProdCon con => ((con a,con b),con c) :- con ((a :* b) :* c)
-- inProdR :: ProdCon con => (con a,(con b,con c)) :- con (a :* (b :* c))

-- entail :: (a :- b) -> (b => r) -> (a => r)

-- inPL :: ProdCon con => (con ((a :* b) :* c) => r) -> (((con a,con b),con c) => r)
-- inPL r = r <+ inProdL
-- -- inPL = entail inProdL

-- inPR :: ProdCon con => (con a,(con b,con c)) :- con (a :* (b :* c))

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
--   type Prod (Kleisli m) = (:*)
  exl   = arr fst
  exr   = arr snd
--   dup   = arr dup
  (&&&) = (A.&&&)
--   (***) = (A.***)


-- | Category with coproduct.
class Category k => CoproductCat k where
  inl :: Ok2 k a b => a `k` (a :+ b)
  inr :: Ok2 k a b => b `k` (a :+ b)
  (|||) :: forall a c d. Ok3 k a c d =>
           c `k` a -> d `k` a -> (c :+ d) `k` a

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
--   type Coprod (Kleisli m) = (:+)
  inl   = arr Left
  inr   = arr Right
--   dup   = arr dup
--   (|||) = inNew2 forkA
  (|||) = (A.|||)
--   (+++) = inNew2 crossA

{--------------------------------------------------------------------
    Memo trie functors
--------------------------------------------------------------------}

instance Category (:->:) where
  type Ok (:->:) = HasTrie
  id = idTrie
  (.) = (@.@)

-- instance ProductCat (:->:) where
--   exl   = trie exl
--   exr   = trie exr
--   (&&&) = inTrie2 (&&&)

-- instance CoproductCat (:->:) where
--   inl   = trie inl
--   inr   = trie inr
--   (|||) = inTrie2 (|||)

#if 0

instance OpCon (:*) HasTrie where inOp = Sub Dict
instance OpCon (:+) HasTrie where inOp = Sub Dict

#if 1

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

#endif
