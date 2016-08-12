{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

-- | Constrained categories

module ConCat where

import Prelude hiding (id,(.))
import qualified Prelude as P

import qualified Control.Arrow as A

import GHC.Types (Constraint)


import Data.Constraint (Dict(..))

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

infixl 7 :*
infixl 6 :+
infixr 1 :=>

type Unit  = ()

type (:*)  = (,)
type (:+)  = Either
type (:=>) = (->)

{--------------------------------------------------------------------
    Category classes
--------------------------------------------------------------------}

infixr 9 .

class Category (k :: u -> u -> *) where
  type Ok k :: u -> Constraint
--   type Ok k = Yes
  okay :: a `k` b -> (OD k a, OD k b)
  id :: Ok k a => a `k` a
  (.) :: b `k` c -> a `k` b -> a `k` c

-- Ok wrapper, avoiding non-injectivity issue
newtype OD k a = OD (Dict (Ok k a))

pattern Okay :: Ok k a => OD k a
pattern Okay = OD Dict

-- The pattern synonym doesn't solve my type checking issue. Investigate.

-- #define OKAY Okay

#define OKAY OD Dict
#define OKAY2 (OKAY,OKAY)

#define OK (okay -> OKAY2)

class    Yes a
instance Yes a

instance Category (->) where
  type Ok (->) = Yes
  id  = P.id
  (.) = (P..)
  okay = const OKAY2

infixr 3 ***, &&&

-- | Category with product.
-- TODO: Generalize '(:*)' to an associated type.
class Category k => ProductCat k where
  okayUnit   :: OD k ()
  okayProd   :: (Ok k a, Ok k b) => OD k (a :* b)
  okayUnProd :: Ok k (a :* b) => (OD k a, OD k b)
  exl :: (Ok k a, Ok k b) => (a :* b) `k` a
  exr :: (Ok k a, Ok k b) => (a :* b) `k` b
  dup :: Ok k a => a `k` (a :* a)
  dup = id &&& id
  swapP :: (Ok k a, Ok k b) => (a :* b) `k` (b :* a)
  swapP =  exr &&& exl
  (***) :: (a `k` c) -> (b `k` d) -> ((a :* b) `k` (c :* d))
  f@OK *** g@OK = f . exl &&& g . exr
  (&&&) :: (a `k` c) -> (a `k` d) -> (a `k` (c :* d))
  f@OK &&& g = (f *** g) . dup
  first :: Ok k b => (a `k` a') -> ((a :* b) `k` (a' :* b))
  first = (*** id)
  second :: Ok k a => (b `k` b') -> ((a :* b) `k` (a :* b'))
  second =  (id ***)
  lassocP :: forall a b c. (Ok k a, Ok k b, Ok k c)
          => (a :* (b :* c)) `k` ((a :* b) :* c)
  lassocP | OKAY <- okayProd :: OD k (b :* c)
          = second exl &&& (exr . exr)
  rassocP :: forall a b c. (Ok k a, Ok k b, Ok k c)
          => ((a :* b) :* c) `k` (a :* (b :* c))
  rassocP | OKAY <- okayProd :: OD k (a :* b)
          =  (exl . exl) &&& first  exr
  {-# MINIMAL okayUnit, okayProd, okayUnProd
            , exl, exr, ((&&&) | ((***), dup)) #-}

instance ProductCat (->) where
  okayUnit   = OKAY
  okayProd   = OKAY
  okayUnProd = OKAY2
  exl        = fst
  exr        = snd
  (&&&)      = (A.&&&)
  (***)      = (A.***)
  first      = A.first
  second     = A.second
  lassocP    = \ (a,(b,c)) -> ((a,b),c)
  rassocP    = \ ((a,b),c) -> (a,(b,c))
  
-- | Apply to both parts of a product
twiceP :: ProductCat k => (a `k` c) -> ((a :* a) `k` (c :* c))
twiceP f = f *** f

#if 0

infixl 1 <~
infixr 1 ~>
-- | Add post- and pre-processing
(<~) :: Category cat =>
        (b `cat` b') -> (a' `cat` a) -> ((a `cat` b) -> (a' `cat` b'))
(h <~ f) g = h . g . f

-- | Add pre- and post-processing
(~>) :: Category cat =>
        (a' `cat` a) -> (b `cat` b') -> ((a `cat` b) -> (a' `cat` b'))
f ~> h = h <~ f

#endif

-- | Operate on left-associated form
inLassocP :: forall a b c a' b' c' k. ProductCat k =>
             (((a :* b) :* c) `k` ((a' :* b') :* c'))
          -> ((a :* (b :* c)) `k` (a' :* (b' :* c')))
inLassocP f@OK | OKAY2 <- okayUnProd :: (OD k (a  :* b ), OD k c )
               , OKAY2 <- okayUnProd :: (OD k (a' :* b'), OD k c')
               , OKAY2 <- okayUnProd :: (OD k a , OD k b )
               , OKAY2 <- okayUnProd :: (OD k a', OD k b')
               = rassocP . f . lassocP

-- | Operate on left-associated form
inRassocP :: forall a b c a' b' c' k. ProductCat k =>
             ((a :* (b :* c)) `k` (a' :* (b' :* c')))
          -> (((a :* b) :* c) `k` ((a' :* b') :* c'))
inRassocP f@OK | OKAY2 <- okayUnProd :: (OD k a , OD k (b  :* c ))
               , OKAY2 <- okayUnProd :: (OD k a', OD k (b' :* c'))
               , OKAY2 <- okayUnProd :: (OD k b , OD k c )
               , OKAY2 <- okayUnProd :: (OD k b', OD k c')
               = lassocP . f . rassocP

-- TODO: bring over more of Circat.Category

#if 1
-- Natural transformations
newtype NT m n = NT (forall a. m a -> n a)

instance Category NT where
  type Ok NT = Yes
  okay = const OKAY2
  id = NT P.id
  NT g . NT f = NT (g . f)
#else
-- Natural transformations
newtype NT k m n = NT (forall a. m a `k` n a)

instance Category k => Category (NT k) where
  type Ok (NT k) = Ok k
--   id = NT id
--   NT g . NT f = NT (g . f)

--   okay = const OKAY2
#endif
