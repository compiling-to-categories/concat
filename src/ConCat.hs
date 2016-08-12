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

class Category k where
  type Ok k a :: Constraint
  id :: Ok k a => a `k` a
  (.) :: b `k` c -> a `k` b -> a `k` c
  -- Constraints help
  okay       :: a `k` b -> (OD k a, OD k b)
  okayUnit   :: OD k ()
  okayProd   :: (Ok k a, Ok k b) => OD k (a :* b)
  okayUnProd :: Ok k (a :* b) => (OD k a, OD k b)

-- Ok wrapper, avoiding non-injectivity issue
newtype OD k a = OD (Dict (Ok k a))

pattern Okay :: Ok k a => OD k a
pattern Okay = OD Dict

-- The pattern synonym doesn't solve my type checking issue. Investigate.

-- #define OKAY Okay

#define OKAY OD Dict
#define OKAY2 (OKAY,OKAY)

#define OK (okay -> OKAY2)

instance Category (->) where
  type Ok (->) a = ()
  id  = P.id
  (.) = (P..)
  okay       = const OKAY2
  okayUnit   = OKAY
  okayProd   = OKAY
  okayUnProd = OKAY2

infixr 3 ***, &&&

-- | Category with product.
-- TODO: Generalize '(:*)' to an associated type.
class Category k => ProductCat k where
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
  {-# MINIMAL exl, exr, ((&&&) | ((***), dup)) #-}

instance ProductCat (->) where
  exl     = fst
  exr     = snd
  (&&&)   = (A.&&&)
  (***)   = (A.***)
  first   = A.first
  second  = A.second
  lassocP = \ (a,(b,c)) -> ((a,b),c)
  rassocP = \ ((a,b),c) -> (a,(b,c))
  
