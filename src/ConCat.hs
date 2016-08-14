{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DefaultSignatures #-}
-- {-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | Constrained categories

module ConCat where

import Prelude hiding (id,(.))
import qualified Prelude as P
import Foreign.C.Types (CSChar, CInt, CShort, CLong, CLLong, CIntMax, CFloat, CDouble)
import Data.Ratio
import qualified Control.Arrow as A

import GHC.Types (Constraint)

import Data.Constraint (Dict(..),(:-)(..),(\\),trans,weaken1)

import Misc

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

{--------------------------------------------------------------------
    Constraints with consequences
--------------------------------------------------------------------}

#if 0

-- Constraint consequences
type family Conseq c a :: Constraint where
  Conseq c (p,q,r)  = (c p, c q, c r)
  Conseq c (p,q,r,s) = (c p, c q, c r, c s)
  Conseq c (a :* b) = (c a, c b)
  Conseq c (a :+ b) = (c a, c b)
  Conseq c t        = ()

#else

-- Open type family

-- Constraint consequences
type family Conseq (c :: u -> Constraint) (a :: u) :: Constraint

type instance Conseq c (p :* q) = (c p, c q)
type instance Conseq c (p :+ q) = (c p, c q)

-- Others

type instance Conseq c (p,q,r)  = (c p, c q, c r)
type instance Conseq c (p,q,r,s) = (c p, c q, c r, c s)

#define ScalarType(t) type instance Conseq c (t) = ()

ScalarType(())
ScalarType(Int)
ScalarType(Integer)
ScalarType(Float)
ScalarType(Double)
ScalarType(CSChar)
ScalarType(CInt)
ScalarType(CShort)
ScalarType(CLong)
ScalarType(CLLong)
ScalarType(CIntMax)
ScalarType(CDouble)
ScalarType(CFloat)
-- etc

instance (c p, c q, c r     ) => HasConseq c (p,q,r  ) where conseq = Sub Dict
instance (c p, c q, c r, c s) => HasConseq c (p,q,r,s) where conseq = Sub Dict

#endif

-- TODO: Try recursively adding consequences

-- Constraints with consequences
class HasConseq c (a :: *) where
  conseq :: c a :- Conseq c a
  default conseq :: c a :- ()
  conseq = Sub Dict

instance (c a, c b) => HasConseq c (a :* b) where conseq = Sub Dict
instance (c a, c b) => HasConseq c (a :+ b) where conseq = Sub Dict

#if 1
-- Example: values with sizes

class HasConseq Sizable a => Sizable (a :: *) where
  size :: a -> Int
  
instance HasConseq Sizable ()
instance Sizable () where size _ = 0

instance HasConseq Sizable Int
instance Sizable Int where size _ = 1

instance (Sizable a, Sizable b) => Sizable (a :* b) where
  size (a,b) = size a + size b

instance (Sizable a, Sizable b) => Sizable (a :+ b) where
  size = size `either` size

#endif

{--------------------------------------------------------------------
    Constraints with product consequences
--------------------------------------------------------------------}

class ProdCon (con :: * -> Constraint) where
  unit   :: () :- con ()
  inProd :: (con a, con b) :- con (a :* b)
  exProd :: con (a :* b) :- (con a, con b)

exProdL :: forall con a b c. ProdCon con => con ((a,b),c) :- ((con a,con b),con c)
exProdL = firstC  exProd `trans` exProd

exProdR :: forall con a b c. ProdCon con => con (a,(b,c)) :- (con a,(con b,con c))
exProdR = secondC exProd `trans` exProd

instance ProdCon Yes where
  unit   = Sub Dict
  inProd = Sub Dict
  exProd = Sub Dict

{--------------------------------------------------------------------
    Category classes
--------------------------------------------------------------------}

infixr 9 .

#define OKAY OD Dict
#define OKAY2 (OKAY,OKAY)

class Category (k :: u -> u -> *) where
  type Ok k :: u -> Constraint
  type Ok k = Yes
  okay :: a `k` b -> (OD k a, OD k b)
--   default okay :: a `k` b -> (OD k a, OD k b)
--   okay = const OKAY2
  id  :: Ok k a => a `k` a
  (.) :: b `k` c -> a `k` b -> a `k` c

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

-- Ok wrapper, avoiding non-injectivity issue
newtype OD k a = OD (Dict (Ok k a))

pattern Okay :: Ok k a => OD k a
pattern Okay = OD Dict

-- The pattern synonym doesn't solve my type checking issue.
-- Investigate.

-- #define OKAY Okay

#define OK (okay -> OKAY2)

instance Category (->) where
  id  = P.id
  (.) = (P..)
  okay = const OKAY2

infixr 3 ***, &&&

-- | Category with product.
-- TODO: Generalize '(:*)' to an associated type.
class (ProdCon (Ok k), Category k) => ProductCat k where
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
  lassocP = second exl &&& (exr . exr) <+ inProd @(Ok k) @b @c
  rassocP :: forall a b c. (Ok k a, Ok k b, Ok k c)
          => ((a :* b) :* c) `k` (a :* (b :* c))
  rassocP =  (exl . exl) &&& first  exr <+ inProd @(Ok k) @a @b
  {-# MINIMAL exl, exr, ((&&&) | ((***), dup)) #-}

-- Alternatively:
-- 
--   lassocP = second exl &&& (exr . exr)
--     <+ (inProd :: (Ok k b, Ok k c) :- Ok k (b :* c))
--   rassocP =  (exl . exl) &&& first  exr
--     <+ (inProd :: (Ok k a, Ok k b) :- Ok k (a :* b))

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
twiceP :: ProductCat k => (a `k` c) -> ((a :* a) `k` (c :* c))
twiceP f = f *** f

-- | Operate on left-associated form
inLassocP :: forall a b c a' b' c' k. ProductCat k =>
             (((a :* b) :* c) `k` ((a' :* b') :* c'))
          -> ((a :* (b :* c)) `k` (a' :* (b' :* c')))
inLassocP f@OK =
  rassocP . f . lassocP
    <+ exProdL @(Ok k) @a  @b  @c
    <+ exProdL @(Ok k) @a' @b' @c'

-- Equivalently,
-- 
--     <+ firstC (exProd @(Ok k) @a  @b ) `trans` (exProd @(Ok k) @(a  :* b ) @c )
--     <+ firstC (exProd @(Ok k) @a' @b') `trans` (exProd @(Ok k) @(a' :* b') @c')
-- Or
--     <+ exProd @(Ok k) @a @b
--     <+ exProd @(Ok k) @(a  :* b ) @c
--     <+ exProd @(Ok k) @a' @b'
--     <+ exProd @(Ok k) @(a' :* b') @c'

-- | Operate on right-associated form
inRassocP :: forall a b c a' b' c' k. ProductCat k =>
             ((a :* (b :* c)) `k` (a' :* (b' :* c')))
          -> (((a :* b) :* c) `k` ((a' :* b') :* c'))
inRassocP f@OK =
  lassocP . f . rassocP
    <+ exProdR @(Ok k) @a  @b  @c
    <+ exProdR @(Ok k) @a' @b' @c'
