{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE StandaloneDeriving    #-}
-- 'satisfy' experiment
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}

-- For Uncurriable:
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# OPTIONS_GHC -Wno-orphans #-} -- For Catify

-- {-# OPTIONS_GHC -ddump-rules #-}

-- | Alternative interface to the class operations from ConCat.Category, so as
-- not to get inlined too eagerly to optimize.

#include "ConCat/Ops.inc"

module ConCat.AltCat (module ConCat.AltCat, module C) where

import Prelude hiding (id,(.),curry,uncurry,const,unzip,zip,zipWith)
import qualified Prelude as P
import Control.Arrow (runKleisli)
import qualified Data.Tuple as P
-- import qualified GHC.Exts
import GHC.Exts (Coercible,coerce,inline)
import Data.Constraint ((\\))

import Data.Pointed (Pointed(..))
import Data.Key (Zip(..))
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(..),distributeRep)
-- import qualified Data.Functor.Rep as R
import Control.Newtype (Newtype(..))
-- import Debug.Trace
#ifdef VectorSized
import Data.Proxy (Proxy(..))
import GHC.TypeLits (KnownNat,natVal)
import Data.Finite (Finite)
#endif

import ConCat.Misc ((:*),(:+),unzip,PseudoFun(..),oops,type (&+&),result)
import ConCat.Rep hiding (Rep)
import qualified ConCat.Rep as R
import ConCat.Additive
import qualified ConCat.Category as C

import ConCat.Category
  ( Category, Ok,Ok2,Ok3,Ok4,Ok5, Ok'
  , ProductCat, Prod, twiceP, inLassocP, inRassocP, transposeP --, unfork
  , CoproductCat, Coprod, inLassocS, inRassocS, transposeS, unjoin
  , CoproductPCat, CoprodP, ScalarCat, LinearCat
  , DistribCat, undistl, undistr
  , ClosedCat, Exp
  , TerminalCat, Unit{-, lunit, runit, constFun-}, CoterminalCat, Counit, constFun2, unitFun, unUnitFun
  , ConstCat, ConstObj, lconst, rconst
  , DelayCat, LoopCat
  , BiCCC
  , BoolCat, BoolOf
  , NumCat, IntegralCat, FractionalCat, FloatingCat, RealFracCat, FromIntegralCat
  , EqCat, OrdCat, MinMaxCat, EnumCat, BottomCat, IfCat, IfT, UnknownCat, RepCat, CoerceCat
  , repIf
  -- , Arr, ArrayCat
  , TransitiveCon(..)
  , U2(..), (:**:)(..)
  , type (|-)(..), (<+), okProd, okExp
  , OpCon(..),Sat(..) -- ,FunctorC(..)
  , yes1, forkCon, joinCon, inForkCon
  -- Functor-level
  , OkFunctor(..),FunctorCat,ZipCat,ZapCat,PointedCat,AddCat,Strong
  , DistributiveCat,RepresentableCat 
  , fmap', liftA2' 
  )

-- | Dummy identity function to trigger rewriting of non-inlining operations to
-- inling operations.
reveal :: (a `k` b) -> (a `k` b)
reveal f = f

-- | Dummy identity function to delay rewriting of non-inlining operations to
-- inling operations.
conceal :: (a `k` b) -> (a `k` b)
conceal f = f

{-# INLINE [0] reveal #-}
{-# INLINE [0] conceal #-}

{-# RULES
"reveal/conceal" forall f. reveal (conceal f) = f
"conceal/reveal" forall f. conceal (reveal f) = f
 #-}

-- TODO: replace reveal & conceal definitions by oops, and see if we ever don't
-- remove them.

infixr 9 .
Op0(id,(Category k, Ok k a) => a `k` a)
Ip2(.,forall k b c a. (Category k, Ok3 k a b c) => (b `k` c) -> (a `k` b) -> (a `k` c))

infixr 3 ***, &&&
Op0(exl,(ProductCat k, Ok2 k a b) => Prod k a b `k` a)
Op0(exr,(ProductCat k, Ok2 k a b) => Prod k a b `k` b)
Ip2(&&&,forall k a c d. (ProductCat k, Ok3 k a c d) => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d))
Ip2(***,forall k a b c d. (ProductCat k, Ok4 k a b c d) => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d))
Op0(dup,forall k a. (ProductCat k, Ok k a) => a `k` Prod k a a)
Op0(swapP,forall k a b. (ProductCat k, Ok2 k a b) => Prod k a b `k` Prod k b a)
Op1(first,forall k a aa b. (ProductCat k, Ok3 k a b aa) => (a `k` aa) -> (Prod k a b `k` Prod k aa b))
Op1(second,forall k a b bb. (ProductCat k, Ok3 k a b bb) => (b `k` bb) -> (Prod k a b `k` Prod k a bb))
Op1(lassocP,forall k a b c. (ProductCat k, Ok3 k a b c) => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c)
Op1(rassocP,forall k a b c. (ProductCat k, Ok3 k a b c) => Prod k (Prod k a b) c `k` Prod k a (Prod k b c))

Op1(unfork, forall k a c d. (ProductCat k, Ok3 k a c d) => (a `k` Prod k c d) -> (a `k` c, a `k` d))

infixr 2 +++, |||
Op0(inl,(CoproductCat k, Ok2 k a b) => a `k` Coprod k a b)
Op0(inr,(CoproductCat k, Ok2 k a b) => b `k` Coprod k a b)
Ip2(|||,forall k a c d. (CoproductCat k, Ok3 k a c d) => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a))
Ip2(+++,forall k a b c d. (CoproductCat k, Ok4 k a b c d) => (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b))
Op0(jam,(CoproductCat k, Ok k a) => Coprod k a a `k` a)
Op0(swapS,forall k a b. (CoproductCat k, Ok2 k a b) => Coprod k a b `k` Coprod k b a)
Op1(left ,forall k a aa b. (CoproductCat k, Ok3 k a b aa) => (a `k` aa) -> (Coprod k a b `k` Coprod k aa b))
Op1(right,forall k a b bb. (CoproductCat k, Ok3 k a b bb) => (b `k` bb) -> (Coprod k a b `k` Coprod k a bb))
Op1(lassocS,forall k a b c. (CoproductCat k, Ok3 k a b c) => Coprod k a (Coprod k b c) `k` Coprod k (Coprod k a b) c)
Op1(rassocS,forall k a b c. (CoproductCat k, Ok3 k a b c) => Coprod k (Coprod k a b) c `k` Coprod k a (Coprod k b c))

-- Temporary workaround. See ConCat.Category comments.
infixr 2 ++++, ||||
Op0(inlD,(CoproductPCat k, Ok2 k a b) => a `k` CoprodP k a b)
Op0(inrD,(CoproductPCat k, Ok2 k a b) => b `k` CoprodP k a b)
Ip2(||||,forall k a c d. (CoproductPCat k, Ok3 k a c d) => (c `k` a) -> (d `k` a) -> (CoprodP k c d `k` a))
Ip2(++++,forall k a b c d. (CoproductPCat k, Ok4 k a b c d) => (c `k` a) -> (d `k` b) -> (CoprodP k c d `k` CoprodP k a b))
Op0(jamD,(CoproductPCat k, Ok k a) => CoprodP k a a `k` a)
Op0(swapSD,forall k a b. (CoproductPCat k, Ok2 k a b) => CoprodP k a b `k` CoprodP k b a)

-- Op1(leftD ,forall k a aa b. (CoproductPCat k, Ok3 k a b aa) => (a `k` aa) -> (CoprodP k a b `k` CoprodP k aa b))
-- Op1(rightD,forall k a b bb. (CoproductPCat k, Ok3 k a b bb) => (b `k` bb) -> (CoprodP k a b `k` CoprodP k a bb))
-- Op1(lassocSD,forall k a b c. (CoproductPCat k, Ok3 k a b c) => CoprodP k a (CoprodP k b c) `k` CoprodP k (CoprodP k a b) c)
-- Op1(rassocSD,forall k a b c. (CoproductPCat k, Ok3 k a b c) => CoprodP k (CoprodP k a b) c `k` CoprodP k a (CoprodP k b c))

Op0(scale,(ScalarCat k a => a -> (a `k` a)))

Op0(apply,forall k a b. (ClosedCat k, Ok2 k a b) => Prod k (Exp k a b) a `k` b)
Op1(curry,(ClosedCat k, Ok3 k a b c) => (Prod k a b `k` c) -> (a `k` Exp k b c))
Op1(uncurry,forall k a b c. (ClosedCat k, Ok3 k a b c) => (a `k` Exp k b c)  -> (Prod k a b `k` c))

Op0(distl,forall k a u v. (DistribCat k, Ok3 k a u v) => Prod k a (Coprod k u v) `k` Coprod k (Prod k a u) (Prod k a v))
Op0(distr,forall k u v b. (DistribCat k, Ok3 k u v b) => Prod k (Coprod k u v) b `k` Coprod k (Prod k u b) (Prod k v b))

Op0(it,(TerminalCat k, Ok k a) => a `k` Unit k)
Op0(ti,(CoterminalCat k, Ok k a) => Counit k `k` a)

Op(const,(ConstCat k b, Ok k a) => b -> (a `k` ConstObj k b))
-- Op(unitArrow,ConstCat k b => b -> (Unit k `k` ConstObj k b))

Op(delay,(DelayCat k, Ok k a) => a -> (a `k` a))

Op(loop,(LoopCat k, Ok3 k s a b) => ((a :* s) `k` (b :* s)) -> (a `k` b))

{-# RULES
-- "inOp unitArrow" forall b. reveal (unitArrow b) = C.unitArrow b
"inOp const" forall b. reveal (const b) = C.const b
 #-}

Op0(notC,BoolCat k => BoolOf k `k` BoolOf k)
Op0(andC,BoolCat k => Prod k (BoolOf k) (BoolOf k) `k` BoolOf k)
Op0(orC,BoolCat k => Prod k (BoolOf k) (BoolOf k) `k` BoolOf k)
Op0(xorC,BoolCat k => Prod k (BoolOf k) (BoolOf k) `k` BoolOf k)

Op0(equal,EqCat k a => Prod k a a `k` BoolOf k)
Op0(notEqual,EqCat k a => Prod k a a `k` BoolOf k)

Op0(lessThan,OrdCat k a => Prod k a a `k` BoolOf k)
Op0(greaterThan,OrdCat k a => Prod k a a `k` BoolOf k)
Op0(lessThanOrEqual,OrdCat k a => Prod k a a `k` BoolOf k)
Op0(greaterThanOrEqual,OrdCat k a => Prod k a a `k` BoolOf k)

Op0(minC, (MinMaxCat k a, Ok k a) => Prod k a a `k` a)
Op0(maxC, (MinMaxCat k a, Ok k a) => Prod k a a `k` a)

Op0(succC,EnumCat k a => a `k` a)
Op0(predC,EnumCat k a => a `k` a)

Op0(bottomC,BottomCat k a b => a `k` b)

Op0(ifC,IfCat k a => Prod k (BoolOf k) (Prod k a a) `k` a)

Op0(unknownC,UnknownCat k a b => a `k` b)

Op0(reprC,RepCat k a r => a `k` r)
Op0(abstC,RepCat k a r => r `k` a)

Op0(coerceC,(CoerceCat k a b) => a `k` b)

-- -- Hack to prevent inlining/rewrite loop for reboxing.
-- #undef OPINLINE
-- #define OPINLINE NOINLINE

Op0(negateC,NumCat k a => a `k` a)
Op0(addC,NumCat k a => Prod k a a `k` a)
Op0(subC,NumCat k a => Prod k a a `k` a)
Op0(mulC,NumCat k a => Prod k a a `k` a)
Op0(powIC,NumCat k a => Prod k a Int `k` a)

Op0(divC,IntegralCat k a => Prod k a a `k` a)
Op0(modC,IntegralCat k a => Prod k a a `k` a)
Op0(divModC, (ProductCat k, IntegralCat k a, Ok k a) => Prod k a a `k` Prod k a a)

Op0(recipC,FractionalCat k a => a `k` a)
Op0(divideC,FractionalCat k a => Prod k a a `k` a)

Op0(floorC,RealFracCat k a b => a `k` b)
Op0(ceilingC,RealFracCat k a b => a `k` b)
Op0(truncateC,RealFracCat k a b => a `k` b)

Op0(expC,FloatingCat k a => a `k` a)
Op0(logC,FloatingCat k a => a `k` a)
Op0(cosC,FloatingCat k a => a `k` a)
Op0(sinC,FloatingCat k a => a `k` a)
-- Op0(powC,FloatingCat k a => a `k` a)

Op0(fromIntegralC,FromIntegralCat k a b => a `k` b)

-- Unnecessary but helpful to track NOINLINE choice
-- Op(constFun,forall k p a b. (ClosedCat k, Ok3 k p a b) => (a `k` b) -> (p `k` Exp k a b))

lunit :: (ProductCat k, TerminalCat k, Ok k a) => a `k` Prod k (Unit k) a
lunit = it &&& id

runit :: (ProductCat k, TerminalCat k, Ok k a) => a `k` Prod k a (Unit k)
runit = id &&& it

constFun :: forall k p a b. (ClosedCat k, Ok3 k p a b)
         => (a `k` b) -> (p `k` Exp k a b)
constFun f = curry (f . exr) <+ okProd @k @p @a
{-# INLINE constFun #-}
-- {-# OPINLINE constFun #-}
-- OpRule1(constFun)

funConst :: forall k a b. (ClosedCat k, TerminalCat k, Ok2 k a b)
         => (() `k` (a -> b)) -> (a `k` b)
funConst f = uncurry f . lunit <+ okProd @k @(Unit k) @a

#if 0

#ifdef VectorSized

Op0(array, ArrayCat k n b => Exp k (Finite n) b `k` Arr n b)
Op0(arrAt, ArrayCat k n b => Prod k (Arr n b) (Finite n) `k` b)

at :: (ArrayCat k n b, ClosedCat k, Ok3 k (Finite n) b (Arr n b))
   => Arr n b `k` Exp k (Finite n) b
at = curry arrAt
-- {-# OPINLINE at #-}

natV :: forall n. KnownNat n => Integer
natV = natVal (Proxy @n)

#else

Op0(array, ArrayCat k a b => Exp k a b `k` Arr a b)
Op0(arrAt, ArrayCat k a b => Prod k (Arr a b) a `k` b)
-- Op0(at   , ArrayCat k a b => Arr a b `k` Exp k a b)

at :: (ArrayCat k a b, ClosedCat k, Ok3 k a b (Arr a b))
   => Arr a b `k` Exp k a b
at = curry arrAt
-- {-# OPINLINE at #-}

#endif

#endif

-- TODO: Consider moving all of the auxiliary functions (like constFun) here.
-- Rename "ConCat.Category" to something like "ConCat.Category.Class" and
-- "ConCat.AltCat" to "ConCat.Category".
-- 
-- Maybe move some of the methods with defaults out of the classes, e.g.,
-- "lassocP" and maybe "dup" and "jam".

pair :: forall k a b. (ClosedCat k, Ok2 k a b) => a `k` Exp k b (Prod k a b)
pair = curry id <+ okProd @k @a @b

{-# RULES
"toCcc' fmap" toCcc' fmap = fmap
 #-}

{--------------------------------------------------------------------
    Automatic uncurrying
--------------------------------------------------------------------}

-- Note: I'm not using yet. I think it needs to go before ccc.
-- Alternatively, generalize from (->) to ClosedCat.

-- | Repeatedly uncurried version of a -> b
class Uncurriable k a b where
  type UncDom a b
  type UncRan a b
  type UncDom a b = a
  type UncRan a b = b
  uncurries :: (a `k` b) -> (UncDom a b `k` UncRan a b)
  -- default uncurries :: (a `k` b) -> (a `k` b)
  default uncurries :: (UncDom a b ~ a, UncRan a b ~ b) =>
                       (a `k` b) -> (UncDom a b `k` UncRan a b)
  -- uncurries = id
  -- uncurries = P.id
  uncurries f = f
  -- experiment
  fiddly_foo_unc :: k a b -> ()
  fiddly_foo_unc = const ()
  {-# INLINE uncurries #-}

instance (ClosedCat k, Uncurriable k (a :* b) c, Ok3 k a b c)
      => Uncurriable k a (b -> c) where
  type UncDom a (b -> c) = UncDom (a :* b) c
  type UncRan a (b -> c) = UncRan (a :* b) c
  -- uncurries = uncurries C.. uncurry
  uncurries = uncurries P.. uncurry
  -- uncurries f = uncurries (uncurry f)
  {-# INLINE uncurries #-}

--     • The constraint ‘Uncurriable k (a :* b) c’
--         is no smaller than the instance head
--       (Use UndecidableInstances to permit this)

-- I get better inlining and simplification with explicit uncurries
-- definitions and specific INLINE pragmas.

#define UncId(t) \
instance Uncurriable k a (t) where uncurries f = f ; {-# INLINE uncurries #-}

UncId(())
UncId(Bool)
UncId(Int)
UncId(Float)
UncId(Double)
UncId(c :* d)
UncId(c :+ d)

-- | Pseudo function to trigger rewriting to TOCCC form.
toCcc' :: forall k a b. (a -> b) -> (a `k` b)
toCcc' _ = oops "toCcc' called"
{-# NOINLINE toCcc' #-}

-- | Pseudo function to stop rewriting from TOCCC form.
unCcc' :: forall k a b. (a `k` b) -> (a -> b)
unCcc' _ = oops "unCcc' called"
{-# NOINLINE unCcc' #-}

-- Prevent the plugin from messing with these ones.
{-# ANN toCcc' (PseudoFun 1) #-}
{-# ANN unCcc' (PseudoFun 1) #-}

{-# RULES

"toCcc'/unCcc'" forall f. toCcc' (unCcc' f) = f
"unCcc'/toCcc'" forall f. unCcc' (toCcc' f) = f

 #-}

-- | Pseudo function to trigger rewriting to CCC form, plus a 'reveal' for
-- inlining.
toCcc :: forall k a b. (a -> b) -> (a `k` b)
toCcc f = reveal (toCcc' f)
-- toCcc f = toCcc' f  -- Try doing without reveal/conceal
{-# INLINE toCcc #-}

-- 2017-09-24
{-# DEPRECATED ccc "ccc is now called toCcc" #-}
ccc :: forall k a b. (a -> b) -> (a `k` b)
ccc f = toCcc f
{-# INLINE ccc #-}

-- | Pseudo function to stop rewriting from CCC form.
unCcc :: forall k a b. (a `k` b) -> (a -> b)
unCcc f = unCcc' (conceal f)
-- unCcc f = unCcc' f  -- Try doing without reveal/conceal
{-# INLINE unCcc #-}

{--------------------------------------------------------------------
    Rewrite rules
--------------------------------------------------------------------}

#if 1
{-# RULES

"g . id" forall g. g . id = g
"id . f" forall f. id . f = f

-- Experiment: systematically right-associate
-- We could go either way, but this choice reduces parentheses.
"(.) assoc right" forall f g h. (h . g) . f = h . (g . f)

"exl/&&&" forall f g. exl . (f &&& g) = f
"exr/&&&" forall f g. exr . (f &&& g) = g

"exl/&&& (b)" forall f g h. exl . (f &&& g) . h = f . h
"exr/&&& (b)" forall f g h. exr . (f &&& g) . h = g . h

-- Unnecessary with right-associating composition
"exl2/&&&" forall f g h. (h . exl) . (f &&& g) = h . f
"exr2/&&&" forall f g h. (h . exr) . (f &&& g) = h . g

"exl3/&&&" forall f g h k. (h . (k . exl)) . (f &&& g) = h . k . f
"exr3/&&&" forall f g h k. (h . (k . exr)) . (f &&& g) = h . k . g

"f . h &&& g . h" forall (f :: a `k` c) (g :: a `k` d) h.
  f . h &&& g . h = (f &&& g) . h <+ okProd @k @c @d

-- -- Careful with this one, since dup eventually inlines to id &&& id
-- "id &&& id" [~2] id &&& id = dup

-- -- Specializations with f == id and/or g == id
-- "h &&& h    " forall (h :: a `k` b)               . h &&& h     = (id &&& id) . h <+ okProd @k @b @b
-- "h &&& g . h" forall (g :: b `k` d) (h :: a `k` b). h &&& g . h = (id &&& g ) . h <+ okProd @k @b @d
-- "f . h &&& h" forall (f :: b `k` c) (h :: a `k` b). f . h &&& h = (f  &&& id) . h <+ okProd @k @c @b

-- Oops! the h &&& h rule generates id &&& id, which also matches the rule.

"exl &&& exr" exl &&& exr = id

"(h *** k) . (f &&& g)" forall f g h k. (h *** k) . (f &&& g) = h . f &&& k . g

-- "(f &&& const y) . h" forall y f h. (f &&& const y) . h = f . h &&& const y
-- "(const x &&& g) . h" forall x g h. (const x &&& g) . h = const x &&& g . h

-- "(k . (f &&& const y)) . h" forall y f h k. (k . (f &&& const y)) . h = k . (f . h &&& const y)
-- "(k . (const x &&& g)) . h" forall x g h k. (k . (const x &&& g)) . h = k . (const x &&& g . h)

"uncurry (curry f)" forall f. uncurry (curry f) = f
"curry (uncurry g)" forall g. curry (uncurry g) = g

"constFun 0" forall g f. apply . (curry (g . exr) &&& f) = g . f

"constFun 1" forall f. apply . (curry exr &&& f) = f

"constFun 3" forall f x. apply . (curry (const x) &&& f) = const x

-- Experiment: same rules but via constFun

"constFun' 0" forall g f. apply . (constFun g &&& f) = g . f

-- "foo1" forall (f :: a `k` c) (g :: a `k` d) h.
--   apply . (curry h . f &&& g) = h . (f &&& g) <+ okProd @k @c @d

-- -- The next one leads to a role error when I chain toCcc calls. To investigate.
-- "foo2" forall (g :: a `k` d) h.
--   apply . (curry h &&& g) = h . (id &&& g) <+ okProd @k @a @d

-- "toCcc apply-compose-fork1" forall (f :: a `k` c) (g :: a `k` d) h.
--   apply . (h . f &&& g) = uncurry h . (f &&& g) <+ okProd @k @c @d

-- -- This rule is especially helpful in eliminating uses of apply and curry.
-- "apply-compose-fork2" forall (g :: a `k` d) h.
--   apply . (h &&& g) = uncurry h . (id &&& g) <+ okProd @k @a @d

-- Warning: this rule may be dangerous. Note that `apply == uncurry id`, so if
-- `h == id`, then we aren't making progress.

-- "uncurry . constFun" forall (f :: p -> q). uncurry (constFun f) = f . exr

"curry apply" curry apply = id

-- -- experiment
-- "constFun id" constFun id = curry exr

-- -- This rule helps expose some product rewrites.
-- -- Will we want the opposite for coproducts?
-- "(h . g) . f" forall f g h. (h . g) . f = h . (g . f)

-- "constFun 1" forall f. apply . (curry (f . exr) &&& id) = f

-- "constFun 2" apply . (curry exr &&& id) = id

-- "constFun 3" forall x. apply . (curry (const x) &&& id) = const x

-- "apply . (curry f . exl &&& exr)" forall f .
--   apply . (curry f . exl &&& exr) = f

"second h . (f &&& g)" forall h f g. second h . (f &&& g) = f &&& h . g

"apply . (curry exr &&& f)" forall f.
  apply . (curry exr &&& f) = f

#if 0
-- Prelude versions of categorical ops

"toCcc Prelude id" toCcc P.id = toCcc id
"toCcc Prelude (.)" forall g f. toCcc (g P.. f) = toCcc (g . f)

"toCcc Prelude (,)" toCcc (,) = toCcc pair
"toCcc Prelude fst" toCcc fst = toCcc exl
"toCcc Prelude snd" toCcc snd = toCcc exr
"toCcc Prelude swap" toCcc P.swap = toCcc swapP

"toCcc Prelude Left" toCcc Left = toCcc inl
"toCcc Prelude Right" toCcc Right = toCcc inl
"toCcc Prelude either" toCcc either = toCcc (|||)

"toCcc Prelude curry" forall f. toCcc (P.curry f) = toCcc (curry f)
"toCcc Prelude uncurry" forall f.  toCcc (P.uncurry f) = toCcc (uncurry f)

"toCcc Prelude const" forall x. toCcc (P.const x) = toCcc (const x)

#endif

-- Use this one for now.
"toCcc Prelude const" forall x. toCcc (P.const x) = toCcc (\ _ -> x)

#if 0

-- I've commented out the class-ops, since they'll get expanded away early via
-- auto-generated built-in rules.

"toCcc Control.Category id" toCcc A.id = toCcc id
"toCcc Control.Category (.)" forall g f. toCcc (g A.. f) = toCcc (g . f)

"toCcc Arrow (&&&)" forall f g. toCcc (f A.&&& g) = toCcc (f &&& g)
"toCcc Arrow (***)" forall f g. toCcc (f A.*** g) = toCcc (f *** g)
"toCcc Arrow first" forall f. toCcc (A.first f) = toCcc (first f)
"toCcc Arrow second" forall g. toCcc (A.second g) = toCcc (second g)

"toCcc Arrow (|||)" forall f g. toCcc (f A.||| g) = toCcc (f ||| g)
"toCcc Arrow (+++)" forall f g. toCcc (f A.+++ g) = toCcc (f +++ g)
"toCcc Arrow left" forall f. toCcc (A.left f) = toCcc (left f)
"toCcc Arrow right" forall g. toCcc (A.right g) = toCcc (right g)

#endif

"const x . f" forall x f. const x . f = const x

-- ConstCat k a && ConstCat k b doesn't entail that ConstCat k (a :* b). I could
-- require that implication to hold via a superclass constraint of `ConstCat k
-- t` using my `OpCon` entailment technique. However, that constraint may be too
-- onerous for some categories.

-- "const a &&& const b" forall a b . const a &&& const b = const (a,b)

-- -- Leads to a loop involving foo2. To investigate.
-- "uncurry id" uncurry id = apply

-- "curry apply" curry apply = id

"toCcc P.curry" forall f. toCcc (P.curry f) = toCcc (curry f)
"toCcc P.uncurry" forall f. toCcc (P.uncurry f) = toCcc (uncurry f)

-- "uncurry pair" uncurry pair = id

"abstC . reprC" abstC . reprC = id
"reprC . abstC" reprC . abstC = id

-- -- "repair" forall c. (exl c, exr c) = c
-- -- GHC objects to the previous form. The next one passes, but will it fire?
-- -- Don't use. Rely on categorical rules instead.
-- "re-pair" forall c. (,) (exl c) (exr c) = c

-- Applies only to (->):
"f . const x" forall f x. f . const x = const (f x)

-- "coerceC = id" coerceC = id  -- when types match

-- "coerceC . coerceC" coerceC . coerceC = coco

-- "coerceC . coerceC" coerceC . coerceC = snd coco'

 #-}
#endif

#if 0

{-# RULES

-- "arrAt . arr" forall g f. atArr . (array . g &&& f) = atArr g f

--    opt_univ fell into a hole {awmL}

-- Oddly, this alternative works:

"arrAt . arr" forall g f. uncurry at . (array . g &&& f) = atArr g f

-- "at . arr" at . array = id
-- "arr . at" array . at = id

 #-}


-- I may have stumbled onto a hack for writing GHC rewrite rules whose RHSs
-- impose stronger constraints than their LHSs. In the RHS: add an inlining
-- synonym for the identity arrow that introduces the extra constraints. I think
-- the simplifier will inline and eliminate the identity synonym while leaving
-- the constraint behind.

atArr :: forall k i a b. (ClosedCat k, Ok3 k i a b)
      => (a `k` Exp k i b) -> (a `k` i) -> (a `k` b)
atArr g f = apply . (g &&& f)
  <+ okProd @k @(Exp k i b) @i
  <+ okExp @k @i @b

#endif

coco :: forall k a b c. (CoerceCat k a b, CoerceCat k b c, TransitiveCon (CoerceCat k))
     => (a `k` c)
coco = coerceC \\ trans @(CoerceCat k) @a @b @c

-- The problem is that coco gives no way to relate b.

coco' :: forall k a b c. (CoerceCat k a b, CoerceCat k b c, TransitiveCon (CoerceCat k))
      => b :* (a `k` c)
coco' = (undefined, (coerceC \\ trans @(CoerceCat k) @a @b @c))

-- Experiment

-- -- lassocP' :: Prod k a (Prod k b c) `k` Prod k (Prod k a b) c
-- lassocP' :: (a,(b,c)) `k` ((a,b),c)
-- lassocP' = ccc (\ (a,(b,c)) -> ((a,b),c))

{--------------------------------------------------------------------
    Some orphan instances
--------------------------------------------------------------------}

-- For some (->) instances, we'll want to use late-inlining synonyms

#ifndef VectorSized

deriving instance Functor  (Arr i)
deriving instance Foldable (Arr i)

instance Distributive (Arr i) where
  distribute :: forall f a. Functor f => f (Arr i a) -> Arr i (f a)
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Representable (Arr i) where
  type Rep (Arr i) = i
  tabulate = array
  index = at
  {-# INLINE tabulate #-}
  {-# INLINE index #-}

-- instance Pointed (Arr i) where
--   point = error "point on Arr i: not yet implemented"

instance Zip (Arr i) where
  zipWith = error "zipWith on Arr i: not yet implemented"

-- zeroArr :: Num a => Arr i a
-- zeroArr = error "zeroArr: not yet implemented"

instance Pointed (Arr i) where
  point = error "point on Arr i: not yet implemented"

#endif

#if 1

-- Experiment

satisfy :: forall c a . (c => a) -> a
satisfy = oops "satisfy"
{-# NOINLINE satisfy #-}

toCcc'' :: forall proxy k a b. proxy (a `k` b) -> (a -> b) -> (a `k` b)
toCcc'' _ = oops "toCcc'' called"
{-# NOINLINE toCcc'' #-}

{-# RULES "ccc notC" forall (_p :: _proxy (Bool `k` Bool)). toCcc'' _p notC = satisfy @(BoolCat k) notC #-}

#endif

-- {-# RULES "ccc (->)" forall f. toCcc' f = f #-}


Op1(fmapC , (FunctorCat k h, Ok2 k a b) => (a `k` b) -> (h a `k` h b))
Op0(unzipC, (FunctorCat k h, Ok2 k a b) => h (a :* b) `k` (h a :* h b))
Op0(zipC  , (ZipCat k h    , Ok2 k a b) => (h a :* h b) `k` h (a :* b))
Op0(pointC, (PointedCat k h a)          => a `k` h a)
Op0(sumAC , (AddCat k h a)              => h a `k` a)

Catify(fmap , fmapC)
-- Catify(fmap , fmapIdT)  -- experiment

Catify(unzip, unzipC)
Catify(zip  , curry zipC)
Catify(point, pointC)
Catify(sumA , sumAC)

zipWithC :: Zip h => (a -> b -> c) -> (h a -> h b -> h c)
-- zipWithC f = curry (fmapC (uncurry f) . zipC)
zipWithC f = curry (fmap (uncurry f) . uncurry zip)
{-# INLINE zipWithC #-}

-- zipWithC f as bs = fmapC (uncurry f) (zipC (as,bs))

Catify(zipWith, zipWithC)

#if 0
unzipC :: forall k h a b. (FunctorCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
       => h (a :* b) `k` (h a :* h b)
unzipC = fmapC exl &&& fmapC exr
           <+ okFunctor @k @h @(a :* b)
           <+ okFunctor @k @h @a
           <+ okFunctor @k @h @b
           <+ okProd    @k @a @b
{-# INLINE unzipC #-}
#endif

#if 0
-- See 2017-12-27 notes
zapC :: forall k h a b.
        (FunctorCat k h, ZipCat k h, TerminalCat k, ClosedCat k, Ok2 k a b)
     => (h (a -> b) :* h a) `k` h b
zapC = fmapC apply . zipC
         <+ okFunctor @k @h @((a -> b) :* a)
         <+ okProd    @k    @(h (a -> b)) @(h a)
         <+ okFunctor @k @h @(a -> b)
         <+ okFunctor @k @h @a
         <+ okFunctor @k @h @b
         <+ okProd    @k    @(a -> b) @a
         <+ okExp     @k    @a @b
{-# INLINE zapC #-}

Catify(zap, uncurry zapC)

-- TODO: define zapC via zipWithC
#else
Op1(zapC, (ZapCat k h, Ok2 k a b) => h (a `k` b) -> (h a `k` h b))
-- Translation for zap? Maybe like fmap's.
-- Catify(zap, zapC)  -- 2017-12-27 notes
#endif

-- TODO: Is there any value to defining utility functions like unzipC and zapC
-- in categorical generality? Maybe define only for functions, but still using
-- the categorical building blocks. Later extend to other categories by
-- translation, at which point the Ok constraints will be checked anyway.

fmapId :: forall k h a. (Category k, FunctorCat k h, Ok k a) => h a `k` h a
fmapId = id <+ okFunctor @k @h @a

{-# RULES
"fmapC id" fmapC id = fmapId
"fmapC compose" forall g f. fmapC g . fmapC f = fmapC (g . f)
 #-}

unzipFmapFork :: forall k h a b c.
                 (ProductCat k, Ok3 k a b c, FunctorCat k h)
              => (a `k` b) -> (a `k` c) -> (h a `k` (h b :* h c))
unzipFmapFork f g = fmapC f &&& fmapC g
  <+ okFunctor @k @h @a
  <+ okFunctor @k @h @b
  <+ okFunctor @k @h @c
{-# INLINE unzipFmapFork #-}

-- constPoint :: forall k h a z.
--       (FunctorCat k h, Pointed h, Ok2 k a z, ConstCat k (h a))
--    => a -> (z `k` h a)
-- constPoint a = const (pointC a <+ okFunctor @k @h @a)

-- constPoint :: forall k h a z. (ConstCat k a, PointedCat k h a, Ok2 k a z)
--            => a -> (z `k` h a)
-- constPoint a = pointC . const a <+ okFunctor @k @h @a

-- foo :: Zip h => (b :* c -> d) -> (a -> b) -> h a -> (h c -> h d)
-- foo g f = curry (fmapC g . zipC) . fmap f

zipWithFmap :: forall k h a b c d.
               (ClosedCat k, FunctorCat k h, ZipCat k h, Ok4 k a b c d)
            => ((b :* c) `k` d) -> (a `k` b) -> (h a `k` (h c -> h d))
zipWithFmap g f = curry (fmapC (uncurry (curry g . f)) . zipC)
  <+ okFunctor @k @h @(a :* c)
  <+ okProd @k @(h a) @(h c)
  <+ okProd @k @a @c
  <+ okExp  @k @c @d
  <+ okFunctor @k @h @a
  <+ okFunctor @k @h @c
  <+ okFunctor @k @h @d
{-# INLINE zipWithFmap #-}

{-# RULES

"unzipC . zipC" unzipC . zipC = id

-- -- Fail. Needs ZipCat on RHS but not LHS.
-- "fmap (f &&& g)" forall f g. fmapC (f &&& g) = zipC . (fmapC f &&& fmapC g)

-- -- Less modular, but uses ZipCat on LHS. Needs Ok constraints on right.
-- "unzipC . fmapC (f &&& g)" forall f g. unzipC . fmapC (f &&& g) = fmapC f &&& fmapC g

-- unzipC . fmapC (f &&& g) = fmapC f &&& fmapC g
-- Use an external definition to get RHS Ok constraints.
-- GHC isn't inlining that definition, so force it.
"unzipC . fmapC (f &&& g)" forall f g.
   unzipC . fmapC (f &&& g) = inline unzipFmapFork f g

-- "fmapC (constFun f)" forall f.
--   fmapC (constFun f) = constFun (pointC f)

-- Do I need to inline constFun, at least on the left?

-- -- *Applying* pointC restricts to functions

-- -- RHS needs PointedCat
-- "fmapC (constFun f)" forall f.
--   fmapC (curry (f . exr)) = pointC . constFun f

-- -- Seems iffy for staging. RHS needs Pointed.
-- "fmapC (constFun f)" forall f. fmapC (constFun f) = const (point f)

-- -- Needs RHS constraints
-- "fmapC (const a)" forall a. fmapC (const a) = const (pointC a)

-- "fmapC (const a)" forall a. fmapC (const a) = constPoint a

-- "zipWith g . fmap f" forall f g .
--   curry (fmapC g . zipC) . fmapC f = fmapC (uncurry (g . f)) . zipC

-- 2017-11-05 notes
"zipWith g . fmap f" forall f g .
  -- zipWith g . fmap f = zipWith (g . f)
  curry (fmapC g . zipC) . fmapC f = inline zipWithFmap g f
  -- curry (fmapC g . zipC) . fmapC f = curry (fmapC (uncurry (curry g . f)) . zipC)

-- 2017-11-05 notes
"constFun (fmap f)" forall f .
  curry (fmap (f . exr) . zipC) = inline constFun (fmap f)

-- -- 2017-11-06 notes
-- "constFun (fmap f)" forall f .
--   curry (fmapC (f . exr) . zipC) = constFun (fmapC f)

 #-}



#if 0
-- Experiment

idCon :: forall con k a b. con k => (a `k` b) -> (a `k` b)
idCon f = f
{-# INLINE idCon #-}

{-# RULES
"idCon test a" fmapC id = fmapId
"idCon test b" idCon @ProductCat (fmapC id) = fmapId
 #-}

-- Too bad. The idCon appears in the rule's LHS.

#endif

Op0(strength, (Strong k h, OkFunctor k h, Ok2 k a b) => (a :* h b) `k` h (a :* b))

Op0(distributeC, (DistributiveCat k g f, Ok k a) => f (g a) `k` g (f a))
Op0(tabulateC  , (RepresentableCat k f , Ok k a) => (Rep f -> a) `k` f a)
Op0(indexC     , (RepresentableCat k f , Ok k a) => f a `k` (Rep f -> a))

Catify(distribute, distributeC)
Catify(tabulate  , tabulateC)
Catify(index     , indexC)

collectC :: (Distributive g, Functor f) => (a -> g b) -> f a -> g (f b)
collectC f = distribute . fmap f
-- collectC f = distributeC . fmapC f
{-# INLINE collectC #-}

Catify(collect, collectC)

{-# RULES

"fmap id" uncurry fmapC . (curry exr &&& id) = id

 #-}

-- -- Names are in transition

-- tabulateC :: ArrayCat k n b => Exp k (Finite n) b `k` Arr n b
-- tabulateC = array

-- indexC :: ArrayCat k n b => Arr n b `k` Exp k (Finite n) b
-- indexC = curry arrAt


-- Variant of 'distributeRep' from Data.Functor.Rep
-- TODO: Generalize from Vector.

-- distributeRepC :: ( -- Representable f, Functor w,
--                     f ~ Vector n, KnownNat n, Representable w
--                   )
--                => w (f a) -> f (w a)

-- distributeRepC :: ( -- Representable f, Functor w,
--                     w ~ Vector n, KnownNat n -- , Representable w
--                   )
--                => w (f a) -> f (w a)

-- distributeRepC wf = tabulateC (\k -> fmapC (`indexC` k) wf)

type Diagonal h = (Representable h, Eq (Rep h))

diag :: Diagonal h => a -> a -> h (h a)
diag z o =
  -- tabulateC (\ i -> tabulateC (\ j -> if i == j then o else z))
  -- tabulateC (\ i -> tabulateC (\ j -> if equal (i,j) then o else z))
  tabulate (\ i -> tabulate (\ j -> if i == j then o else z))
{-# INLINE diag #-}

-- TODO: retry diag as a single tabulateC on h :.: h.

-- HACK: the equal here is to postpone dealing with equality on sum types just yet.
-- See notes from 2017-10-15.
-- TODO: remove and test, now that we're translating (==) early (via Catify).
