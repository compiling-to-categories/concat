{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE StandaloneDeriving    #-}

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

{-# OPTIONS_GHC -Wno-orphans #-} -- See Functor (Arr n)

-- | Alternative interface to the class operations from ConCat.Category, so as
-- not to get inlined too eagerly to optimize.

-- #define VectorSized

#include "ConCat/Ops.inc"

module ConCat.AltCat (module ConCat.AltCat, module C) where

import Prelude hiding (id,(.),curry,uncurry,const)
import qualified Prelude as P
import Control.Arrow (runKleisli)
import qualified Data.Tuple as P
import GHC.Exts (Coercible,coerce)
import Data.Constraint ((\\))

import Data.Pointed (Pointed(..))
import Data.Key (Zip(..))
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(tabulate,index),distributeRep)
import qualified Data.Functor.Rep as R
import Control.Newtype (Newtype(..))
#ifdef VectorSized
import Data.Proxy (Proxy(..))
import GHC.TypeLits (KnownNat,natVal)
import Data.Finite (Finite)
#endif

import qualified ConCat.Category as C
import ConCat.Rep
import ConCat.Misc ((:*),(:+),PseudoFun(..),oops,type (&+&))

import ConCat.Category
  ( Category, Ok,Ok2,Ok3,Ok4,Ok5, Ok'
  , ProductCat, Prod, twiceP, inLassocP, inRassocP, transposeP --, unfork
  , CoproductCat, Coprod, inLassocS, inRassocS, transposeS, unjoin
  , DistribCat, undistl, undistr
  , ClosedCat, Exp
  , TerminalCat, Unit{-, lunit, runit, constFun-}, constFun2, unitFun, unUnitFun
  , ConstCat, ConstObj, lconst, rconst
  , DelayCat, LoopCat
  , BiCCC
  , BoolCat, BoolOf
  , NumCat, IntegralCat, FractionalCat, FloatingCat, RealFracCat, FromIntegralCat
  , EqCat, OrdCat, EnumCat, BottomCat, IfCat, IfT, UnknownCat, RepCat, CoerceCat
  , repIf
  , Arr, ArrayCat
  , TransitiveCon(..)
  , U2(..), (:**:)(..)
  , type (|-)(..), (<+), okProd, okExp, OkFunctor(..)
  , OpCon(..),Sat(..) -- ,FunctorC(..)
  , yes1, forkCon, joinCon, inForkCon
  -- , AmbCat
  )

-- | Dummy identity function to trigger rewriting of non-inlining operations to
-- inling operations.
reveal :: (a `k` b) -> (a `k` b)
reveal f = f
{-# INLINE [0] reveal #-}

-- | Dummy identity function to delay rewriting of non-inlining operations to
-- inling operations.
conceal :: (a `k` b) -> (a `k` b)
conceal f = f
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
Op2(second,forall k a b bb. (ProductCat k, Ok3 k a b bb) => (b `k` bb) -> (Prod k a b `k` Prod k a bb))
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

Op0(apply,forall k a b. (ClosedCat k, Ok2 k a b) => Prod k (Exp k a b) a `k` b)
Op1(curry,(ClosedCat k, Ok3 k a b c) => (Prod k a b `k` c) -> (a `k` Exp k b c))
Op1(uncurry,forall k a b c. (ClosedCat k, Ok3 k a b c) => (a `k` Exp k b c)  -> (Prod k a b `k` c))

Op0(distl,forall k a u v. (DistribCat k, Ok3 k a u v) => Prod k a (Coprod k u v) `k` Coprod k (Prod k a u) (Prod k a v))
Op0(distr,forall k u v b. (DistribCat k, Ok3 k u v b) => Prod k (Coprod k u v) b `k` Coprod k (Prod k u b) (Prod k v b))

Op0(it,(TerminalCat k, Ok k a) => a `k` Unit k)

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
Op0(cosC,FloatingCat k a => a `k` a)
Op0(sinC,FloatingCat k a => a `k` a)

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
{-# ANN toCcc' PseudoFun #-}
{-# ANN unCcc' PseudoFun #-}

{-# RULES

"toCcc'/unCcc'" forall f. toCcc' (unCcc' f) = f
"unCcc'/toCcc'" forall f. unCcc' (toCcc' f) = f

 #-}

-- | Pseudo function to trigger rewriting to CCC form, plus a 'reveal' for
-- inlining.
toCcc :: forall k a b. (a -> b) -> (a `k` b)
toCcc f = reveal (toCcc' f)
{-# INLINE toCcc #-}

-- 2017-09-24
{-# DEPRECATED ccc "ccc is now called toCcc" #-}
ccc :: forall k a b. (a -> b) -> (a `k` b)
ccc f = toCcc f
{-# INLINE ccc #-}

-- | Pseudo function to stop rewriting from CCC form.
unCcc :: forall k a b. (a `k` b) -> (a -> b)
unCcc f = unCcc' (conceal f)
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

-- -- experiment
-- "constFun id" constFun id = curry exr

-- -- This rule helps expose some product rewrites.
-- -- Will we want the opposite for coproducts?
-- "(h . g) . f" forall f g h. (h . g) . f = h . (g . f)

-- "constFun 1" forall f. apply . (curry (f . exr) &&& id) = f

-- "constFun 2" apply . (curry exr &&& id) = id

-- "constFun 3" forall x. apply . (curry (const x) &&& id) = const x

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

-- TODO: probably move the Arr type and operations to concat-examples, say in
-- ConCat.Aggregate and ConCat.AltAggregate.
