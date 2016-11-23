{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Alternative interface to the class operations from ConCat.Category, so as
-- not to get inlined too eagerly to optimize.

module ConCat.AltCat
  ( module ConCat.AltCat
  , module C)
  where

{-# LANGUAGE NoMonomorphismRestriction #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-}  -- TEMP

import Prelude hiding (id,(.),curry,uncurry,const)

import ConCat.Category
  ( Category, Ok,Ok2,Ok3,Ok4,Ok5
  , ProductCat, Prod, twiceP, inLassocP, inRassocP, transposeP, unfork
  , CoproductCat, Coprod, inLassocS, inRassocS, transposeS, unjoin
  , DistribCat, undistl, undistr
  , ClosedCat, Exp
  , TerminalCat, Unit, lunit, runit{-, constFun-}, constFun2, unitFun, unUnitFun
  , ConstCat, ConstObj, lconst, rconst
  , BiCCC
  , BoolCat, BoolOf
  , NumCat, FractionalCat, FloatingCat, FromIntegralCat
  , EqCat, OrdCat, EnumCat, BottomCat, IfCat, UnknownCat, RepCat
  , ccc
  --
  , (<+), okProd
  )

import qualified ConCat.Category as C
import ConCat.Rep

#define Op(nm,ty) \
{- | C.nm without the eager inlining -}; \
nm :: ty; \
nm = C.nm ;\
{-# NOINLINE nm #-}

#define Ip(nm,ty) \
{- | (C.nm) without the eager inlining -}; \
(nm) :: ty; \
(nm) = (C.nm) ;\
{-# NOINLINE (nm) #-}

-- I use semicolons and the {- | ... -} style Haddock comment because CPP macros
-- generate a single line. I want to inject single quotes around the C.foo and
-- (C.op) names to form Haddock links, but CPP interprets them as preventing
-- macro argument insertion.


infixr 9 .
Op(id,(Category k, Ok k a) => a `k` a)
Ip(.,forall k b c a. (Category k, Ok3 k a b c) => (b `k` c) -> (a `k` b) -> (a `k` c))

infixr 3 ***, &&&
Op(exl,(ProductCat k, Ok2 k a b) => Prod k a b `k` a)
Op(exr,(ProductCat k, Ok2 k a b) => Prod k a b `k` b)
Ip(&&&,forall k a c d. (ProductCat k, Ok3 k a c d) => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d))
Ip(***,forall k a b c d. (ProductCat k, Ok4 k a b c d) => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d))
Op(dup,forall k a. (ProductCat k, Ok k a) => a `k` Prod k a a)
Op(swapP,forall k a b. (ProductCat k, Ok2 k a b) => Prod k a b `k` Prod k b a)
Op(first,forall k a aa b. (ProductCat k, Ok3 k a b aa) => (a `k` aa) -> (Prod k a b `k` Prod k aa b))
Op(second,forall k a b bb. (ProductCat k, Ok3 k a b bb) => (b `k` bb) -> (Prod k a b `k` Prod k a bb))
Op(lassocP,forall k a b c. (ProductCat k, Ok3 k a b c) => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c)
Op(rassocP,forall k a b c. (ProductCat k, Ok3 k a b c) => Prod k (Prod k a b) c `k` Prod k a (Prod k b c))

infixr 2 +++, |||
Op(inl,(CoproductCat k, Ok2 k a b) => a `k` Coprod k a b)
Op(inr,(CoproductCat k, Ok2 k a b) => b `k` Coprod k a b)
Ip(|||,forall k a c d. (CoproductCat k, Ok3 k a c d) => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a))
Ip(+++,forall k a b c d. (CoproductCat k, Ok4 k a b c d) => (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b))
Op(jam,(CoproductCat k, Ok k a) => Coprod k a a `k` a)
Op(swapS,forall k a b. (CoproductCat k, Ok2 k a b) => Coprod k a b `k` Coprod k b a)
Op(left ,forall k a aa b. (CoproductCat k, Ok3 k a b aa) => (a `k` aa) -> (Coprod k a b `k` Coprod k aa b))
Op(right,forall k a b bb. (CoproductCat k, Ok3 k a b bb) => (b `k` bb) -> (Coprod k a b `k` Coprod k a bb))
Op(lassocS,forall k a b c. (CoproductCat k, Ok3 k a b c) => Coprod k a (Coprod k b c) `k` Coprod k (Coprod k a b) c)
Op(rassocS,forall k a b c. (CoproductCat k, Ok3 k a b c) => Coprod k (Coprod k a b) c `k` Coprod k a (Coprod k b c))

Op(apply,forall k a b. (ClosedCat k, Ok2 k a b) => Prod k (Exp k a b) a `k` b)
Op(curry,(ClosedCat k, Ok3 k a b c) => (Prod k a b `k` c) -> (a `k` Exp k b c))
Op(uncurry,forall k a b c. (ClosedCat k, Ok3 k a b c) => (a `k` Exp k b c)  -> (Prod k a b `k` c))

Op(distl,forall k a u v. (DistribCat k, Ok3 k a u v) => Prod k a (Coprod k u v) `k` Coprod k (Prod k a u) (Prod k a v))
Op(distr,forall k u v b. (DistribCat k, Ok3 k u v b) => Prod k (Coprod k u v) b `k` Coprod k (Prod k u b) (Prod k v b))

Op(it,(TerminalCat k, Ok k a) => a `k` Unit k)
Op(unitArrow,ConstCat k b => b -> (Unit k `k` ConstObj k b))
Op(const,(ConstCat k b, Ok k a) => b -> (a `k` ConstObj k b))

Op(notC,BoolCat k => BoolOf k `k` BoolOf k)
Op(andC,BoolCat k => Prod k (BoolOf k) (BoolOf k) `k` BoolOf k)
Op(orC,BoolCat k => Prod k (BoolOf k) (BoolOf k) `k` BoolOf k)
Op(xorC,BoolCat k => Prod k (BoolOf k) (BoolOf k) `k` BoolOf k)

Op(negateC,NumCat k a => a `k` a)
Op(addC,NumCat k a => Prod k a a `k` a)
Op(subC,NumCat k a => Prod k a a `k` a)
Op(mulC,NumCat k a => Prod k a a `k` a)
Op(powIC,NumCat k a => Prod k a Int `k` a)

Op(recipC,FractionalCat k a => a `k` a)
Op(divideC,FractionalCat k a => Prod k a a `k` a)

Op(expC,FloatingCat k a => a `k` a)
Op(cosC,FloatingCat k a => a `k` a)
Op(sinC,FloatingCat k a => a `k` a)

Op(fromIntegralC,FromIntegralCat k a b => a `k` b)

Op(equal,EqCat k a => Prod k a a `k` BoolOf k)
Op(notEqual,EqCat k a => Prod k a a `k` BoolOf k)

Op(lessThan,OrdCat k a => Prod k a a `k` BoolOf k)
Op(greaterThan,OrdCat k a => Prod k a a `k` BoolOf k)
Op(lessThanOrEqual,OrdCat k a => Prod k a a `k` BoolOf k)
Op(greaterThanOrEqual,OrdCat k a => Prod k a a `k` BoolOf k)

Op(succC,EnumCat k a => a `k` a)
Op(predC,EnumCat k a => a `k` a)

Op(bottomC,BottomCat k a => Unit k `k` a)

Op(ifC,IfCat k a => Prod k (BoolOf k) (Prod k a a) `k` a)

Op(unknownC,UnknownCat k a b => a `k` b)

Op(reprC,(RepCat k, HasRep a) => a `k` Rep a)
Op(abstC,(RepCat k, HasRep a) => Rep a `k` a)

-- Unnecessary but helpful to track NOINLINE choice
-- Op(constFun,forall k p a b. (ClosedCat k, Ok3 k p a b) => (a `k` b) -> (p `k` Exp k a b))

constFun :: forall k p a b. (ClosedCat k, Ok3 k p a b)
         => (a `k` b) -> (p `k` Exp k a b)
constFun f = curry (f . exr) <+ okProd @k @p @a
{-# INLINE constFun #-}

-- TODO: Consider moving all of the auxiliary functions (like constFun) here.
-- Rename "ConCat.Category" to something like "ConCat.Category.Class" and
-- "ConCat.AltCat" to "ConCat.Category".
-- 
-- Maybe move some of the methods with defaults out of the classes, e.g.,
-- "lassocP" and maybe "dup" and "jam".

{-# RULES

"g . id" forall g. g . id = g
"id . f" forall f. id . f = f

"exl/&&&" forall f g. exl . (f &&& g) = f
"exr/&&&" forall f g. exr . (f &&& g) = g

"exl2/&&&" forall f g h. (h . exl) . (f &&& g) = h . f
"exr2/&&&" forall f g h. (h . exr) . (f &&& g) = h . g

"exl3/&&&" forall f g h k. (h . (k . exl)) . (f &&& g) = h . k . f
"exr3/&&&" forall f g h k. (h . (k . exr)) . (f &&& g) = h . k . g

"f . h &&& g . h" forall (f :: a `k` c) (g :: a `k` d) h.
  f . h &&& g . h = (f &&& g) . h <+ okProd @k @c @d

-- Careful with this one, since dup eventually inlines to id &&& id
-- "id &&& id" [~2] id &&& id = dup

-- -- Specializations with f == id and/or g == id
-- "h &&& h    " forall (h :: a `k` b)               . h &&& h     = (id &&& id) . h <+ okProd @k @b @b
-- "h &&& g . h" forall (g :: b `k` d) (h :: a `k` b). h &&& g . h = (id &&& g ) . h <+ okProd @k @b @d
-- "f . h &&& h" forall (f :: b `k` c) (h :: a `k` b). f . h &&& h = (f  &&& id) . h <+ okProd @k @c @b

-- Oops! the h &&& h rule generates id &&& id, which also matches the rule.

"exl &&& exr" exl &&& exr = id

-- "(f &&& const y) . h" forall y f h. (f &&& const y) . h = f . h &&& const y
-- "(const x &&& g) . h" forall x g h. (const x &&& g) . h = const x &&& g . h

-- "(k . (f &&& const y)) . h" forall y f h k. (k . (f &&& const y)) . h = k . (f . h &&& const y)
-- "(k . (const x &&& g)) . h" forall x g h k. (k . (const x &&& g)) . h = k . (const x &&& g . h)

"uncurry (curry f)" forall f. uncurry (curry f) = f
"curry (uncurry g)" forall g. curry (uncurry g) = g

"constFun 0" forall g f. apply . (curry (g . exr) &&& f) = g . f

"constFun 1" forall f. apply . (curry exr &&& f) = f

"constFun 3" forall f x. apply . (curry (const x) &&& f) = const x

"foo1" forall (f :: a `k` c) (g :: a `k` d) h.
  apply . (curry h . f &&& g) = h . (f &&& g) <+ okProd @k @c @d

"foo2" forall (g :: a `k` d) h.
  apply . (curry h &&& g) = h . (id &&& g) <+ okProd @k @a @d

 #-}

-- -- This rule helps expose some product rewrites.
-- -- Will we want the opposite for coproducts?
-- "(h . g) . f" forall f g h. (h . g) . f = h . (g . f)

-- "constFun 1" forall f. apply . (curry (f . exr) &&& id) = f

-- "constFun 2" apply . (curry exr &&& id) = id

-- "constFun 3" forall x. apply . (curry (const x) &&& id) = const x
