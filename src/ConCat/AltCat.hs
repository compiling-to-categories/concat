{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
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
  , TerminalCat, Unit, lunit, runit, constFun, constFun2, unitFun, unUnitFun
  , ConstCat, ConstObj, lconst, rconst
  , BiCCC
  , BoolCat, BoolOf
  , NumCat, FractionalCat, FloatingCat, FromIntegralCat
  , EqCat, OrdCat, EnumCat, BottomCat, IfCat, UnknownCat, RepCat
  , ccc
  )

import qualified ConCat.Category as C
import ConCat.Rep

#define Op(nm,ty) \
nm :: ty; \
nm = C.nm ;\
{-# NOINLINE [2] nm #-}

#define InfixOp(nm,ty) \
(nm) :: ty; \
(nm) = (C.nm) ;\
{-# NOINLINE [2] (nm) #-}


infixr 9 .
Op(id,(Category k, Ok k a) => a `k` a)
InfixOp(.,forall k b c a. (Category k, Ok3 k a b c) => (b `k` c) -> (a `k` b) -> (a `k` c))

infixr 3 ***, &&&
Op(exl,(ProductCat k, Ok2 k a b) => Prod k a b `k` a)
Op(exr,(ProductCat k, Ok2 k a b) => Prod k a b `k` b)
InfixOp(&&&,forall k a c d. (ProductCat k, Ok3 k a c d) => (a `k` c) -> (a `k` d) -> (a `k` Prod k c d))
InfixOp(***,forall k a b c d. (ProductCat k, Ok4 k a b c d) => (a `k` c) -> (b `k` d) -> (Prod k a b `k` Prod k c d))
Op(swapP,forall k a b. (ProductCat k, Ok2 k a b) => Prod k a b `k` Prod k b a)
Op(first,forall k a aa b. (ProductCat k, Ok3 k a b aa) => (a `k` aa) -> (Prod k a b `k` Prod k aa b))
Op(second,forall k a b bb. (ProductCat k, Ok3 k a b bb) => (b `k` bb) -> (Prod k a b `k` Prod k a bb))
Op(lassocP,forall k a b c. (ProductCat k, Ok3 k a b c) => Prod k a (Prod k b c) `k` Prod k (Prod k a b) c)
Op(rassocP,forall k a b c. (ProductCat k, Ok3 k a b c) => Prod k (Prod k a b) c `k` Prod k a (Prod k b c))

infixr 2 +++, |||
Op(inl,(CoproductCat k, Ok2 k a b) => a `k` Coprod k a b)
Op(inr,(CoproductCat k, Ok2 k a b) => b `k` Coprod k a b)
InfixOp(|||,forall k a c d. (CoproductCat k, Ok3 k a c d) => (c `k` a) -> (d `k` a) -> (Coprod k c d `k` a))
InfixOp(+++,forall k a b c d. (CoproductCat k, Ok4 k a b c d) => (c `k` a) -> (d `k` b) -> (Coprod k c d `k` Coprod k a b))
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


