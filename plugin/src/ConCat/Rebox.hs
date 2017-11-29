{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

-- For Catify etc
#include "ConCat/Ops.inc"

-- | Reboxing experiments

module ConCat.Rebox where

import Prelude hiding (id,(.),curry,uncurry)
import qualified Prelude as P
import qualified Control.Arrow as P
import Data.Tuple (swap)
import GHC.Types
import GHC.Prim
import GHC.Integer

import ConCat.Misc (xor)
import ConCat.AltCat

boxI :: Int# -> Int
boxI = I#
{-# INLINE [0] boxI #-}

boxF :: Float# -> Float
boxF = F#
{-# INLINE [0] boxF #-}

boxD :: Double# -> Double
boxD = D#
{-# INLINE [0] boxD #-}

boxIB :: Int# -> Bool
boxIB i = tagToEnum# i
{-# INLINE [0] boxIB #-}

unboxF :: Float -> Float#
unboxF (F# f#) = f#
-- {-# INLINE [0] unboxF #-}

unboxD :: Double -> Double#
unboxD (D# d#) = d#
-- {-# INLINE [0] unboxD #-}

unboxI :: Int -> Int#
unboxI (I# i#) = i#
-- {-# INLINE [0] unboxI #-}

unboxIB :: Bool -> Int#
unboxIB i = unboxI (fromEnum i)
-- {-# INLINE [0] unboxIB #-}

-- Handy for translating case-of-Int#
ifEqInt# :: Int# -> Int# -> a -> a -> a
ifEqInt# m n a b = if equal (boxI m, boxI n) then a else b
{-# INLINE ifEqInt# #-}

#if 1

#define Rebox1(box,unbox,uop,bop) \
  "rebox2" [~0] uop = \ u# -> unbox (bop (box u#))

#define Rebox2(box,unbox,uop,bop) \
  "rebox2" [~0] uop = \ u# v# -> unbox (bop (box u#) (box v#))

#define ReboxB2(box,uop,bop) Rebox2(box,unboxIB,uop,bop)

#define Rebox1I(uop,bop) Rebox1(boxI,unboxI,uop,bop)
#define Rebox1F(uop,bop) Rebox1(boxF,unboxF,uop,bop)
#define Rebox1D(uop,bop) Rebox1(boxD,unboxD,uop,bop)

#define Rebox2I(uop,bop) Rebox2(boxI,unboxI,uop,bop)
#define Rebox2F(uop,bop) Rebox2(boxF,unboxF,uop,bop)
#define Rebox2D(uop,bop) Rebox2(boxD,unboxD,uop,bop)

#define ReboxB2I(uop,bop) ReboxB2(boxI,uop,bop)
#define ReboxB2F(uop,bop) ReboxB2(boxF,uop,bop)
#define ReboxB2D(uop,bop) ReboxB2(boxD,uop,bop)

{-# RULES

ReboxB2I((==#),(==))
ReboxB2I((/=#),(/=))
ReboxB2I(( >#) ,(>))
ReboxB2I(( <#) ,(<))
ReboxB2I((>=#),(>=))
ReboxB2I((<=#),(<=))

ReboxB2F(eqFloat#,(==))
ReboxB2F(neFloat#,(/=))
ReboxB2F(gtFloat#,( >))
ReboxB2F(geFloat#,( <))
ReboxB2F(ltFloat#,(>=))
ReboxB2F(leFloat#,(<=))

ReboxB2D((==##),(==))
ReboxB2D((/=##),(/=))
ReboxB2D(( >##) ,(>))
ReboxB2D(( <##) ,(<))
ReboxB2D((>=##),(>=))
ReboxB2D((<=##),(<=))

Rebox1I(negateInt#,negate)
Rebox2I((+#),(+))
Rebox2I((-#),(-))
Rebox2I((*#),(*))
-- Rebox1(boxD,unboxI,double2Int#,truncate)
Rebox1(boxD,unboxI,double2Int#,truncateC)
Rebox1(boxF,unboxI,float2Int#,truncateC)

-- Generating truncateC instead of truncate to avoid an infinite rewrite loop
-- between these rules and GHC's "truncate/Double->Int" and
-- "truncate/Float->Int" rule. Maybe change all of the generated functions to be
-- the categorical versions to more robustly avoid such loops. This change would
-- make rewriting a little more efficient as well, since operations like
-- truncate would get rewritten to their counterparts like truncateC anyway.

Rebox1F(negateFloat#,negate)
Rebox2F(plusFloat#,(+))
Rebox2F(minusFloat#,(-))
Rebox2F(timesFloat#,(*))
Rebox2F(divideFloat#,(/))
Rebox1F(sinFloat#,sin)
Rebox1F(cosFloat#,cos)
Rebox1F(expFloat#,exp)
Rebox1F(logFloat#,log)
Rebox1(boxI,unboxF,int2Float#,fromIntegralC)

Rebox1D(negateDouble#,negate)
Rebox2D((+##),(+))
Rebox2D((-##),(-))
Rebox2D((*##),(*))
Rebox2D((/##),(/))
Rebox1D(sinDouble#,sin)
Rebox1D(cosDouble#,cos)
Rebox1D(expDouble#,exp)
Rebox1D(logDouble#,log)
Rebox2D((**##),(**))
Rebox1(boxI,unboxD,int2Double#,fromIntegralC)

-- fromIntegralC to avoid looping with GHC's fromIntegral/Int->Float and
-- fromIntegral/Int->Double

Rebox2(id,unboxIB, eqInteger#,(==))
Rebox2(id,unboxIB,neqInteger#,(/=))
Rebox2(id,unboxIB, geInteger#,(> ))
Rebox2(id,unboxIB, ltInteger#,(< ))
Rebox2(id,unboxIB, gtInteger#,(>=))
Rebox2(id,unboxIB, leInteger#,(<=))

 #-}

#else

{-# RULES

"boxI ==" forall u v   . boxIB (u ==# v)          = equal              (boxI u,boxI v)
"boxI /=" forall u v   . boxIB (u /=# v)          = notEqual           (boxI u,boxI v)
"boxI >"  forall u v   . boxIB (u >#  v)          = greaterThan        (boxI u,boxI v)
"boxI >=" forall u v   . boxIB (u >=# v)          = greaterThanOrEqual (boxI u,boxI v)
"boxI <"  forall u v   . boxIB (u <#  v)          = lessThan           (boxI u,boxI v)
"boxI <=" forall u v   . boxIB (u <=# v)          = lessThanOrEqual    (boxI u,boxI v)

"boxF ==" forall u v   . boxIB (u `eqFloat#` v)   = equal              (boxF u,boxF v)
"boxF /=" forall u v   . boxIB (u `neFloat#` v)   = notEqual           (boxF u,boxF v)
"boxF >"  forall u v   . boxIB (u `gtFloat#` v)   = greaterThan        (boxF u,boxF v)
"boxF >=" forall u v   . boxIB (u `geFloat#` v)   = greaterThanOrEqual (boxF u,boxF v)
"boxF <"  forall u v   . boxIB (u `ltFloat#` v)   = lessThan           (boxF u,boxF v)
"boxF <=" forall u v   . boxIB (u `leFloat#` v)   = lessThanOrEqual    (boxF u,boxF v)

"boxD ==" forall u v   . boxIB (u ==## v)         = equal              (boxD u,boxD v)
"boxD /=" forall u v   . boxIB (u /=## v)         = notEqual           (boxD u,boxD v)
"boxD >"  forall u v   . boxIB (u >##  v)         = greaterThan        (boxD u,boxD v)
"boxD >=" forall u v   . boxIB (u >=## v)         = greaterThanOrEqual (boxD u,boxD v)
"boxD <"  forall u v   . boxIB (u <##  v)         = lessThan           (boxD u,boxD v)
"boxD <=" forall u v   . boxIB (u <=## v)         = lessThanOrEqual    (boxD u,boxD v)

-- TODO: shorten the OrdCat names

"boxI negate" forall u . boxI (negateInt# u)      = negateC (boxI u)
"boxI +" forall u v    . boxI (u +# v)            = addC (boxI u,boxI v)
"boxI -" forall u v    . boxI (u -# v)            = subC (boxI u,boxI v)
"boxI *" forall u v    . boxI (u *# v)            = mulC (boxI u,boxI v)
"boxI trunc" forall u  . boxI (double2Int# u)     = truncateC (boxD u)

"boxF negate" forall u . boxF (negateFloat# u)    = negateC (boxF u)
"boxF +" forall u v    . boxF (u `plusFloat#`  v) = addC (boxF u,boxF v)
"boxF -" forall u v    . boxF (u `minusFloat#` v) = subC (boxF u,boxF v)
"boxF *" forall u v    . boxF (u `timesFloat#` v) = mulC (boxF u,boxF v)
"boxF exp" forall u    . boxF (expFloat# u)       = expC (boxF u)
"boxF log" forall u    . boxF (logFloat# u        = logC(boxF u)
"boxF cos" forall u    . boxF (cosFloat# u)       = cosC (boxF u)
"boxF sin" forall u    . boxF (sinFloat# u)       = sinC (boxF u)

"boxD i2D"    forall n . boxD (int2Double# n)     = fromIntegralC (boxI n)
"boxD negate" forall u . boxD (negateDouble# u)   = negateC (boxD u)
"boxD +" forall u v    . boxD (u +## v)           = addC (boxD u,boxD v)
"boxD -" forall u v    . boxD (u -## v)           = subC (boxD u,boxD v)
"boxD *" forall u v    . boxD (u *## v)           = mulC (boxD u,boxD v)
"boxD exp" forall u    . boxD (expDouble# u)      = expC (boxD u)
"boxD log" forall u    . boxD (logDouble# u)      = logC (boxD u)
"boxD cos" forall u    . boxD (cosDouble# u)      = cosC (boxD u)
"boxD sin" forall u    . boxD (sinDouble# u)      = sinC (boxD u)

-- These two don't work:

-- "boxF /" forall u v. boxF (u `divideFloat#` v) = divideC (boxF u,boxF v)
-- "boxD /" forall u v. boxD (u /## v) = divideC (boxD u,boxD v)

--     RULE left-hand side too complicated to desugar
--       Optimised lhs: case /## u v of wild_00 { __DEFAULT ->
--                      boxD wild_00
--                      }
--       Orig lhs: case /## u v of wild_00 { __DEFAULT -> boxD wild_00 }

-- /## 1.0## (cosDouble# x)

"boxD /" [~0] forall u v. u /## v            = unboxD (divideC (boxD u, boxD v))
"boxF /" [~0] forall u v. u `divideFloat#` v = unboxF (divideC (boxF u, boxF v))

-- TODO: Maybe change all the the reboxing rules to this style. Or maybe not,
-- since it's not driven by ccc, and hence could easily degrade all numeric
-- performance.

-- TODO: maybe change all of the rules to [~0].

-- Also problematic:

-- "boxZ ==" forall u v . boxIB (eqInteger# u v) = equal (u,v)

-- RULE left-hand side too complicated to desugar
--   Optimised lhs: case eqInteger# u v of wild_00 { __DEFAULT ->
--                  boxIB wild_00
--                  }
--   Orig lhs: case eqInteger# u v of wild_00 { __DEFAULT ->
--             boxIB wild_00
--             }

-- Integer numeric operations. Move elsewhere?

"eqInteger     cat" [~0] eqInteger     = curry equal
"neqInteger    cat" [~0] neqInteger    = curry notEqual
"leInteger     cat" [~0] leInteger     = curry lessThanOrEqual
"ltInteger     cat" [~0] ltInteger     = curry lessThan
"gtInteger     cat" [~0] gtInteger     = curry greaterThan
"geInteger     cat" [~0] geInteger     = curry greaterThanOrEqual

"negateInteger cat" [~0] negateInteger = negateC
"plusInteger   cat" [~0] plusInteger   = curry addC
"minusInteger  cat" [~0] minusInteger  = curry subC
"timesInteger  cat" [~0] timesInteger  = curry mulC

-- We don't yet have categorical versions of the following, but we will.

-- "absInteger    cat" [~0] absInteger    = 
-- "signumInteger cat" [~0] signumInteger = 

-- "quotInteger   cat" [~0] quotInteger   = 
-- "remInteger    cat" [~0] remInteger    = 
-- "divInteger    cat" [~0] divInteger    = 
-- "modInteger    cat" [~0] modInteger    = 
-- "gcdInteger    cat" [~0] gcdInteger    = 
-- "lcmInteger    cat" [~0] lcmInteger    = 

-- We also see the # versions in some optimized code.

"boxZ ==" [~0] forall u v . eqInteger#  u v  = unboxIB (equal              (u,v))
"boxZ /=" [~0] forall u v . neqInteger# u v  = unboxIB (notEqual           (u,v))
"boxZ >"  [~0] forall u v . gtInteger#  u v  = unboxIB (greaterThan        (u,v))
"boxZ >=" [~0] forall u v . geInteger#  u v  = unboxIB (greaterThanOrEqual (u,v))
"boxZ <"  [~0] forall u v . ltInteger#  u v  = unboxIB (lessThan           (u,v))
"boxZ <=" [~0] forall u v . leInteger#  u v  = unboxIB (lessThanOrEqual    (u,v))

 #-}

-- The float/double division reboxing scheme works without the INLINE pragmas or
-- with INLINE [1-4], but gives the following warning with INLINE [0]:

{-

ghc: panic! (the 'impossible' happened)
  (GHC version 8.0.2 for x86_64-apple-darwin):
	ccc post-transfo check. Lint
      [RHS of wild1_agZn :: Double#]
      The type of this binder is primitive: wild1_agZn
      Binder's type: Double#
  ccc
    @ Syn
    @ (R, R2)
    @ Bool
    (\ (x_eta_Bh :: (R, R2)) ->
       case unboxD
              (divideC
                 @ (->)
                 @ Double
                 ($fFractionalCat(->)a @ Double $fFractionalDouble)
                 (boxD 1.0##,
                  cosC
                    @ (->)
                    @ Double
                    ($fFloatingCat(->)a @ Double $fFloatingDouble)
                    (exl
                       @ (->)
                       @ R
                       @ R2
                       $fProductCat(->)
                       ...
                       x_eta_Bh)))
       of wild1_agZn { __DEFAULT ->

-}

-- When I turn off lintSteps in ConCat.Plugin, we get into an infinite
-- unfolding/reboxing loop. I tried the following rules
-- 
-- "D# . unboxD" forall u. D# (unboxD u) = u
-- "F# . unboxF" forall u. F# (unboxF u) = u
-- 
-- but
-- 
--     RULE left-hand side too complicated to desugar
--       Optimised lhs: case unboxD u of wild_00 { __DEFAULT ->
--                      GHC.Types.D# wild_00 }


#endif

{--------------------------------------------------------------------
    Capture class ops
--------------------------------------------------------------------}

#if 1

-- Now in Ops.inc
-- -- Basic
-- #define Catify(op,meth) {-# RULES "catify" [~0] op = meth #-}
-- -- Same name as in Prelude
-- #define CatifyP(nm)  Catify(P.nm,nm)
-- #define CatifyPI(op) Catify((P.op),(op))
-- -- Curried
-- #define CatifyC(op,meth) Catify(op,curry (meth))

#if 0

CatifyP(id)
CatifyPI(.)

Catify(fst,exl)
Catify(snd,exr)

-- Function-specialize arrow methods. Or drop them.
Catify((P.&&&) @(->),(&&&))
Catify((P.***) @(->),(***))
Catify(P.first,first)
Catify(P.second,second)

Catify(Left,inl)
Catify(Right,inr)

Catify((P.|||) @(->),(|||))
Catify((P.+++) @(->),(+++))
Catify(P.left,left)
Catify(P.right,right)

CatifyP(curry)
CatifyP(uncurry)

#endif

Catify(swap,swapP)

-- The catifies above are unnecessary, since the plugin can inlinine and
-- re-discover the categorical version.

Catify(not,notC)
CatifyC((&&),andC)
CatifyC((||),orC)
CatifyC(xor,xorC)

CatifyC((==),equal)
CatifyC((/=),notEqual)

CatifyC((<),lessThan)
CatifyC((>),greaterThan)
CatifyC((<=),lessThanOrEqual)
CatifyC((>=),greaterThanOrEqual)

Catify(succ,succC)
Catify(pred,predC)

Catify(negate,negateC)
CatifyC((+),addC)
CatifyC((-),subC)
CatifyC((*),mulC)
CatifyC((^),powIC)

CatifyC(div,divC)
CatifyC(mod,modC)

Catify(recip,recipC)
CatifyC((/),divideC)

Catify(exp,expC)
Catify(log,logC)
Catify(cos,cosC)
Catify(sin,sinC)
Catify((**),pow)

-- u ** v == exp (log (u ** v)) == exp (v * log u)  -- log is base in Haskell
pow :: Floating a => a -> a -> a
u `pow` v = exp (v * log u)
{-# INLINE pow #-}

Catify(floor,floorC)
Catify(ceiling,ceilingC)
Catify(truncate,truncateC)

Catify(fromIntegral,fromIntegralC)

-- ifThenElse? where is it?

-- RepCat?
-- CoerceCat?

#endif

-- Maybe move elsewhere

{-# RULES

"pair fst snd" forall p. (,) (exl p) (exr p) = p

"curry apply 2" forall f a b. curry f a b = f (a,b)

"swap" forall p. (,) (exr p) (exl p) = swap p

 #-}
