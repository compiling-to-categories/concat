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

import Prelude hiding (id,(.),curry,uncurry,const)
import qualified Prelude as P
import qualified Control.Arrow as P
import Data.Tuple (swap)
import GHC.Types
import GHC.Prim
import GHC.Integer
import GHC.Float

import ConCat.Misc (xor,cond)
import ConCat.Additive((^+^))
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
  "rebox2" [~0] uop = \ u# v# -> unbox (bop (box u#,box v#))

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

ReboxB2I((==#),equal)
ReboxB2I((/=#),notEqual)
ReboxB2I(( >#),greaterThan)
ReboxB2I(( <#),lessThan)
ReboxB2I((>=#),greaterThanOrEqual)
ReboxB2I((<=#),lessThanOrEqual)

ReboxB2F(eqFloat#,equal)
ReboxB2F(neFloat#,notEqual)
ReboxB2F(gtFloat#,greaterThan)
ReboxB2F(geFloat#,greaterThanOrEqual)
ReboxB2F(ltFloat#,lessThan)
ReboxB2F(leFloat#,lessThanOrEqual)

ReboxB2D((==##),equal)
ReboxB2D((/=##),notEqual)
ReboxB2D(( >##),greaterThan)
ReboxB2D(( <##),lessThan)
ReboxB2D((>=##),greaterThanOrEqual)
ReboxB2D((<=##),lessThanOrEqual)

Rebox1I(negateInt#,negateC)
Rebox2I((+#),addC)
Rebox2I((-#),subC)
Rebox2I((*#),mulC)
-- Rebox1(boxD,unboxI,double2Int#,truncate)
Rebox1(boxD,unboxI,double2Int#,truncateC)
Rebox1(boxF,unboxI,float2Int#,truncateC)

-- Generating truncateC instead of truncate to avoid an infinite rewrite loop
-- between these rules and GHC's "truncate/Double->Int" and
-- "truncate/Float->Int" rule. Maybe change all of the generated functions to be
-- the categorical versions to more robustly avoid such loops. This change would
-- make rewriting a little more efficient as well, since operations like
-- truncate would get rewritten to their counterparts like truncateC anyway.

Rebox1F(negateFloat#,negateC)
Rebox2F(plusFloat#,addC)
Rebox2F(minusFloat#,subC)
Rebox2F(timesFloat#,mulC)
Rebox2F(divideFloat#,divideC)
Rebox1F(sinFloat#,sinC)
Rebox1F(sqrtFloat#,sqrtC)
Rebox1F(cosFloat#,cosC)
Rebox1F(expFloat#,expC)
Rebox1F(logFloat#,logC)
Rebox1(boxI,unboxF,int2Float#,fromIntegralC)

Rebox1D(negateDouble#,negateC)
Rebox2D((+##),addC)
Rebox2D((-##),subC)
Rebox2D((*##),mulC)
Rebox2D((/##),divideC)
Rebox1D(sinDouble#,sinC)
Rebox1D(sqrtDouble#,sqrtC)
Rebox1D(cosDouble#,cosC)
Rebox1D(expDouble#,expC)
Rebox1D(logDouble#,logC)
Rebox2D((**##),uncurry pow)
Rebox1(boxI,unboxD,int2Double#,fromIntegralC)

-- fromIntegralC to avoid looping with GHC's fromIntegral/Int->Float and
-- fromIntegral/Int->Double

Rebox2(id,unboxIB, eqInteger#,equal)
Rebox2(id,unboxIB,neqInteger#,notEqual)
Rebox2(id,unboxIB, geInteger#,greaterThanOrEqual)
Rebox2(id,unboxIB, ltInteger#,lessThan)
Rebox2(id,unboxIB, gtInteger#,greaterThan)
Rebox2(id,unboxIB, leInteger#,lessThanOrEqual)

 #-}

#else

{-# RULES

"boxI ==" [~0] forall u v   . boxIB (u ==# v)        = equal              (boxI u,boxI v)
"boxI /=" [~0] forall u v   . boxIB (u /=# v)        = notEqual           (boxI u,boxI v)
"boxI >"  [~0] forall u v   . boxIB (u >#  v)        = greaterThan        (boxI u,boxI v)
"boxI >=" [~0] forall u v   . boxIB (u >=# v)        = greaterThanOrEqual (boxI u,boxI v)
"boxI <"  [~0] forall u v   . boxIB (u <#  v)        = lessThan           (boxI u,boxI v)
"boxI <=" [~0] forall u v   . boxIB (u <=# v)        = lessThanOrEqual    (boxI u,boxI v)

"boxF ==" [~0] forall u v   . boxIB (u `eqFloat#` v) = equal              (boxF u,boxF v)
"boxF /=" [~0] forall u v   . boxIB (u `neFloat#` v) = notEqual           (boxF u,boxF v)
"boxF >"  [~0] forall u v   . boxIB (u `gtFloat#` v) = greaterThan        (boxF u,boxF v)
"boxF >=" [~0] forall u v   . boxIB (u `geFloat#` v) = greaterThanOrEqual (boxF u,boxF v)
"boxF <"  [~0] forall u v   . boxIB (u `ltFloat#` v) = lessThan           (boxF u,boxF v)
"boxF <=" [~0] forall u v   . boxIB (u `leFloat#` v) = lessThanOrEqual    (boxF u,boxF v)

"boxD ==" [~0] forall u v   . boxIB (u ==## v)       = equal              (boxD u,boxD v)
"boxD /=" [~0] forall u v   . boxIB (u /=## v)       = notEqual           (boxD u,boxD v)
"boxD >"  [~0] forall u v   . boxIB (u >##  v)       = greaterThan        (boxD u,boxD v)
"boxD >=" [~0] forall u v   . boxIB (u >=## v)       = greaterThanOrEqual (boxD u,boxD v)
"boxD <"  [~0] forall u v   . boxIB (u <##  v)       = lessThan           (boxD u,boxD v)
"boxD <=" [~0] forall u v   . boxIB (u <=## v)       = lessThanOrEqual    (boxD u,boxD v)

-- TODO: shorten the OrdCat names

"boxI negate" [~0] forall u   . boxI (negateInt# u)      = negateC (boxI u)
"boxI +"      [~0] forall u v . boxI (u +# v)            = addC (boxI u,boxI v)
"boxI -"      [~0] forall u v . boxI (u -# v)            = subC (boxI u,boxI v)
"boxI *"      [~0] forall u v . boxI (u *# v)            = mulC (boxI u,boxI v)
"boxI trunc"  [~0] forall u   . boxI (double2Int# u)     = truncateC (boxD u)

"boxF negate" [~0] forall u   . boxF (negateFloat# u)    = negateC (boxF u)
"boxF +"      [~0] forall u v . boxF (u `plusFloat#`  v) = addC (boxF u,boxF v)
"boxF -"      [~0] forall u v . boxF (u `minusFloat#` v) = subC (boxF u,boxF v)
"boxF *"      [~0] forall u v . boxF (u `timesFloat#` v) = mulC (boxF u,boxF v)
"boxF exp"    [~0] forall u   . boxF (expFloat# u)       = expC (boxF u)
"boxF log"    [~0] forall u   . boxF (logFloat# u)       = logC(boxF u)
"boxF cos"    [~0] forall u   . boxF (cosFloat# u)       = cosC (boxF u)
"boxF sin"    [~0] forall u   . boxF (sinFloat# u)       = sinC (boxF u)
"boxF sqrt"   [~0] forall u   . boxF (sqrtFloat# u)      = sqrtC (boxF u)

"boxD i2D"    [~0] forall n   . boxD (int2Double# n)     = fromIntegralC (boxI n)
"boxD negate" [~0] forall u   . boxD (negateDouble# u)   = negateC (boxD u)
"boxD +"      [~0] forall u v . boxD (u +## v)           = addC (boxD u,boxD v)
"boxD -"      [~0] forall u v . boxD (u -## v)           = subC (boxD u,boxD v)
"boxD *"      [~0] forall u v . boxD (u *## v)           = mulC (boxD u,boxD v)
"boxD exp"    [~0] forall u   . boxD (expDouble# u)      = expC (boxD u)
"boxD log"    [~0] forall u   . boxD (logDouble# u)      = logC (boxD u)
"boxD cos"    [~0] forall u   . boxD (cosDouble# u)      = cosC (boxD u)
"boxD sin"    [~0] forall u   . boxD (sinDouble# u)      = sinC (boxD u)
"boxD sqrt"   [~0] forall u   . boxD (sqrtDouble# u)     = sqrtC (boxD u)

-- These two don't work:

-- "boxF /" [~0] forall u v. boxF (u `divideFloat#` v) = divideC (boxF u,boxF v)
-- "boxD /" [~0] forall u v. boxD (u /## v) = divideC (boxD u,boxD v)

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

-- "boxZ ==" [~0] forall u v . boxIB (eqInteger# u v) = equal (u,v)

-- RULE left-hand side too complicated to desugar
--   Optimised lhs: case eqInteger# u v of wild_00 { __DEFAULT ->
--                  boxIB wild_00
--                  }
--   Orig lhs: case eqInteger# u v of wild_00 { __DEFAULT ->
--             boxIB wild_00
--             }

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
-- "D# . unboxD" [~0] forall u. D# (unboxD u) = u
-- "F# . unboxF" [~0] forall u. F# (unboxF u) = u
-- 
-- but
-- 
--     RULE left-hand side too complicated to desugar
--       Optimised lhs: case unboxD u of wild_00 { __DEFAULT ->
--                      GHC.Types.D# wild_00 }


#endif

-- Integer numeric operations. Move elsewhere?

{-# RULES

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

#-}

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

-- -- Now that we have better conditional support (including differentiation),
-- -- don't translate min & max. See journal notes 2018-02-10.
-- CatifyC(min,minC)
-- CatifyC(max,maxC)

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
Catify(sqrt,sqrtC)
Catify((**),pow)

-- u ** v == exp (log (u ** v)) == exp (v * log u)  -- log is base in Haskell
pow :: Floating a => a -> a -> a
-- u `pow` v = exp (v * log u)
u `pow` v = expC (mulC (v,logC u))  -- needed for GHC >= 8.2?
{-# INLINE pow #-}

Catify(floor,floorC)
Catify(ceiling,ceilingC)
Catify(truncate,truncateC)

Catify(fromIntegral,fromIntegralC)

-- ifThenElse? where is it?

-- RepCat?
-- CoerceCat?

#endif

CatifyC(plusFloat  , addC)
CatifyC(minusFloat , subC)
CatifyC(timesFloat , mulC)
CatifyC(divideFloat, divideC)
Catify(negateFloat , negate)

CatifyC(gtFloat,greaterThan)
CatifyC(geFloat,greaterThanOrEqual)
CatifyC(ltFloat,lessThan)
CatifyC(leFloat,lessThanOrEqual)

Catify(expFloat,exp)
Catify(logFloat,log)
Catify(sinFloat,sin)
Catify(sqrtFloat,sqrt)
Catify(cosFloat,cos)

CatifyC(plusDouble  , addC)
CatifyC(minusDouble , subC)
CatifyC(timesDouble , mulC)
CatifyC(divideDouble, divideC)
Catify(negateDouble , negateC)

CatifyC(gtDouble,greaterThan)
CatifyC(geDouble,greaterThanOrEqual)
CatifyC(ltDouble,lessThan)
CatifyC(leDouble,lessThanOrEqual)

Catify(expDouble,expC)
Catify(logDouble,logC)
Catify(sinDouble,sinC)
Catify(sqrtDouble,sqrtC)
Catify(cosDouble,cosC)

-- Maybe move elsewhere

{-# RULES

"curry apply 2" forall f a b. curry f a b = f (a,b)

-- GHC 8.2+ says "A constructor, (,), appears as outermost match in RULE lhs.
-- This rule will be ignored."
#if ! MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
"pair fst snd" forall p. (,) (exl p) (exr p) = p
"swap" forall p. (,) (exr p) (exl p) = swap p
#endif

 #-}

-- Others


{-# RULES

-- I haven't seen this one working.
"mulC 1 right" forall f. mulC . (f &&& const 1.0) = f

-- (\ z -> if f z <= g z then g z else f z) --> max . (f &&& g)
-- "if-as-max" forall f g. 
--   ifC . (lessThanOrEqual . (f &&& g) &&& (g &&& f)) = maxC . (f &&& g)

--    • Could not deduce (MinMaxCat k c) arising from a use of ‘maxC’

-- "if-as-max" forall a b.
--   -- if lessThanOrEqual (a,b) then b else a = maxC (a,b)
--   case lessThanOrEqual (a,b) of { False -> a ; True -> b} = maxC (a,b)

"if-as-max" forall a b. cond b a (lessThanOrEqual (a,b)) = max a b

-- Neither if-then-else nor case can be the LHS of a rule.

 #-}

-- -- Notes 2018-01-04, 2018-01-07, and 2018-02-23
-- CatifyC((^+^),jamP)

