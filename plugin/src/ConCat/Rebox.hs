{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -Wno-orphans -Wno-inline-rule-shadowing #-}

-- | Reboxing experiments

module ConCat.Rebox where

import Prelude hiding (curry)

import GHC.Types
import GHC.Prim
import GHC.Integer

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
"boxF cos" forall u    . boxF (cosFloat# u)       = cosC (boxF u)
"boxF sin" forall u    . boxF (sinFloat# u)       = sinC (boxF u)

"boxD i2D"    forall n . boxD (int2Double# n)     = fromIntegralC (boxI n)
"boxD negate" forall u . boxD (negateDouble# u)   = negateC (boxD u)
"boxD +" forall u v    . boxD (u +## v)           = addC (boxD u,boxD v)
"boxD -" forall u v    . boxD (u -## v)           = subC (boxD u,boxD v)
"boxD *" forall u v    . boxD (u *## v)           = mulC (boxD u,boxD v)
"boxD exp" forall u    . boxD (expDouble# u)      = expC (boxD u)
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


-- Handy for translating case-of-Int#
ifEqInt# :: Int# -> Int# -> a -> a -> a
ifEqInt# m n a b = if equal (boxI m, boxI n) then a else b
{-# INLINE ifEqInt# #-}
