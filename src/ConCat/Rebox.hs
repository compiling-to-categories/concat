{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -Wno-orphans -Wno-inline-rule-shadowing #-}

-- | Reboxing experiments

module ConCat.Rebox where

import GHC.Types
import GHC.Prim

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

{-# RULES

"boxI negate" forall u. boxI (negateInt# u) = negateC (boxI u)
"boxI +" forall u v. boxI (u +# v) = addC (boxI u,boxI v)
"boxI -" forall u v. boxI (u -# v) = subC (boxI u,boxI v)
"boxI *" forall u v. boxI (u *# v) = mulC (boxI u,boxI v)

"boxF negate" forall u. boxF (negateFloat# u) = negateC (boxF u)
"boxF +" forall u v. boxF (u `plusFloat#`  v) = addC (boxF u,boxF v)
"boxF -" forall u v. boxF (u `minusFloat#` v) = subC (boxF u,boxF v)
"boxF *" forall u v. boxF (u `timesFloat#` v) = mulC (boxF u,boxF v)
"boxF /" forall u v. boxF (u `divideFloat#` v) = divideC (boxF u,boxF v)
"boxF exp" forall u. boxF (expFloat# u) = expC (boxF u)
"boxF cos" forall u. boxF (cosFloat# u) = cosC (boxF u)
"boxF sin" forall u. boxF (sinFloat# u) = sinC (boxF u)

"boxD negate" forall u. boxD (negateDouble# u) = negateC (boxD u)
"boxD +" forall u v. boxD (u +## v) = addC (boxD u,boxD v)
"boxD -" forall u v. boxD (u -## v) = subC (boxD u,boxD v)
"boxD *" forall u v. boxD (u *## v) = mulC (boxD u,boxD v)
"boxD /" forall u v. boxD (u /## v) = divideC (boxD u,boxD v)
"boxD exp" forall u. boxD (expDouble# u) = expC (boxD u)
"boxD cos" forall u. boxD (cosDouble# u) = cosC (boxD u)
"boxD sin" forall u. boxD (sinDouble# u) = sinC (boxD u)

 #-}

--     RULE left-hand side too complicated to desugar
--       Optimised lhs: case /## u v of wild_00 { __DEFAULT ->
--                      boxD wild_00
--                      }
--       Orig lhs: case /## u v of wild_00 { __DEFAULT -> boxD wild_00 }

-- To do:
#if 0

rebox :: a -> a
rebox x = x
{-# INLINE [0] rebox #-}

{-# RULES

"rebox /" forall u v. rebox (D# (u /## v)) = divideC (boxD u,boxD v)

 #-}
  
#endif
