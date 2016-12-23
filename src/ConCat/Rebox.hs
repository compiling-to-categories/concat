{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# OPTIONS_GHC -Wno-orphans -Wno-inline-rule-shadowing #-}

-- | Some experiments with reboxing

{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

module ConCat.Rebox where

import GHC.Types
import GHC.Prim

fooI :: Int -> Int
fooI x = 3 * x + x

barI :: Int -> Int -> Int
barI x y = 3 * x + y + 7

fooI' :: Int -> Int
fooI' = fooI . reI

mkI :: Int# -> Int
mkI = I#
{-# NOINLINE mkI #-}

unI :: Int -> Int#
unI (I# x) = x
-- {-# NOINLINE unI #-}

fooI'' :: Int -> Int
fooI'' x  = fooI (mkI (unI x))

-- fooF :: Float -> Float
-- fooF x = 3 * x + x

reI :: Int -> Int
reI y = I# (unI y)
-- reI (I# x) = I# x
{-# INLINE reI #-}

#if 1

plusI :: Int -> Int -> Int
plusI = (+)
{-# NOINLINE plusI #-}

timesI :: Int -> Int -> Int
timesI = (+)
{-# NOINLINE timesI #-}

{-# RULES

"I# +" forall u v. I# (u +# v) = I# u `plusI` I# v
"I# *" forall u v. I# (u *# v) = I# u `timesI` I# v

-- "F# +" forall u v. F# (u `plusFloat#` v) = F# u `addF` F# v
-- "F# *" forall u v. F# (u `timesFloat#` v) = F# u `timesF` F# v

 #-}

#endif
