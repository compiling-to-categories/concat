{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds, TypeOperators, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-} -- see comment

-- Needed to define (*) as a type family
{-# LANGUAGE NoStarIsType #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

-- | Simple type-level, Peano-style (unary) natural numbers

module ConCat.Nat where

-- TODO: exports

data Nat = Z | S Nat

-- So we don't need -fno-warn-unticked-promoted-constructors
type Z = 'Z
type S = 'S

infixl 6 +

-- | Sum of type-level numbers
type family (a :: Nat) + (b :: Nat) :: Nat where
  a +  Z  = a
  a + S b = S (a + b)

infixl 6 -

-- Experiment:
-- | Difference of type-level numbers
type family a - b :: Nat where
  n   - Z   = n
  S n - S m = n - m

infixl 7 *

-- | Product of type-level numbers
type family a * b :: Nat where
  a *  Z  = a
  a * S b = a + (a * b)

--     Nested type family application
--       in the type family application: a + (a * b)
--     (Use UndecidableInstances to permit this)
--     In the type instance declaration for ‘*’

infixr 8 ^

-- | Exponentiating type-level numbers
type family a ^ b :: Nat where
  a ^   Z = S Z
  a ^ S b = a * (a ^ b)

type N0  = Z

-- Generated code
-- 
--   putStrLn $ unlines ["type N" ++ show (n+1) ++ " = S N" ++ show n | n <- [0..31]]

type N1  = S N0
type N2  = S N1
type N3  = S N2
type N4  = S N3
type N5  = S N4
type N6  = S N5
type N7  = S N6
type N8  = S N7
type N9  = S N8
type N10 = S N9
type N11 = S N10
type N12 = S N11
type N13 = S N12
type N14 = S N13
type N15 = S N14
type N16 = S N15
type N17 = S N16
type N18 = S N17
type N19 = S N18
type N20 = S N19
type N21 = S N20
type N22 = S N21
type N23 = S N22
type N24 = S N23
type N25 = S N24
type N26 = S N25
type N27 = S N26
type N28 = S N27
type N29 = S N28
type N30 = S N29
type N31 = S N30
type N32 = S N31
