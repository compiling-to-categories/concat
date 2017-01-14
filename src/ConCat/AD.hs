{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation

module ConCat.AD where

import Prelude hiding (id,(.),curry,uncurry,const)

import ConCat.Misc ((:*))
import ConCat.Free.LinearRow
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat

import ConCat.GAD

-- Differentiable functions
type D s = GD (L s)

instance Num s => TerminalCat (D s) where
  it = linearD (const ()) zeroLM
  {-# INLINE it #-}

instance Ok (L s) b => ConstCat (D s) b where
  const b = D (const (b, zeroLM))
  {-# INLINE const #-}

instance Ok (L s) s => NumCat (D s) s where
  negateC = linearD negateC (scale (-1))
  addC    = linearD addC    jamLM
  mulC    = D (mulC &&& (\ (a,b) -> scale b `joinLM` scale a))
  powIC   = notDef "powC"
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

const' :: (a -> c) -> (a -> b -> c)
const' = (const .)

scalarD :: Ok (L s) s => (s -> s) -> (s -> s -> s) -> D s s s
scalarD f d = D (\ x -> let r = f x in (r, scale (d x r)))
{-# INLINE scalarD #-}

-- Use scalarD with const f when only r matters and with const' g when only x
-- matters.

scalarR :: Ok (L s) s => (s -> s) -> (s -> s) -> D s s s
scalarR f f' = scalarD f (\ _ -> f')
-- scalarR f x = scalarD f (const x)
-- scalarR f = scalarD f . const
{-# INLINE scalarR #-}

scalarX :: Ok (L s) s => (s -> s) -> (s -> s) -> D s s s
scalarX f f' = scalarD f (\ x _ -> f' x)
-- scalarX f f' = scalarD f (\ x y -> const (f' x) y)
-- scalarX f f' = scalarD f (\ x -> const (f' x))
-- scalarX f f' = scalarD f (const . f')
-- scalarX f f' = scalarD f (const' f')
-- scalarX f = scalarD f . const'
{-# INLINE scalarX #-}

square :: Num a => a -> a
square a = a * a
{-# INLINE square #-}

instance (Ok (L s) s, Fractional s) => FractionalCat (D s) s where
  recipC = scalarR recip (negate . square)
  {-# INLINE recipC #-}

instance (Ok (L s) s, Floating s) => FloatingCat (D s) s where
  expC = scalarR exp id
  sinC = scalarX sin cos
  cosC = scalarX cos (negate . sin)
  {-# INLINE expC #-}
  {-# INLINE sinC #-}
  {-# INLINE cosC #-}

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

andDer :: forall a b . (a -> b) -> (a -> b :* LR a b)
andDer = andDeriv
{-# NOINLINE andDer #-}
{-# RULES "andDer" andDer = andDeriv #-}
-- {-# ANN andDer PseudoFun #-}

der :: forall a b . (a -> b) -> (a -> LR a b)
der = deriv
{-# NOINLINE der #-}
{-# RULES "der" der = deriv #-}
-- {-# ANN der PseudoFun #-}
