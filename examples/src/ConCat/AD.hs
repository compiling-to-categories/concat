{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ConstraintKinds #-}
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
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation

module ConCat.AD where

import Prelude hiding (id,(.),curry,uncurry,const,unzip)

import GHC.Generics(Par1(..),(:.:)(..))
import Control.Newtype (unpack)
import Data.Distributive (Distributive(..))
-- import Data.Key (Zip(..))
import Data.Constraint ((\\))

import ConCat.Misc ((:*),Yes1)
import ConCat.Free.VectorSpace (HasV(..),VComp(..))
import ConCat.Free.LinearRow
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat
-- import ConCat.Free.Diagonal (diagF)
import ConCat.GAD

-- Differentiable functions
type D s = GD (L s)

type instance GDOk (L s) = Yes1

-- instance ClosedCat (D s) where
--   apply = applyD
-- --   curry = curryD

-- applyD :: forall s a b. Ok2 (D s) a b => D s ((a -> b) :* a) b
-- applyD = D (\ (f,a) -> let (b,f') = andDeriv f a in
--               (b, _))

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
  powIC   = notDef "powC"       -- TODO
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}
  -- subC = addC . second negateC -- experiment: same as default
  -- {-# INLINE subC    #-}

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

-- instance (OkLF h, VComp h) => LinearCat (D s) h where
--   fmapC :: forall a b. Ok2 (D s) a b => D s a b -> D s (h a) (h b)
--   fmapC (D f) = D (second (L . pushH . mkDiag) . unzip . fmap f)
--    where
--      pushH :: h (h (V s b (V s a s))) -> V s (h b) (V s (h a) s)
--      pushH = fmap Comp1 . Comp1 . fmap distribute
--                \\ vcomp @h @s @a
--                \\ vcomp @h @s @b
--      mkDiag :: h (L s a b) -> h (h (V s b (V s a s)))
--      mkDiag = diagF zeroL . fmap unpack
--   zipC = linearD zipC zipC
--   sumC = linearD sumC sumC

#if 0

fmap unpack :: h (L s a b) -> h (V s b (V s a s))
      zeroL :: V s b (V s a s)
diagF zeroL :: h (V s b (V s a s)) -> h (h (V s b (V s a s)))

fmap distribute    :: h (h (V s b (V s a s))) -> h (V s b (h (V s a s)))
Comp1 . distribute :: ... -> (h :.: V s b) (h (V s a s))
fmap Comp1         :: ... -> (h :.: V s b) ((h :.: V s a) s)
                   :: ... -> V s (h b) (V s (h a) s)

f :: a -> b :* L s a b

L . pushH . mkDiag :: h (L s a b) -> L s (h a) (h b)

fmap f                      :: h a -> h (b :* L s a b)
unzip                       :: ... -> h b :* h (L s a b)
second (L . pushH . mkDiag) :: ... -> h b :* L s (h a) (h b)

#endif

-- diagF zeroLM fs'

-- diagF :: (Applicative f, Keyed f, Adjustable f) => a -> f a -> f (f a)

-- TODO: Generalize from D s to GD k. zipC and sumC come easily, but maybe I
-- need to generalize diagF to a method.

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

-- andDer :: forall a b . (a -> b) -> (a -> b :* LR a b)
andDer :: forall s a b . (a -> b) -> (a -> b :* L s a b)
andDer = andDeriv
{-# INLINE andDer #-}

der :: forall s a b . (a -> b) -> (a -> L s a b)
der = deriv
{-# INLINE der #-}

type IsScalar s = V s s ~ Par1

gradient :: (HasV s a, IsScalar s) => (a -> s) -> a -> a
-- gradient :: HasV R a => (a -> R) -> a -> a
gradient f = gradientD (toCcc f)
{-# INLINE gradient #-}

gradientD :: (HasV s a, IsScalar s) => D s a s -> a -> a
-- gradientD :: HasV R a => D R a R -> a -> a
gradientD (D h) = unV . unPar1 . unpack . snd . h
{-# INLINE gradientD #-}


--                             f :: a -> s
--                         der f :: a -> L s a s
--                unpack . der f :: a -> V s s (V s a s)
--                               :: a -> Par1 (V s a s)
--       unPar1 . unpack . der f :: a -> V s a s
-- unV . unPar1 . unpack . der f :: a -> a

