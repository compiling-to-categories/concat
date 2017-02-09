{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-} -- for ^+^

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation, representing linear maps as functions.

module ConCat.ADFun2 where

import Prelude hiding (id,(.),curry,uncurry,const)

import Control.Newtype (unpack)
import Data.Key (Zip(..))

import ConCat.Misc ((:*),R,Binop)
-- import ConCat.Free.VectorSpace (HasV(..))
-- import ConCat.Free.LinearRow
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat
-- -- For the addition used in applyD. Consider alternatives.
-- import ConCat.Free.VectorSpace (HasV(..),onV2)
-- import qualified ConCat.Free.VectorSpace as V
import ConCat.Additive

import ConCat.GAD

-- Differentiable functions with linear maps represented as functions
type D = GD (->)

type instance GDOk (->) = Additive

#if 1
instance ClosedCat D where
  apply = D (\ (f,a) -> (f a, \ (df,da) -> df a ^+^ f da))
  curry (D h) = D (\ a -> (curry f a, \ da -> \ b -> f' (a,b) (da,zero)))
   where
     (f,f') = unfork h
#else
instance ClosedCat D where
  apply = applyD
  curry = curryD

applyD :: forall a b. Ok2 D a b => D ((a -> b) :* a) b
applyD = D (\ (f,a) -> (f a, \ (df,da) -> df a ^+^ f da))

curryD :: forall a b c. Ok3 D a b c => D (a :* b) c -> D a (b -> c)
curryD (D h) = D (\ a -> (curry f a, \ da -> \ b -> f' (a,b) (da,zero)))
 where
   (f,f') = unfork h
#endif

#if 0

instance ConstCat D b where
  const b = D (const (b, zeroLM))
  {-# INLINE const #-}

instance Num s => TerminalCat D where
  it = linearD (const ()) zeroLM
  {-# INLINE it #-}

instance Ok (L s) s => NumCat D s where
  negateC = linearD negateC (scale (-1))
  addC    = linearD addC    jamLM
  mulC    = D (mulC &&& (\ (a,b) -> scale b `joinLM` scale a))
  powIC   = notDef "powC"       -- TODO
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

instance (Ok (L s) s, Fractional s) => FractionalCat D s where
  recipC = scalarR recip (negate . square)
  {-# INLINE recipC #-}

instance (Ok (L s) s, Floating s) => FloatingCat D s where
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

gradient :: HasV R a => (a -> R) -> a -> a
gradient f = unV . unpack . unpack . der f
{-# INLINE gradient #-}  -- experiment
-- {-# NOINLINE gradient #-}
-- {-# RULES "gradient" forall f. gradient f = unV . unpack . unpack . der f #-}

--                             f :: a -> R
--                         der f :: a -> L R a R
--                unpack . der f :: a -> V R R (V R a R)
--                               :: a -> Par1 (V R a R)
--       unpack . unpack . der f :: a -> V R a R
-- unV . unpack . unpack . der f :: a -> a

#endif

{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

-- (^+^) :: forall a. (HasV R a, Zip (V R a)) => Binop a
-- (^+^) = onV2 ((V.^+^) :: Binop (V R a R))

-- (^+^) :: forall s a. (HasV s a, Num s, Zip (V s a)) => Binop a
-- (^+^) = onV2 ((V.^+^) :: Binop (V s a s))
