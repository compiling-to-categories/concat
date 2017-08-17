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

module ConCat.ADFun where

import Prelude hiding (id,(.),curry,uncurry,const)

import Control.Newtype (unpack)

import ConCat.Misc ((:*),R,Yes1,oops)
import ConCat.Free.VectorSpace (HasV(..))
import ConCat.Free.LinearRow
-- The following import allows the instances to type-check. Why?
import qualified ConCat.Category as C
import ConCat.AltCat

import Data.Constraint hiding ((&&&),(***),(:=>))

import ConCat.GAD
import ConCat.Additive

-- Differentiable functions
type D = GD (->)

-- type instance GDOk (->) = Yes1

type instance GDOk (->) = Additive

instance OpCon (:*) (Sat Additive) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

instance OpCon (->) (Sat Additive) where
  inOp = Entail (Sub Dict)
  {-# INLINE inOp #-}

#if 0
instance ClosedCat D where
  apply = D (\ (f,a) -> (f a, \ (df,da) -> df a ^+^ deriv f a da))
  curry (D h) = D (\ a -> (curry f a, \ da -> \ b -> f' (a,b) (da,zero)))
   where
     (f,f') = unfork h
  {-# INLINE apply #-}
  {-# INLINE curry #-}

-- TODO: generalize to ClosedCat k for an arbitrary CCC k. I guess I can simply
-- apply ccc to the lambda expressions.
#else
instance ClosedCat D where
  apply = applyD
  curry = curryD
  {-# INLINE apply #-}
  {-# INLINE curry #-}

applyD :: forall a b. Ok2 D a b => D ((a -> b) :* a) b
applyD = D (\ (f,a) -> (f a, \ (df,da) -> df a ^+^ f da))

curryD :: forall a b c. Ok3 D a b c => D (a :* b) c -> D a (b -> c)
curryD (D h) = D (\ a -> (curry f a, \ da -> \ b -> f' (a,b) (da,zero)))
 where
   (f,f') = unfork h

{-# INLINE applyD #-}
{-# INLINE curryD #-}
#endif


-- instance ClosedCat (D s) where
--   apply = applyD
-- --   curry = curryD

-- applyD :: forall s a b. Ok2 (D s) a b => D s ((a -> b) :* a) b
-- applyD = D (\ (f,a) -> let (b,f') = andDeriv f a in
--               (b, _))

-- Differentiable linear function
linearDF :: (a -> b) -> D a b
linearDF f = linearD f f
{-# INLINE linearDF #-}

instance Additive b => ConstCat D b where
  const b = D (const (b, const zero))
  {-# INLINE const #-}

instance TerminalCat D where
  it = const ()
  {-# INLINE it #-}

instance (Num s, Additive s) => NumCat D s where
  negateC = linearDF negateC
  addC    = linearDF addC
  mulC    = D (mulC &&& \ (a,b) (da,db) -> a * db + da * b)
  powIC   = notDef "powC"       -- TODO
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

const' :: (a -> c) -> (a -> b -> c)
const' = (const .)

scalarD :: Num s => (s -> s) -> (s -> s -> s) -> D s s
scalarD f d = D (\ x -> let r = f x in (r, (* d x r)))
{-# INLINE scalarD #-}

-- Use scalarD with const f when only r matters and with const' g when only x
-- matters.

scalarR :: Num s => (s -> s) -> (s -> s) -> D s s
scalarR f f' = scalarD f (\ _ -> f')
-- scalarR f x = scalarD f (const x)
-- scalarR f = scalarD f . const
{-# INLINE scalarR #-}

scalarX :: Num s => (s -> s) -> (s -> s) -> D s s
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

instance (Fractional s, Additive s) => FractionalCat D s where
  recipC = scalarR recip (negate . square)
  {-# INLINE recipC #-}

instance (Floating s, Additive s) => FloatingCat D s where
  expC = scalarR exp id
  sinC = scalarX sin cos
  cosC = scalarX cos (negate . sin)
  {-# INLINE expC #-}
  {-# INLINE sinC #-}
  {-# INLINE cosC #-}

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

-- Type specialization of andDeriv
andDerF :: forall a b . (a -> b) -> (a -> b :* (a -> b))
andDerF = andDeriv
-- andDerF _ = oops "andDerF"
-- {-# NOINLINE andDerF #-}
-- {-# RULES "andDerF" andDerF = andDeriv #-}

-- Type specialization of deriv
derFL :: forall a b . (a -> b) -> (a -> (a -> b))
derFL = deriv
-- derFL = oops "derFL"
-- {-# NOINLINE derFL #-}
-- {-# RULES "derFL" derFL = deriv #-}
-- {-# INLINE derFL #-}

-- AD with derivative-as-function, then converted to linear map
andDerFL :: forall s a b. (OkLM s a, OkLM s b, HasL (V s a), s ~ R)
         => (a -> b) -> (a -> b :* L s a b)
andDerFL _ = oops "andDerFL"
-- andDerFL = (fmap.fmap.fmap) linear andDeriv
-- andDerFL = (second linear .) . andDerF
-- andDerFL f = second linear . andDerF f
{-# NOINLINE andDerFL #-}
-- {-# RULES "andDerFL" andDerFL = andDeriv #-}
{-# RULES "andDerFL" forall f. andDerFL f = second linear . andDerF f #-}

-- When the dust settles, experiment with "error" and with INLINE (separately).

-- The s ~ R is just to make testing a little easier. Remove later.

#if 0

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
-- gradient :: HasV s a => (a -> s) -> a -> a
gradient f = unV . unpack . unpack . der f
{-# INLINE gradient #-}
-- {-# RULES "gradient" forall f. gradient f = unV . unpack . unpack . der f #-}

--                             f :: a -> R
--                         der f :: a -> L R a R
--                unpack . der f :: a -> V R R (V R a R)
--                               :: a -> Par1 (V R a R)
--       unpack . unpack . der f :: a -> V R a R
-- unV . unpack . unpack . der f :: a -> a

#endif
