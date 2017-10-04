{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Automatic differentiation

module ConCat.ADFun where

import Prelude hiding (id,(.),curry,uncurry,const,zip,unzip)
-- import Debug.Trace (trace)

import Control.Newtype (unpack)
import Data.Pointed (Pointed(..))
import Data.Key (Zip(..))
import Data.Constraint hiding ((&&&),(***),(:=>))

import ConCat.Misc ((:*),R,Yes1,oops,unzip,type (&+&))
import ConCat.Free.VectorSpace (HasV(..))
import ConCat.Free.LinearRow
import ConCat.AltCat
import ConCat.AltAggregate
import ConCat.GAD
import ConCat.Additive
-- The following imports allows the instances to type-check. Why?
import qualified ConCat.Category  as C
import qualified ConCat.Aggregate as C

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
  apply = applyD ; {-# INLINE apply #-}
  curry = curryD ; {-# INLINE curry #-}

applyD :: forall a b. Ok2 D a b => D ((a -> b) :* a) b
-- applyD = D (\ (f,a)                   -> (f a, \ (df,da) -> df a ^+^ f da))
applyD = -- trace "calling applyD" $
 D (\ (f,a) -> let (b,f') = andDerF f a in (b, \ (df,da) -> df a ^+^ f' da))
-- applyD = oops "applyD called"   -- does it?

curryD :: forall a b c. Ok3 D a b c => D (a :* b) c -> D a (b -> c)
curryD (D (unfork -> (f,f'))) =
  D (\ a -> (curry f a, \ da -> \ b -> f' (a,b) (da,zero)))

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
scalarD f d = D (\ x   -> let r = f x in (r, (* d x r)))
{-# INLINE scalarD #-}

-- Use scalarD with const f when only r matters and with const' g when only x
-- matters.

scalarR :: Num s => (s        -> s) -> (s -> s) -> D s s
scalarR f f'   = scalarD f (\ _ -> f')
-- scalarR f x = scalarD f (const x)
-- scalarR f   = scalarD f . const
{-# INLINE scalarR #-}

scalarX :: Num s => (s             -> s) -> (s -> s) -> D s s
scalarX f f'    = scalarD f (\ x _    -> f' x)
-- scalarX f f' = scalarD f (\ x y -> const (f' x) y)
-- scalarX f f' = scalarD f (\ x   -> const (f' x))
-- scalarX f f' = scalarD f (const . f')
-- scalarX f f' = scalarD f (const' f')
-- scalarX f    = scalarD f . const'
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

-- type Ok D = (Yes1 &+& Additive)

#if 1
instance OkArr D i where
  okArr :: forall a. Ok' D a |- Ok' D (Arr i a)
  okArr = Entail (Sub Dict)
  -- okArr = inForkCon (yes1 *** additive1 @h @a)

-- class OkArr k h where okArr :: Ok' k a |- Ok' k (h a)

instance LinearCat D i where
  fmapC  = linearDF fmapC
  zipC   = linearDF zipC
  sumC   = linearDF sumC
  pointC = linearDF pointC
  {-# INLINE fmapC #-}
  {-# INLINE zipC #-}
  {-# INLINE sumC #-}
  {-# INLINE pointC #-}

#else
instance Additive1 h => OkFunctor D h where
  okFunctor :: forall a. Ok' D a |- Ok' D (h a)
  okFunctor = inForkCon (yes1 *** additive1 @h @a)

-- class OkFunctor k h where okFunctor :: Ok' k a |- Ok' k (h a)

instance (Zip h, Foldable h, Additive1 h) => LinearCat D h where
  fmapC = linearDF fmapC
  zipC  = linearDF zipC
  sumC  = linearDF sumC
  {-# INLINE fmapC #-}
  {-# INLINE zipC #-}
  {-# INLINE sumC #-}
#endif

-- fmapC' (D h) = D (second (curry zapC) . unzipC . fmapC' h)

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

-- Type specialization of andDeriv
andDerF :: forall a b . (a -> b) -> (a -> b :* (a -> b))
andDerF = andDeriv
{-# INLINE andDerF #-}

-- Type specialization of deriv
derF :: forall a b . (a -> b) -> (a -> (a -> b))
derF = deriv
{-# INLINE derF #-}

-- AD with derivative-as-function, then converted to linear map
andDerFL :: forall s a b. HasLin s a b => (a -> b) -> (a -> b :* L s a b)
andDerFL f = second linear . andDerF f
{-# INLINE andDerFL #-}

-- AD with derivative-as-function, then converted to linear map
derFL :: forall s a b. HasLin s a b => (a -> b) -> (a -> L s a b)
derFL f = linear . derF f
{-# INLINE derFL #-}
