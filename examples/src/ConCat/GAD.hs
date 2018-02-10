{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

#include "ConCat/AbsTy.inc"

-- | Generalized automatic differentiation

module ConCat.GAD where

import Prelude hiding (id,(.),curry,uncurry,const,zip,unzip,zipWith)
import qualified Prelude as P
-- import GHC.Exts (Coercible,coerce)
import GHC.Exts (Constraint)

import Data.Constraint (Dict(..),(:-)(..))

-- import GHC.Generics (Par1(..),(:.:)(..),(:*:)())
-- import Control.Newtype
-- import Data.Key (Zip(..))

import Data.Pointed
import Data.Key
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable)
import qualified Data.Functor.Rep as R

import ConCat.Misc ((:*),type (&+&),cond,result,unzip,sqr,bottom)
import ConCat.Additive
import ConCat.AltCat
import ConCat.Rep

AbsTyImports

-- TODO: try again with importing Category qualified and AltCat unqualified.

-- newtype GD k a b = D { unD :: a -> b :* (a `k` b) }
data GD k a b = D { unD :: a -> (b :* (a `k` b)) }

mkD :: HasRep (a `k` b) => (a -> b :* Rep (a `k` b)) -> GD k a b
mkD = D P.. (result P.. second) abst
{-# INLINE mkD #-}

unMkD :: HasRep (a `k` b) => GD k a b -> (a -> b :* Rep (a `k` b))
unMkD = (result P.. second) repr P.. unD
{-# INLINE unMkD #-}

-- Differentiable linear function, given the function and its constant derivative
linearD :: (a -> b) -> (a `k` b) -> GD k a b
-- linearD f f' = D (f &&& const f')
linearD f f' = D (\ a -> (f a, f'))
{-# INLINE linearD #-}

-- -- Differentiable linear function
-- linear :: (a -> b) -> GD k a b
-- linear f = linearD f (toCcc' f)
-- {-# INLINE linear #-}

-- Use of linear leads to an plugin error. TODO: track down. linear also has the
-- unfortunate effect of hiding the requirements on k, resulting in run-time
-- errors instead of compile-time errors.

-- instance Newtype (D s a b) where
--   type O (D s a b) = (a -> b :* L s a b)
--   pack f = D f
--   unpack (D f) = f

instance HasRep (GD k a b) where
  type Rep (GD k a b) = (a -> b :* (a `k` b))
  abst f = D f
  repr (D f) = f

AbsTy(GD k a b)

-- Common pattern for linear functions
#define Linear(nm) nm = linearD nm nm ; {-# INLINE nm #-}

instance (TerminalCat k, CoterminalCat k, ConstCat k b, Additive b)
      => ConstCat (GD k) b where
  const b = linearD (const b) (const zero)
  {-# INLINE const #-}

-- What if we went further, and defined nonlinear arrows like mulC as if linear?
-- Probably wouldn't work, since the linear approximations depend on input. On
-- the other hand, maybe approximations of function shiftings at zero.

instance Category k => Category (GD k) where
  type Ok (GD k) = Ok k
  Linear(id)
  -- D g . D f = D (\ a ->
  --   let (b,f') = f a
  --       (c,g') = g b
  --   in
  --     (c, g' . f'))
  D g . D f = D (\ a -> let { (b,f') = f a ; (c,g') = g b } in (c, g' . f'))

  {-# INLINE (.) #-}

instance ProductCat k => ProductCat (GD k) where
  Linear(exl)
  Linear(exr)
  Linear(dup)
  -- D f *** D g = D (second (uncurry (***)) . transposeP . (f *** g))
  -- D f *** D g = D (\ (a,b) ->
  --   let (c,f') = f a
  --       (d,g') = g b
  --   in
  --     ((c,d), f' *** g'))
  D f *** D g =
    D (\ (a,b) -> let { (c,f') = f a ; (d,g') = g b } in ((c,d), f' *** g'))
  {-# INLINE (***) #-}

  -- D f &&& D g = D (\ a ->
  --   let (c,f') = f a
  --       (d,g') = g a
  --   in
  --     ((c,d), f' &&& g')) -- or default
  -- {-# INLINE (&&&) #-}

instance OkAdd k => OkAdd (GD k) where
  okAdd :: forall a. Ok' (GD k) a |- Sat Additive a
  okAdd = Entail (Sub (Dict <+ okAdd @k @a))

instance CoproductPCat k => CoproductPCat (GD k) where
  Linear(inlP)
  Linear(inrP)
  -- D f ++++ D g = D (second (uncurry (++++)) . transposeP . (f ++++ g))
  -- D f ++++ D g = D (\ (a,b) ->
  --   let (c,f') = f a
  --       (d,g') = g b
  --   in
  --     ((c,d), f' ++++ g'))
  D f ++++ D g =
    D (\ (a,b) -> let { (c,f') = f a ; (d,g') = g b } in ((c,d), f' ++++ g'))
  Linear(jamP)
  Linear(swapPS)
  {-# INLINE (++++) #-}
  -- D f |||| D g = D (\ (a,b) ->
  --   let (c ,f') = f a
  --       (c',g') = g b
  --   in
  --     (c ^+^ c', f' |||| g')) -- or default
  -- {-# INLINE (||||) #-}

{--------------------------------------------------------------------
    Indexed products and coproducts
--------------------------------------------------------------------}

#if 0
class (Category k, OkIxProd k h) => IxProductCat k h where
  exF    :: forall a  . Ok  k a   => h (h a `k` a)
  forkF  :: forall a b. Ok2 k a b => h (a `k` b) -> (a `k` h b)
  crossF :: forall a b. Ok2 k a b => h (a `k` b) -> (h a `k` h b)
  replF  :: forall a  . Ok  k a   => a `k` h a

class (Category k, OkIxProd k h) => IxCoproductPCat k h where
  inPF   :: forall a   . (Additive a, Ok  k a  ) => h (a `k` h a)
  joinPF :: forall a b . (Additive a, Ok2 k a b) => h (b `k` a) -> (h b `k` a)
  plusPF :: forall a b . (Additive a, Ok2 k a b) => h (b `k` a) -> (h b `k` h a)  -- same as crossPF
  jamPF  :: forall a   . (Additive a, Ok  k a  ) => h a `k` a

class OkIxProd k h where
  okIxProd :: Ok' k a |- Ok' k h a
#endif

instance OkIxProd k h => OkIxProd (GD k) h where
  okIxProd :: forall a. Ok' (GD k) a |- Ok' (GD k) (h a)
  okIxProd = Entail (Sub (Dict <+ okIxProd @k @h @a))

#define Linears(nm) nm = zipWith linearD nm nm

instance (IxProductCat (->) h, IxProductCat k h, Zip h) => IxProductCat (GD k) h where
  Linears(exF)
  Linear(replF)
  crossF (fmap repr -> fs) = D (second crossF . unzip . crossF fs)
  {-# INLINE crossF #-}

-- crossF types:
-- 
--   crossF fs     :: h a -> h (b :* (a `k` b))
--   unzip         :: .. -> h b :* h (a `k` b)
--   second crossF :: .. -> h b :* (h a `k` h b

instance (IxCoproductPCat (->) h, IxCoproductPCat k h, Zip h) => IxCoproductPCat (GD k) h where
  Linears(inPF)
  Linear(jamPF)
  plusPF (fmap repr -> fs) = D (second plusPF . unzip . plusPF fs)
  {-# INLINE plusPF #-}

{--------------------------------------------------------------------
    NumCat etc
--------------------------------------------------------------------}

instance {-# overlappable #-} (LinearCat k s, Additive s, Num s) => NumCat (GD k) s where
  addC    = linearD addC jamP
  negateC = linearD negateC (scale (-1))
  mulC    = D (mulC &&& \ (u,v) -> scale v |||| scale u) -- \ (du,dv) -> u*dv + v*du
  powIC   = notDef "powIC"       -- TODO
  {-# INLINE negateC #-}
  {-# INLINE addC    #-}
  {-# INLINE mulC    #-}
  {-# INLINE powIC   #-}

scalarD :: ScalarCat k s => (s -> s) -> (s -> s -> s) -> GD k s s
scalarD f d = D (\ x -> let r = f x in (r, scale (d x r)))
{-# INLINE scalarD #-}

-- Specializations

scalarR :: ScalarCat k s => (s -> s) -> (s -> s) -> GD k s s
scalarR f x = scalarD f (const x)
{-# INLINE scalarR #-}

scalarX :: ScalarCat k s => (s -> s) -> (s -> s) -> GD k s s
scalarX f r = scalarD f (const . r)
{-# INLINE scalarX #-}

instance (LinearCat k s, Additive s, Fractional s) => FractionalCat (GD k) s where
  recipC = scalarR recip (negate . sqr)
  {-# INLINE recipC #-}

instance (ScalarCat k s, Ok k s, Floating s) => FloatingCat (GD k) s where
  expC = scalarR exp id
  logC = scalarX log recip
  sinC = scalarX sin cos
  cosC = scalarX cos (negate . sin)
  {-# INLINE expC #-}
  {-# INLINE sinC #-}
  {-# INLINE cosC #-}
  {-# INLINE logC #-}

-- TODO: experiment with moving some of these dual derivatives to DualAdditive,
-- in the style of addD, mulD, etc.

instance (ProductCat k, Ord a) => MinMaxCat (GD k) a where
  minC = D (minC &&& cond exl exr . lessThanOrEqual)
  maxC = D (maxC &&& cond exr exl . lessThanOrEqual)
  {-# INLINE minC #-} 
  {-# INLINE maxC #-} 

-- Equivalently,
-- 
-- minC = D (\ (x,y) -> (minC (x,y), if x <= y then exl else exr))
-- maxC = D (\ (x,y) -> (maxC (x,y), if x <= y then exr else exl))

-- Functor-level operations:

-- TODO: IfCat. Maybe make ifC :: (a :* a) `k` (Bool -> a), which is linear.

{--------------------------------------------------------------------
    Discrete
--------------------------------------------------------------------}

-- Experiment

-- Differentiable discrete function, yielding 'bottom' derivative
discreteD :: (a -> b) -> GD k a b
discreteD f = D (\ a -> (f a, bottom))
{-# INLINE discreteD #-}

#define Discrete(nm) nm = discreteD nm ; {-# INLINE nm #-}

instance (ProductCat k, Ok k Bool) => BoolCat (GD k) where
  Discrete(notC)
  Discrete(andC)
  Discrete(orC)
  Discrete(xorC)

instance IfCat k a => IfCat (GD k) a where
  Linear(ifC)

{--------------------------------------------------------------------
    Functor-level operations
--------------------------------------------------------------------}

instance (IxProductCat k h, FunctorCat k h) => FunctorCat (GD k) h where
  fmapC = inAbst (\ q -> second crossF . unzipC . fmapC q)
  Linear(unzipC)
  {-# INLINE fmapC #-}

-- See 2017-12-27 notes
-- 
--      q :: a -> b :* (a `k` b)
-- fmap q :: h a -> h (b :* (a `k` b))
-- unzip  :: h (b :* (a `k` b)) -> h b :* h (a `k` b)
-- crossF :: h (a `k` b) -> (h a `k` h b)

instance OkFunctor k h => OkFunctor (GD k) h where
  okFunctor :: forall a. Ok' (GD k) a |- Ok' (GD k) (h a)
  okFunctor = Entail (Sub (Dict <+ okFunctor @k @h @a))
  -- okFunctor = Entail (Sub Dict)
  -- okFunctor = inForkCon (yes1 *** okFunctor @k @h @a)
  {-# INLINE okFunctor #-}

-- TODO: FunctorCat. See RAD

instance (AddCat (->) h a, AddCat k h a, OkFunctor (GD k) h)
      => AddCat (GD k) h a where
  Linear(sumAC)

instance (ZipCat k h, OkFunctor (GD k) h) => ZipCat (GD k) h where
  Linear(zipC)
  -- zipWithC = ??
  -- {-# INLINE zipWithC #-}

instance (ZapCat k h, OkFunctor k h, Zip h) => ZapCat (GD k) h where
  zapC = abst . result (second zapC . unzip) . zapC . fmap repr

-- fmap repr            :: h (GD k a b) -> h (a -> b :* k a b)
-- zapC                 :: h (a -> b :* k a b) -> (h a -> h (b :* k a b))
-- result unzip         :: (h a -> h (b :* k a b)) -> (h a -> h b :* h (k a b))
-- (result.second) zapC :: (h a -> h b :* h (k a b)) -> (h a -> h b :* k h a h b)
-- abst                 :: (h a -> h b :* k h a h b) -> GD k h a h b

-- TODO: What use can we make of the ZapCat instance? Maybe repeated differentiation.

instance (OkFunctor (GD k) h, Pointed h, PointedCat k h a) => PointedCat (GD k) h a where
  Linear(pointC)

-- instance (IxProductCat k h, FunctorCat k h, Strong k h)
--       => Strong (GD k) h where
--   Linear(strength)

instance (DistributiveCat (->) g f, DistributiveCat k g f)
      => DistributiveCat (GD k) g f where
  Linear(distributeC)

instance (RepresentableCat (->) g, RepresentableCat k g)
      => RepresentableCat (GD k) g where
  Linear(indexC)
  Linear(tabulateC)

{--------------------------------------------------------------------
    Other instances
--------------------------------------------------------------------}

notDef :: String -> a
notDef meth = error (meth ++ " on D not defined")

instance (RepCat (->) a r, RepCat k a r) => RepCat (GD k) a r where
  Linear(reprC)
  Linear(abstC)

#if 0
instance (Coercible a b, V s a ~ V s b, Ok2 k a b) => CoerceCat (GD k) a b where
  Linear(coerceC)
#else
instance ( CoerceCat (->) a b
         , CoerceCat k a b
         ) => CoerceCat (GD k) a b where
  Linear(coerceC)
#endif

{--------------------------------------------------------------------
    Differentiation interface
--------------------------------------------------------------------}

-- | A function combined with its derivative
andDeriv :: forall k a b . (a -> b) -> (a -> b :* (a `k` b))
andDeriv h = unD (toCcc h)
{-# INLINE andDeriv #-}

-- | The derivative of a given function
deriv :: forall k a b . (a -> b) -> (a -> (a `k` b))
deriv h = snd P.. andDeriv h
{-# INLINE deriv #-}
