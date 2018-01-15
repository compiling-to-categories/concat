{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}

#include "ConCat/AbsTy.inc"
AbsTyPragmas

-- | Additive maps

module ConCat.AdditiveFun
  ( Additive1(..), type (-+>)(..), addFun, addFun'
  , module ConCat.Additive
  
  ) where

import Prelude hiding (id,(.),const,curry,uncurry,zipWith)

import Data.Monoid
import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:.:)(..))
import GHC.TypeLits (KnownNat)

import Data.Constraint (Dict(..),(:-)(..))
import Data.Key (Zip)
import Data.Pointed (Pointed)
import Data.Vector.Sized (Vector)

import ConCat.Orphans ()
import ConCat.AltCat
import ConCat.Rep
import ConCat.Additive
-- -- The following imports allows the instances to type-check. Why?
-- import qualified ConCat.Category  as C

AbsTyImports

infixr 1 -+>
-- | Additive homomorphisms
newtype a -+> b = AddFun (a -> b)

instance HasRep (a -+> b) where
  type Rep (a -+> b) = a -> b
  abst f = AddFun f
  repr (AddFun f) = f

AbsTy(a -+> b)


#define OPINLINE INLINE

-- -- Prevents some subtle non-termination errors. See 2017-12-27 journal notes.
-- #define OPINLINE INLINE [0]

-- -- Changed to NOINLINE [0]. See 2017-12-29 journal notes.
-- #define OPINLINE NOINLINE [0]
-- -- I copied this definition from ConCat.Category. TODO: centralize.

instance Category (-+>) where
  type Ok (-+>) = Additive -- &+& Eq  -- the Eq is for CoproductPCat
  id = abst id
  (.) = inAbst2 (.)
  {-# OPINLINE id #-}
  {-# OPINLINE (.) #-}

instance ProductCat (-+>) where
  exl    = abst exl
  exr    = abst exr
  (&&&)  = inAbst2 (&&&)
  (***)  = inAbst2 (***)
  dup    = abst dup
  swapP  = abst swapP
  first  = inAbst first
  second = inAbst second
  {-# OPINLINE exl #-}
  {-# OPINLINE exr #-}
  {-# OPINLINE (&&&) #-}
  {-# OPINLINE (***) #-}
  {-# OPINLINE dup #-}
  {-# OPINLINE swapP #-}
  {-# OPINLINE first #-}
  {-# OPINLINE second #-}

instance CoproductPCat (-+>) where
  inlP   = abst (,zero)
  inrP   = abst (zero,)
  (||||) = inAbst2 (\ f g (x,y) -> f x ^+^ g y)
  (++++) = inAbst2 (***)
  jamP   = abst (uncurry (^+^))
  swapPS = abst swapP
  -- ...
  {-# OPINLINE inlP #-}
  {-# OPINLINE inrP #-}
  {-# OPINLINE (||||) #-}
  {-# OPINLINE (++++) #-}
  {-# OPINLINE jamP #-}
  {-# OPINLINE swapPS #-}

instance Num s => ScalarCat (-+>) s where
  scale s = abst (s *)
  {-# OPINLINE scale #-}

-- TODO: generalize from (*). Semimodule?

instance Ok (-+>) b => ConstCat (-+>) b where
  const b = abst (const b)
  {-# OPINLINE const #-}

instance TerminalCat (-+>) where
  it = abst zero
  {-# OPINLINE it #-}

instance CoterminalCat (-+>) where
  ti = abst zero
  {-# OPINLINE ti #-}

-- Note that zero for functions is point zero, i.e., const zero.

{--------------------------------------------------------------------
    Indexed products and coproducts
--------------------------------------------------------------------}

instance OkIxProd (-+>) n where okIxProd = Entail (Sub Dict)

instance IxProductCat (-+>) n where
  exF    = abst . exF
  forkF  = abst . forkF  . fmap repr
  crossF = abst . crossF . fmap repr
  replF  = abst replF
  {-# OPINLINE exF    #-}
  {-# OPINLINE forkF  #-}
  {-# OPINLINE crossF #-}
  {-# OPINLINE replF  #-}

#if 0
-- | Indexed coproducts as indexed products
class (Category k, OkIxProd k n) => IxCoproductPCat k n where
  inPF   :: forall a   . Ok  k a   => (a `k` (a :^ n)) :^ n
  joinPF :: forall a b . Ok2 k a b => (b `k` a) :^ n -> ((b :^ n) `k` a)
  plusPF :: forall a b . Ok2 k a b => (b `k` a) :^ n -> ((b :^ n) `k` (a :^ n))  -- same as crossPF
  jamPF  :: forall a   . Ok  k a   => (a :^ n) `k` a
#endif

instance (IxSummable n) => IxCoproductPCat (-+>) n where
  inPF   = abst . inPF
  joinPF = abst . joinPF . fmap repr
  plusPF = abst . plusPF . fmap repr
  jamPF  = abst jamPF
  {-# OPINLINE inPF   #-}
  {-# OPINLINE joinPF #-}
  {-# OPINLINE plusPF #-}
  {-# OPINLINE jamPF  #-}

{--------------------------------------------------------------------
    Functor additivity
--------------------------------------------------------------------}

class Additive1 h where additive1 :: Sat Additive a |- Sat Additive (h a)

instance Additive1 ((->) a) where additive1 = Entail (Sub Dict)
instance Additive1 Sum      where additive1 = Entail (Sub Dict)
instance Additive1 Product  where additive1 = Entail (Sub Dict)
instance Additive1 U1       where additive1 = Entail (Sub Dict)
instance Additive1 Par1     where additive1 = Entail (Sub Dict)
instance (AddF f, AddF g) => Additive1 (f :*: g)  where additive1 = Entail (Sub Dict)
instance (AddF f, AddF g) => Additive1 (g :.: f)  where additive1 = Entail (Sub Dict)
instance KnownNat n       => Additive1 (Vector n) where additive1 = Entail (Sub Dict)

-- instance OkAdd (-+>) where
--   okAdd = Entail (Sub Dict)

{--------------------------------------------------------------------
    NumCat etc
--------------------------------------------------------------------}

instance (Num s, Additive s) => NumCat (-+>) s where
  addC    = abst addC
  negateC = abst negateC
  mulC    = abst mulC
  powIC   = abst powIC
  {-# OPINLINE negateC #-}
  {-# OPINLINE addC    #-}
  {-# OPINLINE mulC    #-}
  {-# OPINLINE powIC   #-}

-- TODO: more

{--------------------------------------------------------------------
    Functor-level operations
--------------------------------------------------------------------}

instance Additive1 h => OkFunctor (-+>) h where
  okFunctor :: forall a. Sat Additive a |- Sat Additive (h a)
  okFunctor = additive1
  {-# OPINLINE okFunctor #-}

instance (Functor h, Additive1 h) => FunctorCat (-+>) h where
  fmapC = inAbst fmapC
  unzipC = abst unzipC
  {-# OPINLINE fmapC #-}
  {-# OPINLINE unzipC #-}

instance (Zip h, Additive1 h) => ZipCat (-+>) h where
  zipC = abst zipC
  {-# OPINLINE zipC #-}

instance (Zip h, OkFunctor (-+>) h) => ZapCat (-+>) h where
  zapC fs = abst (zapC (repr <$> fs))
  {-# OPINLINE zapC #-}

--                      fs   :: h (a -+> b)
--             repr <$> fs   :: h (a -> b)
--       zapC (repr <$> fs)  :: h a -> h b
-- abst (zapC (repr <$> fs)) :: (-+>) (h a) (h b)

-- class ({- Pointed h, -} OkFunctor k h, Ok k a) => PointedCat k h a where
--   pointC :: a `k` h a

instance (Pointed h, Additive1 h, Additive a) => PointedCat (-+>) h a where
  pointC = abst pointC
  {-# OPINLINE pointC #-}

instance (Foldable h, Additive a) => AddCat (-+>) h a where
  sumAC = abst sumA
  {-# OPINLINE sumAC #-}

{--------------------------------------------------------------------
    CCC interface
--------------------------------------------------------------------}

addFun :: (a -> b) -> (a -> b)
addFun f = repr (toCcc @(-+>) f)
{-# INLINE addFun #-}

-- addFun = repr . toCcc @(-+>)

addFun' :: (a -> b) -> (a -> b)
addFun' f = repr (toCcc' @(-+>) f)
{-# INLINE addFun' #-}
