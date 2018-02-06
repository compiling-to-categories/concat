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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall #-}

#include "ConCat/AbsTy.inc"
AbsTyPragmas

-- | Additive maps

module ConCat.AdditiveFun
  ( Additive1(..), type (-+>)(..), addFun, addFun', unAddFun
  , module ConCat.Additive
  
  ) where

import Prelude hiding (id,(.),const,curry,uncurry,zipWith)

import Data.Constraint (Dict(..),(:-)(..))
import Data.Key (Zip)
import Data.Pointed (Pointed)
import Data.Functor.Rep (Representable)

import ConCat.Orphans ()
import ConCat.AltCat
import ConCat.Rep
import ConCat.Additive

AbsTyImports

infixr 1 -+>
-- | Additive homomorphisms
data a -+> b = AddFun (a -> b)

-- newtype

unAddFun :: (a -+> b) -> (a -> b)
unAddFun (AddFun f) = f

-- deriving instance Additive b => Additive (a -+> b)

instance HasRep (a -+> b) where
  type Rep (a -+> b) = a -> b
  abst f = AddFun f
  repr (AddFun f) = f

AbsTy(a -+> b)

-- QQQ

-- instance Additive (Double -+> Double) where
--   zero = abst zero
--   (^+^) = inAbst2 (^+^)

instance Additive b => Additive (a -+> b) where
  zero = abst zero
  (^+^) = inAbst2 (^+^)

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
  -- jamP   = abst jamP
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

instance CoerceCat (->) a b => CoerceCat (-+>) a b where
  coerceC = abst coerceC

{--------------------------------------------------------------------
    Indexed products and coproducts
--------------------------------------------------------------------}

instance Additive1 h => OkIxProd (-+>) h where
  okIxProd :: forall a. Ok' (-+>) a |- Ok' (-+>) (h a)
  okIxProd = Entail (Sub (Dict <+ additive1 @h @a))

instance (Representable h, Zip h, Pointed h, Additive1 h) => IxProductCat (-+>) h where
  exF    = abst <$> exF
  forkF  = inAbstF1 forkF
  crossF = inAbstF1 crossF
  replF  = abst replF
  {-# OPINLINE exF    #-}
  {-# OPINLINE forkF  #-}
  {-# OPINLINE crossF #-}
  {-# OPINLINE replF  #-}

instance (Summable h, Additive1 h) => IxCoproductPCat (-+>) h where
  inPF   = abst <$> inPF
  joinPF = inAbstF1 joinPF
  plusPF = inAbstF1 plusPF
  jamPF  = abst jamPF
  {-# OPINLINE inPF   #-}
  {-# OPINLINE joinPF #-}
  {-# OPINLINE plusPF #-}
  {-# OPINLINE jamPF  #-}

instance OkAdd (-+>) where okAdd = Entail (Sub Dict)

#if 0

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

-- I don't think I need NumCat etc.

#endif

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

instance (Summable h, Additive a) => AddCat (-+>) h a where
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
