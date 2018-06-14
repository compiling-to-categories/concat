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
import Data.Functor.Rep (Representable(tabulate))

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
{-# INLINE unAddFun #-}

-- deriving instance Additive b => Additive (a -+> b)

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

#define Abst(nm) nm = abst nm ; {-# INLINE nm #-}

instance Additive b => Additive (a -+> b) where
  Abst(zero)
  (^+^) = inAbst2 (^+^)
  {-# OPINLINE (^+^) #-}

instance Category (-+>) where
  type Ok (-+>) = Additive -- &+& Eq  -- the Eq is for CoproductPCat
  Abst(id)
  (.) = inAbst2 (.)
  {-# OPINLINE (.) #-}

instance MonoidalPCat (-+>) where
  (***) = inAbst2 (***)
  first  = inAbst first
  second = inAbst second
  {-# OPINLINE (***) #-}
  {-# OPINLINE first #-}
  {-# OPINLINE second #-}

instance BraidedPCat (-+>) where
  Abst(swapP)

instance ProductCat (-+>) where
  Abst(exl)
  Abst(exr)
  (&&&)  = inAbst2 (&&&)
  Abst(dup)
  {-# OPINLINE (&&&) #-}

instance CoproductPCat (-+>) where
#if 1
  inlP = abst (,zero)
  inrP = abst (zero,)
  jamP = abst (uncurry (^+^))
  -- swapPS = swapP
  {-# INLINE inlP #-}
  {-# INLINE inrP #-}
  {-# INLINE jamP #-}
  -- {-# INLINE swapPS #-}
#else
  Abst(inlP)
  Abst(inrP)
  Abst(jamP)
  -- Abst(swapPS)
  -- (||||) = inAbst2 (\ f g (x,y) -> f x ^+^ g y)
  -- (++++) = inAbst2 (***)
  -- jamP   = abst (uncurry (^+^))  -- 2018-02-04 notes
  -- jamP   = abst jamP  -- 2018-02-07 notes
  -- ...
  -- {-# OPINLINE (||||) #-}
  -- {-# OPINLINE (++++) #-}
  -- {-# OPINLINE jamP #-}
#endif

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
  Abst(coerceC)

instance RepCat (->) a r => RepCat (-+>) a r where
  Abst(reprC)
  Abst(abstC)

{--------------------------------------------------------------------
    Indexed products and coproducts
--------------------------------------------------------------------}

instance Additive1 h => OkIxProd (-+>) h where
  okIxProd :: forall a. Ok' (-+>) a |- Ok' (-+>) (h a)
  okIxProd = Entail (Sub (Dict <+ additive1 @h @a))
  {-# OPINLINE okIxProd #-}

instance ({- Representable h, Pointed h, -} Zip h, Additive1 h) => IxMonoidalPCat (-+>) h where
  crossF = inAbstF1 crossF
  {-# OPINLINE crossF #-}

instance (Representable h, Zip h, Pointed h, Additive1 h) => IxProductCat (-+>) h where
  exF    = abst <$> exF
  forkF  = inAbstF1 forkF
  Abst(replF)
  {-# OPINLINE exF    #-}
  {-# OPINLINE forkF  #-}

inFF :: (Additive a, Summable h) => h (a -> h a)
inFF = tabulate (\ i a -> tabulate (\ j -> if i == j then a else zero))

instance (Summable h, Additive1 h) => IxCoproductPCat (-+>) h where
#if 1
  inPF   = abst <$> inFF
  -- joinPF = inAbstF1 joinPF
  -- plusPF = inAbstF1 plusPF
  -- Abst(jamPF)
  jamPF = abst sumA
  -- {-# OPINLINE jamPF   #-}
#else
  inPF   = abst <$> inPF
  -- joinPF = inAbstF1 joinPF
  -- plusPF = inAbstF1 plusPF
  Abst(jamPF)
#endif
  {-# OPINLINE inPF   #-}
  -- {-# OPINLINE joinPF #-}
  -- {-# OPINLINE plusPF #-}

instance OkAdd (-+>) where okAdd = Entail (Sub Dict)

#if 0

{--------------------------------------------------------------------
    NumCat etc
--------------------------------------------------------------------}

instance (Num s, Additive s) => NumCat (-+>) s where
  Abst(addC)
  Abst(negateC)
  Abst(mulC)
  Abst(powIC)

-- I don't think I need NumCat etc.

instance BoolCat (-+>) where
  Abst(notC)
  Abst(andC)
  Abst(orC)
  Abst(xorC)

instance Additive a => IfCat (-+>) a where
  Abst(ifC)

#endif

{--------------------------------------------------------------------
    Functor-level operations
--------------------------------------------------------------------}

-- instance (Functor h, Additive1 h) => Strong (-+>) h where
--   strength = abst strength

instance Additive1 h => OkFunctor (-+>) h where
  okFunctor :: forall a. Sat Additive a |- Sat Additive (h a)
  okFunctor = additive1
  {-# OPINLINE okFunctor #-}

instance (Functor h, Additive1 h) => FunctorCat (-+>) h where
  fmapC = inAbst fmapC
  Abst(unzipC)
  {-# OPINLINE fmapC #-}

instance (Zip h, Additive1 h) => ZipCat (-+>) h where
  Abst(zipC)

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
  Abst(pointC)

instance (Summable h, Additive a) => AddCat (-+>) h a where
  Abst(sumAC)

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
