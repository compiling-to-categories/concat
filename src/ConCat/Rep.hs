{-# LANGUAGE TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, EmptyCase, LambdaCase #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-} -- experiment

-- -- Experiment
-- {-# LANGUAGE MagicHash #-}

{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Rep
-- Copyright   :  (c) 2014 Tabula, Inc. and 2016 Conal Elliott
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Convert to and from standard representations
----------------------------------------------------------------------

module ConCat.Rep (HasRep(..)) where

import Data.Monoid
-- import Data.Newtypes.PrettyDouble
import Control.Applicative (WrappedMonad(..))
import qualified GHC.Generics as G

import Data.Functor.Identity (Identity(..))
import Control.Monad.Trans.Reader (ReaderT(..))
import Control.Monad.Trans.Writer (WriterT(..))
import Control.Monad.Trans.State (StateT(..))

-- import Data.Void (Void)
-- TODO: more

import ConCat.Complex

-- -- Experiment
-- import GHC.Exts (Int(..),Int#)

-- TODO: Eliminate most of the following when I drop these types.
import ConCat.Misc ((:*),(:+),Parity(..))

-- import TypeUnary.TyNat (Z,S)
-- import TypeUnary.Nat (Nat(..),IsNat(..))
-- import TypeUnary.Vec (Vec(..))

-- | Convert to and from standard representations. Used for transforming case
-- expression scrutinees and constructor applications. The 'repr' method should
-- convert to a standard representation (unit, products, sums), or closer to
-- such a representation, via another type with a 'HasRep' instance. The 'abst'
-- method should reveal a constructor so that we can perform the
-- case-of-known-constructor transformation.

class HasRep a where
  type Rep a
  repr :: a -> Rep a
  abst :: Rep a -> a

-- -- Identity as @'abst' . 'repr'@.
-- abstRepr :: HasRep a => a -> a
-- abstRepr = abst . repr

#define INLINES {-# INLINE repr #-};{-# INLINE abst #-}

instance HasRep (a,b,c) where
  type Rep (a,b,c) = ((a,b),c)
  repr (a,b,c) = ((a,b),c)
  abst ((a,b),c) = (a,b,c)
  INLINES

instance HasRep (a,b,c,d) where
  type Rep (a,b,c,d) = ((a,b),(c,d))
  repr (a,b,c,d) = ((a,b),(c,d))
  abst ((a,b),(c,d)) = (a,b,c,d)
  INLINES

instance HasRep (a,b,c,d,e) where
  type Rep (a,b,c,d,e) = ((a,b,c,d),e)
  repr (a,b,c,d,e) = ((a,b,c,d),e)
  abst ((a,b,c,d),e) = (a,b,c,d,e)
  INLINES

instance HasRep (a,b,c,d,e,f) where
  type Rep (a,b,c,d,e,f) = ((a,b,c,d),(e,f))
  repr (a,b,c,d,e,f) = ((a,b,c,d),(e,f))
  abst ((a,b,c,d),(e,f)) = (a,b,c,d,e,f)
  INLINES

instance HasRep (a,b,c,d,e,f,g) where
  type Rep (a,b,c,d,e,f,g) = ((a,b,c,d),(e,f,g))
  repr (a,b,c,d,e,f,g) = ((a,b,c,d),(e,f,g))
  abst ((a,b,c,d),(e,f,g)) = (a,b,c,d,e,f,g)
  INLINES

instance HasRep (a,b,c,d,e,f,g,h) where
  type Rep (a,b,c,d,e,f,g,h) = ((a,b,c,d),(e,f,g,h))
  repr (a,b,c,d,e,f,g,h) = ((a,b,c,d),(e,f,g,h))
  abst ((a,b,c,d),(e,f,g,h)) = (a,b,c,d,e,f,g,h)
  INLINES

#if 0
-- Switching to ShapedTypes.Vec
instance HasRep (Vec Z a) where
  type Rep (Vec Z a) = ()
  repr ZVec = ()
  abst () = ZVec
  INLINES

instance HasRep (Vec (S n) a) where
  type Rep (Vec (S n) a) = (a,Vec n a)
  repr (a :< as) = (a, as)
  abst (a, as) = (a :< as)
  INLINES

instance HasRep (Nat Z) where
  type Rep (Nat Z) = ()
  repr Zero = ()
  abst () = Zero
  INLINES

instance IsNat n => HasRep (Nat (S n)) where
  type Rep (Nat (S n)) = () :* Nat n
  repr (Succ n) = ((),n)
  abst ((),n) = Succ n
  INLINES
-- The IsNat constraint comes from Succ.
-- TODO: See about eliminating that constructor constraint.
#endif

#if 1

-- I'm now synthesizing HasRep instances for newtypes.
-- Oh! I still need support for explicit uses.

#define WrapRep(abstT,reprT,con) \
instance HasRep (abstT) where { type Rep (abstT) = reprT; repr (con a) = a ; abst a = con a }

WrapRep(Sum a,a,Sum)
-- WrapRep(PrettyDouble,Double,PrettyDouble)
WrapRep(Product a,a,Product)
WrapRep(All,Bool,All)
WrapRep(Any,Bool,Any)
WrapRep(Dual a,a,Dual)
WrapRep(Endo a,a->a,Endo)
WrapRep(WrappedMonad m a,m a,WrapMonad)
WrapRep(Identity a,a,Identity)
WrapRep(ReaderT e m a, e -> m a, ReaderT)
WrapRep(WriterT w m a, m (a,w), WriterT)
WrapRep(StateT s m a, s -> m (a,s), StateT)

WrapRep(Parity,Bool,Parity)
#endif

-- TODO: Generate these dictionaries on the fly during compilation, so we won't
-- have to list them here.

-- Experimental treatment of Maybe
instance HasRep (Maybe a) where
  type Rep (Maybe a) = Bool :* a
  repr (Just a) = (True,a)
  repr Nothing  = (False,undefined)
  abst (True,a ) = Just a
  abst (False,_) = Nothing 
  INLINES

-- TODO: LambdaCCC.Prim has an BottomP primitive. If the error ever occurs,
-- replace with ErrorP (taking a string argument) and tweak the reification.

-- Generalize Maybe to sums:

-- I use this version for circuits. Restore it later, after I'm handing :+ in reify-rules.

-- instance HasRep (a :+ b) where
--   type Rep (a :+ b) = Bool :* (a :* b)
--   repr (Left  a) = (False,(a,undefined)) -- error "repr on Maybe: undefined value"
--   repr (Right b) = (True,(undefined,b))
--   abst (False,(a,_)) = Left  a
--   abst (True ,(_,b)) = Right b

-- -- TODO: Redefine `Maybe` representation as sum:
-- 
-- type instance Rep (Maybe a) = Unit :+ a
-- ...

instance HasRep (Complex a) where
  type Rep (Complex a) = a :* a
  repr (a :+ a') = (a,a')
  abst (a,a') = (a :+ a')
  INLINES

-- instance HasRep (G.V1 p) where
--   type Rep (G.V1 p) = Void
--   repr = \ case
--   abst = \ case
--   INLINES

instance HasRep (G.U1 p) where
  type Rep (G.U1 p) = ()
  repr G.U1 = ()
  abst () = G.U1
  INLINES

instance HasRep (G.Par1 p) where
  type Rep (G.Par1 p) = p
  repr = G.unPar1
  abst = G.Par1
  INLINES

instance HasRep (G.K1 i c p) where
  type Rep (G.K1 i c p) = c
  repr = G.unK1
  abst = G.K1
  INLINES

instance HasRep (G.M1 i c f p) where
  type Rep (G.M1 i c f p) = f p
  repr = G.unM1
  abst = G.M1
  INLINES

instance HasRep ((f G.:+: g) p) where
  type Rep ((f G.:+: g) p) = f p :+ g p
  repr (G.L1  x) = Left  x
  repr (G.R1  x) = Right x
  abst (Left  x) = G.L1  x
  abst (Right x) = G.R1  x
  INLINES

instance HasRep ((f G.:*: g) p) where
  type Rep ((f G.:*: g) p) = f p :* g p
  repr (x G.:*: y) = (x,y)
  abst (x,y) = (x G.:*: y)
  INLINES

instance HasRep ((G.:.:) f g p) where
  type Rep ((G.:.:) f g p) = f (g p)
  repr = G.unComp1
  abst = G.Comp1
  INLINES

-- TODO: Can I *replace* HasRep with Generic?

{--------------------------------------------------------------------
    Experiments
--------------------------------------------------------------------}

#if 0
-- Represent unboxed types as boxed counterparts.

instance HasRep Int# where
  type Rep Int# = Int
  abst (I# n) = n
  repr n = I# n
  INLINES

--     • Expecting a lifted type, but ‘Int#’ is unlifted
--     • In the first argument of ‘HasRep’, namely ‘Int#’
--       In the instance declaration for ‘HasRep Int#’
#endif
