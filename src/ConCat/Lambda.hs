{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Lambda calculus interface to CCC construction

module ConCat.Lambda where

import Prelude hiding (id,(.),curry,uncurry)
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)
import Data.Type.Equality ((:~:)(..),TestEquality(..))
import Data.Typeable (Typeable,typeRep,eqT)
import Data.Proxy (Proxy(..))

import ConCat.Category

-- | Variable names
type Name = String

-- | Typed variable.
data V a = Typeable a => V Name

instance Show (V a) where
  -- show (V str) = str
  showsPrec p (V str) =
    showParen (p > 0) $
    showString str . showString " :: " . showsPrec 0 (typeRep (Proxy :: Proxy a))

instance TestEquality V where
  (V n :: V a) `testEquality` (V m :: V b)
    | Just Refl <- eqT @a @b, n == m = Just Refl
    | otherwise                      = Nothing

infixr 1 :$
infixr 8 :@

-- | Binding patterns
data Pat :: (u -> u -> *) -> u -> * where
  UnitPat :: Pat k (Unit k)
  VarPat  :: Ok k a => V a -> Pat k a
  (:$)    :: Oks k [a,b] => Pat k a -> Pat k b -> Pat k (Prod k a b)
  (:@)    :: Ok k a => Pat k a -> Pat k a -> Pat k  a

#if 0

type L k p b = Pat k p -> (p `k` b)

lit :: (ConstCat k b, Ok k p) => b -> L k p b
lit b = const (constArrow b)

prim1 :: (ClosedCat k, Oks k [p,a,b]) => (a `k` b) -> L k p (Exp k a b)
prim1 f = const (constFun f)

prim2 :: (ClosedCat k, Oks k [p,a,b,c])
      => (Prod k a b `k` c) -> L k p (Exp k a (Exp k b c))
prim2 f = const (constFun2 f)

var :: forall k p b. (ProductCat k, Oks k [p,b]) => V b -> L k p b
var u = fromMaybe (error $ "unbound variable: " ++ show u) . conv
 where
   conv :: forall c. Ok k c => Pat k c -> Maybe (c `k` b)
   conv (VarPat v) | Just Refl <- v `testEquality` u = Just id
                   | otherwise                       = Nothing
   conv UnitPat  = Nothing
   conv (p :$ q) = ((. exr) <$> conv q) `mplus` ((. exl) <$> conv p)
   conv (p :@ q) = conv q `mplus` conv p

app :: forall k p a b. (ClosedCat k, Oks k [p,a,b])
    => L k p (Exp k a b) -> L k p a -> L k p b
app a b p = apply . (a p &&& b p)
            <+ okProd @k @(Exp k a b) @a
            <+ okExp  @k @a @b

lam :: forall k p a b. (ClosedCat k, Oks k [p,a,b])
    => Pat k a -> L k (Prod k p a) b -> L k p (Exp k a b)
lam a b p = curry (b (p :$ a))

#else

-- Hide the binding context behind a quantifier

data L k b = L (forall p. Ok k p => Pat k p -> (p `k` b))

lit :: ConstCat k b => b -> L k b
lit b = L (const (constArrow b))

prim1 :: (ClosedCat k, Oks k [a,b]) => (a `k` b) -> L k (Exp k a b)
prim1 f = L (const (constFun f))

prim2 :: (ClosedCat k, Oks k [a,b,c])
      => (Prod k a b `k` c) -> L k (Exp k a (Exp k b c))
prim2 f = L (const (constFun2 f))

var :: forall k b. (ProductCat k, Ok k b) => V b -> L k b
var u = L (fromMaybe (error $ "convert: unbound variable: " ++ show u) . conv)
 where
   conv :: forall c. Ok k c => Pat k c -> Maybe (c `k` b)
   conv (VarPat v) | Just Refl <- v `testEquality` u = Just id
                   | otherwise                       = Nothing
   conv UnitPat  = Nothing
   conv (p :$ q) = ((. exr) <$> conv q) `mplus` ((. exl) <$> conv p)
   conv (p :@ q) = conv q `mplus` conv p

-- Perhaps convertVar would be more efficient if it picked apart the Pat only
-- once rather than once per variable lookup.

app :: forall k a b. (ClosedCat k, Ok k a, Ok k b)
    => L k (Exp k a b) -> L k a -> L k b
app (L a) (L b) = L (\ p -> apply . (a p &&& b p))
                  <+ okProd @k @(Exp k a b) @a
                  <+ okExp  @k @a @b

lam :: forall k a b. (ClosedCat k, Oks k [a,b])
    => Pat k a -> L k b -> L k (Exp k a b)
lam a (L b) = L (\ (p :: Pat k p) -> curry (b (p :$ a)) <+ okProd @k @p @a)

#endif
