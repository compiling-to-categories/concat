{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | 

module ConCat.E where

import Prelude hiding (id,(.))

import ConCat.Misc
import ConCat.Category

-- | Variable names
type Name = String

-- | Typed variable. Phantom
data V a = V Name

infixr 1 :$
infixr 8 :@

-- | Binding patterns
data Pat :: * -> * where
  UnitPat :: Pat ()
  VarPat  :: V a -> Pat a
  (:$)    :: Pat a -> Pat b -> Pat (a :* b)
  (:@)    :: Pat a -> Pat a -> Pat a

infixl 9 :^
-- | Lambda expressions
data E :: (* -> * -> *) -> (* -> *) -> (* -> *) where
  Var     :: Ok k a => V a -> E k p a
  ConstE  :: Ok k a => p a -> E k p a
  (:^)    :: Oks k [a,b] => E k p (Exp k a b) -> E k p a -> E k p b
  Lam     :: Oks k [a,b] => Pat a -> E k p b -> E k p (Exp k a b)


-- CCC k version of lambda expression of type b in context of type p

#if 0

type L k p b = Pat p -> (p `k` b)

app :: forall k p a b. (ClosedCat k, Oks k [p,a,b])
    => L k p (Exp k a b) -> L k p a -> L k p b
app u v p = apply . (u p &&& v p)
  <+ okProd @k @(Exp k a b) @a
  <+ okExp  @k @(Ok k) @a @b

-- convert (u :^ v)     p = apply . (convert u p &&& convert v p)

#else

data L k b = L (forall p. Ok k p => Pat p -> (p `k` b))

app :: forall k a b. (ClosedCat k, Ok k a, Ok k b)
    => L k (Exp k a b) -> L k a -> L k b
app (L u) (L v) = L (\ p -> apply . (u p &&& v p))
  <+ okProd @k @(Exp k a b) @a
  <+ okExp  @k @a @b

#endif
