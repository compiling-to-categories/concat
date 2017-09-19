{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Indexed sets of morphisms

module ConCat.Choice where

import Prelude hiding (id,(.),curry,uncurry,const)
import qualified Prelude as P
import GHC.Types (Constraint)

import ConCat.Misc ((:*),oops)
import ConCat.Category
import ConCat.AltCat (reveal)

-- | Like Dict from Data.Constraint, but for parametrized constraints.
-- Injectivity in both con and a helps type inference.
data Dict1 :: (* -> Constraint) -> * -> * where
  Dict1 :: con a => Dict1 con a

-- Alternatively, wrap Dict:
-- 
-- data Dict1 con a = Dict1 (Dict con a)

-- | Generate any value of type @p@ out of thin air.
class ChoiceCat con k where
  chooseC' :: Ok3 k p a b => Dict1 con p -> ((p :* a) `k` b) -> (a `k` b)

-- Needs AllowAmbiguousTypes

-- | Generate any value of type @p@.
chooseC :: forall k con p a b. (ChoiceCat con k, Ok3 k p a b)
        => Dict1 con p -> ((p :* a) `k` b) -> (a `k` b)
chooseC = chooseC'
{-# INLINE [0] chooseC #-}

-- "chooseC'" vs "chooseC", since GHC eagerly inlines all methods to their
-- dictionary selectors, defeating translation across categories. Look for a
-- tidier alternative.

-- Use chooseC for translation and choose for Haskell-friendliness.

-- Placing the category argument k first in chooseC helps the plugin recognize
-- to use reCat.

{-# RULES

"reveal chooseC" forall d f. reveal (chooseC d f) = chooseC' d (reveal f)

 #-}

-- Use type application and a curried function for the Haskell/(->) version.

-- | Generate any value of type @p@.
choose :: forall con p a b. con p
       => (p -> a -> b) -> (a -> b)
choose = chooseC @(->) (Dict1 @con @p) . uncurry
{-# INLINE choose #-}

-- | Nondeterminism category. Like a set of morphisms all of the same type, but
-- represented as a function whose range is that set. The function's domain is
-- existentially hidden.
data Choice :: (* -> Constraint) -> * -> * -> * where
  Choice :: con p => (p -> a -> b) -> Choice con a b

-- Equivalently,
-- 
-- data Choice con a b = forall p. con p => Choice (p -> a -> b)

onChoice :: forall con a b q. (forall p. con p => (p -> a -> b) -> q) -> Choice con a b -> q
onChoice h (Choice f) = h f
{-# INLINE onChoice #-}

-- | Deterministic (trivially nondeterministic) arrow
exactly :: con () => (a -> b) -> Choice con a b
exactly f = Choice (\ () -> f)

type CartCon con = (con (), OpCon (:*) (Sat con))

instance CartCon con => ChoiceCat con (Choice con) where
  chooseC' Dict1 (Choice (f :: p -> q :* a -> b)) =
    Choice @con (uncurry (curry . f))
      <+ inOp @(:*) @(Sat con) @p @q
  {-# INLINE chooseC' #-}

--           Choice f  :: Choice con (q :* a) b
--                  f  :: p -> q :* a -> b
--          curry . f  :: p -> q -> a -> b
-- uncurry (curry . f) :: p :* q -> a -> b

-- Equivalently, \ (p,q) a -> f p (q,a)

instance ChoiceCat con (->) where
  chooseC' = oops "chooseC on (->): Convert to a category that really has an instance."
  -- {-# NOINLINE chooseC' #-}   -- remove later

{--------------------------------------------------------------------
    Category class instances
--------------------------------------------------------------------}

instance CartCon con => Category (Choice con) where
  type Ok (Choice con) = Ok (->) -- Yes1
  id = exactly id
  -- Choice g . Choice f = Choice (\ (p,q) -> g q . f p)
  Choice (g :: q -> b -> c) . Choice (f :: p -> a -> b) =
    Choice (\ (p,q) -> g q . f p)
      <+ inOp @(:*) @(Sat con) @p @q
  {-# INLINE (.) #-}

-- TODO: refactor the needed entailments, which appear also in
-- other instances.

instance CartCon con => ProductCat (Choice con) where
  exl = exactly exl
  exr = exactly exr
  -- Choice f &&& Choice g = Choice (\ (p,q) -> f p &&& g q)
  Choice (f :: p -> a -> c) &&& Choice (g :: q -> a -> d) =
    Choice (\ (p,q) -> f p &&& g q)
      <+ inOp @(:*) @(Sat con) @p @q
  {-# INLINE (&&&) #-}

instance CartCon con => CoproductCat (Choice con) where
  inl = exactly inl
  inr = exactly inr
  -- Choice f ||| Choice g = Choice (\ (p,q) -> f p ||| g q)
  Choice (f :: p -> a -> c) ||| Choice (g :: q -> b -> c) =
    Choice (\ (p,q) -> f p ||| g q)
      <+ inOp @(:*) @(Sat con) @p @q
  {-# INLINE (|||) #-}

instance (CartCon con) => DistribCat (Choice con) where
  distl = exactly distl
  distr = exactly distr

instance (CartCon con) => ClosedCat (Choice con) where
  apply = exactly apply
  curry (Choice f) = Choice (curry . f)
  uncurry (Choice g) = Choice (uncurry . g)

instance (TerminalCat (->), CartCon con)
      => TerminalCat (Choice con) where
  it = exactly it

instance (ConstCat (->) b, CartCon con) => ConstCat (Choice con) b where
  const b = exactly (const b)

instance (BoolCat (->), CartCon con) => BoolCat (Choice con) where
  notC = exactly notC
  andC = exactly andC
  orC  = exactly orC
  xorC = exactly xorC

instance (EqCat (->) a, CartCon con) => EqCat (Choice con) a where
  equal    = exactly equal
  notEqual = exactly notEqual

instance (OrdCat (->) a, CartCon con) => OrdCat (Choice con) a where
  lessThan           = exactly lessThan
  greaterThan        = exactly greaterThan
  lessThanOrEqual    = exactly lessThanOrEqual
  greaterThanOrEqual = exactly greaterThanOrEqual

instance (EnumCat (->) a, CartCon con) => EnumCat (Choice con) a where
  succC = exactly succC
  predC = exactly predC

instance (NumCat (->) a, ProductCat (->), CartCon con)
      => NumCat (Choice con) a where
  addC    = exactly addC
  mulC    = exactly mulC
  negateC = exactly negateC
  powIC   = exactly powIC

instance (IntegralCat (->) a, ProductCat (->), OkUnit (->), con ())
      => IntegralCat (Choice con) a where
  divC = exactly divC
  modC = exactly modC

instance (FractionalCat (->) a, ProductCat (->), OkUnit (->), con ())
      => FractionalCat (Choice con) a where
  recipC  = exactly recipC
  divideC = exactly divideC

instance (FloatingCat (->) a, ProductCat (->), OkUnit (->), con ())
      => FloatingCat (Choice con) a where
  expC = exactly expC
  cosC = exactly cosC
  sinC = exactly sinC

instance (RealFracCat (->) a b, ProductCat (->), OkUnit (->), con ())
      => RealFracCat (Choice con) a b where
  floorC    = exactly floorC
  ceilingC  = exactly ceilingC
  truncateC = exactly truncateC

instance (FromIntegralCat (->) a b, ProductCat (->), OkUnit (->), con ())
      => FromIntegralCat (Choice con) a b where
  fromIntegralC = exactly fromIntegralC

instance (BottomCat (->) a b, ProductCat (->), OkUnit (->), con ())
      => BottomCat (Choice con) a b where
  bottomC = exactly bottomC

instance (IfCat (->) a, ProductCat (->), CartCon con)
      => IfCat (Choice con) a where
  ifC = exactly ifC

instance (UnknownCat (->) a b, ProductCat (->), OkUnit (->), con ())
      => UnknownCat (Choice con) a b where
  unknownC = exactly unknownC

instance (RepCat (->) a r, ProductCat (->), OkUnit (->), con ())
      => RepCat (Choice con) a r where
  reprC = exactly reprC
  abstC = exactly abstC

instance (ArrayCat (->) a b, ProductCat (->), CartCon con)
      => ArrayCat (Choice con) a b where
  array = exactly array
  arrAt = exactly arrAt
