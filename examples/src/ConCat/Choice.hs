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

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Indexed sets of morphisms

module ConCat.Choice where

import Prelude hiding (id,(.),curry,uncurry,const)
import GHC.Types (Constraint)

import ConCat.Category

-- | Nondeterminism category. Like a set of morphisms all of the same type, but
-- represented as a function whose range is that set. The function's domain is
-- existentially hidden.

data Choice k a b = forall p. Ok k p => Choice (p -> (a `k` b))

-- Equivalently,

-- data Choice :: (* -> * -> *) -> * -> * -> * where
--   Choice :: Ok k p => (p -> (a `k` b)) -> Choice k a b

-- TODO: maybe revert to wiring in k = (->), transforming to another category
-- later.

-- | Deterministic (trivially nondeterministic) arrow
exactly :: OkUnit k => (a `k` b) -> Choice k a b
exactly f = Choice (\ () -> f)

-- | Generate any value of type @p@.
class ChoiceCat k p where
  choose' :: Ok k p => () `k` p

-- Or
--
--   choose' :: ((p :* a) `k` b) -> (a `k` b)

instance ChoiceCat (->) p where
  choose' = error "There isn't really a choose' for (->)"

-- | Generate any value of type @p@.
choose :: (ChoiceCat k' p, Ok k' p) => k' () p
choose = choose'
{-# INLINE [0] choose #-}

instance (ConstCat k p, Ok k ()) => ChoiceCat (Choice k) p where
  choose' = Choice const

-- "choose'" vs "choose", since GHC eagerly inlines all methods to their
-- dictionary selectors, defeating translation across categories. Look for a
-- tidier alternative.

instance (Category k, OkProd k, OkUnit k) => Category (Choice k) where
  type Ok (Choice k) = Ok k
  id = exactly id
  -- Choice g . Choice f = Choice (\ (p,q) -> g q . f p)
  Choice (g :: q -> (b `k` c)) . Choice (f :: p -> (a `k` b)) = Choice (\ (p,q) -> g q . f p) <+ okProd @k @p @q

--   The constraint ‘OkProd k’ is no smaller than the instance head
--   (Use UndecidableInstances to permit this)

instance (ProductCat k, OkUnit k) => ProductCat (Choice k) where
  exl = exactly exl
  exr = exactly exr
  -- Choice f &&& Choice g = Choice (\ (p,q) -> f p &&& g q)
  Choice (f :: p -> (a `k` c)) &&& Choice (g :: q -> (a `k` d)) = Choice (\ (p,q) -> f p &&& g q) <+ okProd @k @p @q

instance (CoproductCat k, OkProd k, OkUnit k) => CoproductCat (Choice k) where
  inl = exactly inl
  inr = exactly inr
  -- Choice f ||| Choice g = Choice (\ (p,q) -> f p ||| g q)
  Choice (f :: p -> (a `k` c)) ||| Choice (g :: q -> (b `k` c)) = Choice (\ (p,q) -> f p ||| g q) <+ okProd @k @p @q

instance (DistribCat k, OkUnit k) => DistribCat (Choice k) where
  distl = exactly distl
  distr = exactly distr

instance (ClosedCat k, OkUnit k) => ClosedCat (Choice k) where
  apply = exactly apply
  curry (Choice f) = Choice (curry . f)
  uncurry (Choice g) = Choice (uncurry . g)

instance (TerminalCat k, OkProd k, OkUnit k) => TerminalCat (Choice k) where
  it = exactly it

instance (ConstCat k b, OkProd k, OkUnit k) => ConstCat (Choice k) b where
  const b = exactly (const b)

instance (BoolCat k, OkProd k, OkUnit k) => BoolCat (Choice k) where
  notC = exactly notC
  andC = exactly andC
  orC  = exactly orC
  xorC = exactly xorC

instance (EqCat k a, OkProd k, OkUnit k) => EqCat (Choice k) a where
  equal    = exactly equal
  notEqual = exactly notEqual

instance (OrdCat k a, OkProd k, OkUnit k) => OrdCat (Choice k) a where
  lessThan           = exactly lessThan
  greaterThan        = exactly greaterThan
  lessThanOrEqual    = exactly lessThanOrEqual
  greaterThanOrEqual = exactly greaterThanOrEqual

instance (EnumCat k a, OkProd k, OkUnit k) => EnumCat (Choice k) a where
  succC = exactly succC
  predC = exactly predC

instance (NumCat k a, ProductCat k, OkUnit k) => NumCat (Choice k) a where
  addC    = exactly addC
  mulC    = exactly mulC
  negateC = exactly negateC
  powIC   = exactly powIC

instance (IntegralCat k a, ProductCat k, OkUnit k) => IntegralCat (Choice k) a where
  divC = exactly divC
  modC = exactly modC

instance (FractionalCat k a, ProductCat k, OkUnit k) => FractionalCat (Choice k) a where
  recipC  = exactly recipC
  divideC = exactly divideC

instance (FloatingCat k a, ProductCat k, OkUnit k) => FloatingCat (Choice k) a where
  expC = exactly expC
  cosC = exactly cosC
  sinC = exactly sinC

instance (RealFracCat k a b, ProductCat k, OkUnit k) => RealFracCat (Choice k) a b where
  floorC    = exactly floorC
  ceilingC  = exactly ceilingC
  truncateC = exactly truncateC

instance (FromIntegralCat k a b, ProductCat k, OkUnit k) => FromIntegralCat (Choice k) a b where
  fromIntegralC = exactly fromIntegralC

instance (BottomCat k a b, ProductCat k, OkUnit k) => BottomCat (Choice k) a b where
  bottomC = exactly bottomC

instance (IfCat k a, ProductCat k, OkUnit k) => IfCat (Choice k) a where
  ifC = exactly ifC

instance (UnknownCat k a b, ProductCat k, OkUnit k) => UnknownCat (Choice k) a b where
  unknownC = exactly unknownC

instance (RepCat k a r, ProductCat k, OkUnit k) => RepCat (Choice k) a r where
  reprC = exactly reprC
  abstC = exactly abstC

instance (ArrayCat k a b, ProductCat k, OkUnit k) => ArrayCat (Choice k) a b where
  array = exactly array
  arrAt = exactly arrAt

