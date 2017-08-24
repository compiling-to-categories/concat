{-# LANGUAGE CPP #-}
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

-- | Nondeterministic arrows
data ND k a b = forall p. Ok k p => ND (p -> (a `k` b))

-- | Deterministic (trivially nondeterministic) arrow
exactly :: OkUnit k => (a `k` b) -> ND k a b
exactly f = ND (\ () -> f)

-- | Generate any value of type @p@.
class ChooseCat k p where
  choose' :: Ok k p => () `k` p

-- | Generate any value of type @p@.
choose :: (ChooseCat k' p, Ok k' p) => k' () p
choose = choose'
{-# INLINE [0] choose #-}

instance (ConstCat k p, Ok k ()) => ChooseCat (ND k) p where
  choose' = ND const

-- "choose'" vs "choose", since GHC eagerly inlines all methods to their
-- dictionary selectors, defeating translation across categories. Look for a
-- tidier alternative.

instance (Category k, OkProd k, OkUnit k) => Category (ND k) where
  type Ok (ND k) = Ok k
  id = exactly id
  -- ND g . ND f = ND (\ (p,q) -> g q . f p)
  ND (g :: q -> (b `k` c)) . ND (f :: p -> (a `k` b)) = ND (\ (p,q) -> g q . f p) <+ okProd @k @p @q

--   The constraint ‘OkProd k’ is no smaller than the instance head
--   (Use UndecidableInstances to permit this)

instance (ProductCat k, OkUnit k) => ProductCat (ND k) where
  exl = exactly exl
  exr = exactly exr 
  -- ND f &&& ND g = ND (\ (p,q) -> f p &&& g q)
  ND (f :: p -> (a `k` c)) &&& ND (g :: q -> (a `k` d)) = ND (\ (p,q) -> f p &&& g q) <+ okProd @k @p @q

instance (CoproductCat k, OkProd k, OkUnit k) => CoproductCat (ND k) where
  inl = exactly inl
  inr = exactly inr 
  -- ND f ||| ND g = ND (\ (p,q) -> f p ||| g q)
  ND (f :: p -> (a `k` c)) ||| ND (g :: q -> (b `k` c)) = ND (\ (p,q) -> f p ||| g q) <+ okProd @k @p @q

instance (DistribCat k, OkUnit k) => DistribCat (ND k) where
  distl = exactly distl
  distr = exactly distr 

instance (ClosedCat k, OkUnit k) => ClosedCat (ND k) where
  apply = exactly apply
  curry (ND f) = ND (curry . f)
  uncurry (ND g) = ND (uncurry . g)

instance (TerminalCat k, OkProd k, OkUnit k) => TerminalCat (ND k) where
  it = exactly it

instance (ConstCat k b, OkProd k, OkUnit k) => ConstCat (ND k) b where
  const b = exactly (const b)

instance (BoolCat k, OkProd k, OkUnit k) => BoolCat (ND k) where
  notC = exactly notC
  andC = exactly andC
  orC  = exactly orC
  xorC = exactly xorC

instance (EqCat k a, OkProd k, OkUnit k) => EqCat (ND k) a where
  equal    = exactly equal
  notEqual = exactly notEqual

instance (OrdCat k a, OkProd k, OkUnit k) => OrdCat (ND k) a where
  lessThan           = exactly lessThan
  greaterThan        = exactly greaterThan
  lessThanOrEqual    = exactly lessThanOrEqual
  greaterThanOrEqual = exactly greaterThanOrEqual

instance (EnumCat k a, OkProd k, OkUnit k) => EnumCat (ND k) a where
  succC = exactly succC
  predC = exactly predC

instance (NumCat k a, ProductCat k, OkUnit k) => NumCat (ND k) a where
  addC    = exactly addC
  mulC    = exactly mulC
  negateC = exactly negateC
  powIC   = exactly powIC

instance (IntegralCat k a, ProductCat k, OkUnit k) => IntegralCat (ND k) a where
  divC = exactly divC
  modC = exactly modC

instance (FractionalCat k a, ProductCat k, OkUnit k) => FractionalCat (ND k) a where
  recipC  = exactly recipC
  divideC = exactly divideC

instance (FloatingCat k a, ProductCat k, OkUnit k) => FloatingCat (ND k) a where
  expC = exactly expC
  cosC = exactly cosC
  sinC = exactly sinC

instance (RealFracCat k a b, ProductCat k, OkUnit k) => RealFracCat (ND k) a b where
  floorC    = exactly floorC
  ceilingC  = exactly ceilingC
  truncateC = exactly truncateC

instance (FromIntegralCat k a b, ProductCat k, OkUnit k) => FromIntegralCat (ND k) a b where
  fromIntegralC = exactly fromIntegralC

instance (BottomCat k a b, ProductCat k, OkUnit k) => BottomCat (ND k) a b where
  bottomC = exactly bottomC

instance (IfCat k a, ProductCat k, OkUnit k) => IfCat (ND k) a where
  ifC = exactly ifC

instance (UnknownCat k a b, ProductCat k, OkUnit k) => UnknownCat (ND k) a b where
  unknownC = exactly unknownC

instance (RepCat k a r, ProductCat k, OkUnit k) => RepCat (ND k) a r where
  reprC = exactly reprC
  abstC = exactly abstC

instance (ArrayCat k a b, ProductCat k, OkUnit k) => ArrayCat (ND k) a b where
  array = exactly array
  arrAt = exactly arrAt

