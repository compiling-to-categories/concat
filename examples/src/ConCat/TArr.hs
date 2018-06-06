{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Domain-typed arrays

module ConCat.TArr where

import Prelude hiding (id, (.), const, curry)  -- Coming from ConCat.AltCat.

import GHC.TypeLits
import GHC.Types (Nat)
import Data.Proxy
-- import Data.Tuple            (swap)

import Data.Finite.Internal  (Finite(..))
import Data.Vector.Sized (Vector)
import qualified Data.Vector.Sized as V
import Control.Newtype
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable,index,tabulate,distributeRep)
import qualified Data.Functor.Rep as R

import ConCat.Misc           ((:*), (:+), cond,nat,int)
import ConCat.Rep
import ConCat.AltCat
import ConCat.Isomorphism

{----------------------------------------------------------------------
   Some useful isomorphisms.
----------------------------------------------------------------------}

type KnownNat2 m n = (KnownNat m, KnownNat n)

finSum :: forall m n. KnownNat2 m n => Finite m :+ Finite n <-> Finite (m + n)
finSum = Iso to un
 where 
   to (Left  (Finite l)) = Finite l
   to (Right (Finite k)) = Finite (k + nat @m)
   un (Finite l) | l < m     = Left  (Finite l)
                 | otherwise = Right (Finite (l - m))
    where
      m = nat @m
{-# INLINE finSum #-}

finProd :: forall m n. KnownNat2 m n => Finite m :* Finite n <-> Finite (m * n)
finProd = Iso to un
 where
   to (Finite l, Finite k) = Finite (l * nat @n + k)
   un (Finite l) = (Finite q, Finite r) where (q,r) = l `divMod` nat @n
{-# INLINE finProd #-}

#if 0

type a :^ b = b -> a

-- Using Horner's rule and its inverse, as per Conal's suggestion.
finExp :: forall m n. KnownNat2 m n => Finite m :^ Finite n <-> Finite (m ^ n)
finExp = Iso h g
  where -- g :: forall m n. KnownNat2 m n => Finite (m ^ n) -> Finite m :^ Finite n
        g (Finite l) = \ n -> v `V.index` n
          where v :: V.Vector n (Finite m)
                v = V.unfoldrN (first Finite . swap . flip divMod (nat @m)) l

        -- h :: forall m n. KnownNat2 m n => Finite m :^ Finite n -> Finite (m ^ n)
        -- h f = Finite $ V.foldl' (\accum m -> accum * (nat @m) + getFinite m)
        --                       0
        --                       $ V.reverse $ V.generate f
        -- h f = V.foldl' (curry u) (Finite 0) ((V.reverse . V.generate) f)
        -- h = V.foldl' (curry u) (Finite 0) . (V.reverse . V.generate)
        h = (V.foldl' . curry) u (Finite 0) . (V.reverse . V.generate)
          where u (Finite acc, Finite m) = Finite (acc * nat @m + m)

inFin :: (HasFin a, HasFin b) => (Finite (Card a) -> Finite (Card b)) -> (a -> b)
inFin f' = unFin . f' . toFin

liftFin :: (HasFin a, HasFin b) => (a -> b) -> Finite (Card a) -> Finite (Card b)
liftFin f = toFin . f . unFin

#endif

toFin :: HasFin a => a -> Finite (Card a)
toFin = isoFwd iso

unFin :: HasFin a => Finite (Card a) -> a
unFin = isoRev iso

{----------------------------------------------------------------------
   A class of types with known finite representations.
----------------------------------------------------------------------}

type KnownCard a = KnownNat (Card a)

type KnownCard2 a b = (KnownCard a, KnownCard b)

class KnownCard a => HasFin a where
  type Card a :: Nat
  iso :: a <-> Finite (Card a)

instance HasFin () where
  type Card () = 1
  iso = Iso (const (Finite 0)) (const ())

instance HasFin Bool where
  type Card Bool = 2
  iso = Iso (Finite . cond 1 0) (\ (Finite n) -> n > 0)

instance KnownNat n => HasFin (Finite n) where
  type Card (Finite n) = n
  iso = id

instance (HasFin a, HasFin b) => HasFin (a :+ b) where
  type Card (a :+ b) = Card a + Card b
  iso = finSum . (iso +++ iso)

instance (HasFin a, HasFin b) => HasFin (a :* b) where
  type Card (a :* b) = Card a * Card b
  iso = finProd . (iso *** iso)

-- instance (HasFin a, HasFin b) => HasFin (a :^ b) where
--   type Card (a :^ b) = Card a ^ Card b
--   iso = finExp . Iso liftFin inFin

{----------------------------------------------------------------------
  Domain-typed "arrays"
----------------------------------------------------------------------}

newtype Arr a b = Arr (Vector (Card a) b)

instance Newtype (Arr a b) where
  type O (Arr a b) = Vector (Card a) b
  pack v = Arr v
  unpack (Arr v) = v

instance HasRep (Arr a b) where
  type Rep (Arr a b) = O (Arr a b)
  abst = pack
  repr = unpack

-- TODO: maybe a macro for HasRep instances that mirror Newtype instances.

deriving instance Functor (Arr a)
deriving instance HasFin a => Applicative (Arr a)

-- TODO: Distributive and Representable instances.

instance HasFin a => Distributive (Arr a) where
  distribute :: Functor f => f (Arr a b) -> Arr a (f b)
  distribute = distributeRep
  {-# INLINE distribute #-}

instance HasFin a => Representable (Arr a) where
  type Rep (Arr a) = a
  tabulate :: (a -> b) -> Arr a b
  tabulate f = pack (tabulate (f . unFin))
  index :: Arr a b -> (a -> b)
  Arr v `index` a = v `index` toFin a
  {-# INLINE tabulate #-}
  {-# INLINE index #-}

(!) :: HasFin a => Arr a b -> (a -> b)
(!) = index
{-# INLINE (!) #-}

instance (HasFin a, Foldable ((->) a)) => Foldable (Arr a) where
  foldMap f = foldMap f . index  -- fold homomorphism
  {-# INLINE foldMap #-}

type Flat f = Arr (R.Rep f)

{--------------------------------------------------------------------
    Splitting
--------------------------------------------------------------------}

chunk :: KnownNat2 m n => Vector (m * n) a -> Finite m -> Vector n a
chunk mn i = tabulate (index mn . curry toFin i)

#if 0

                mn                  :: Vector (m * n) a
                                 i  :: Finite m
                           toFin    :: Finite m :* Finite n -> Finite (m :* n)
                     curry toFin    :: Finite m -> Finite n -> Finite (m :* n)
                     curry toFin i  :: Finite n -> Finite (m :* n)
          index mn                  :: Finite (m :* n) -> a
          index mn . curry toFin i  :: Finite n -> a
tabulate (index mn . curry toFin i) :: Vector n a

#endif

vecSplitProd :: KnownNat2 m n => Vector (m * n) a -> Vector m (Vector n a)
vecSplitProd = tabulate . chunk

-- vecSplitProd mn = tabulate (chunk mn)
-- vecSplitProd mn = tabulate (\ i -> chunk mn i)

arrSplitProd :: KnownCard2 a b => Arr (a :* b) c -> Arr a (Arr b c)
arrSplitProd = pack . fmap pack . vecSplitProd . unpack
