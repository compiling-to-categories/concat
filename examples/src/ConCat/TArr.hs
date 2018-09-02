{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
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

#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
{-# LANGUAGE NoStarIsType #-}
#endif

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -Wno-unused-binds #-}   -- TEMP

-- When spurious recompilation is fixed, use this plugin, and drop ConCat.Known.
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

-- | Domain-typed arrays

module ConCat.TArr
  ( HasFin(..),HasFin',toFin,unFin
  , Arr(..),Flat,flat,toFlat,unFlat
  , vecU1, vecPar1, vecProd, vecComp
  , arrU1, arrPar1, arrProd, arrComp
  , reverseF
  ) where

import Prelude hiding (id, (.), const, curry, uncurry)  -- Coming from ConCat.AltCat.

import Data.Monoid
import Data.Foldable
import GHC.TypeLits
import GHC.Types (Nat)
import GHC.Generics (U1(..),Par1(..),(:*:)(..),(:.:)(..))
import GHC.Exts (Coercible,coerce)
-- import Data.Proxy
-- import Data.Tuple            (swap)

import Data.Finite.Internal  (Finite(..))
import Data.Finite  (finite)
import Data.Vector.Sized (Vector)
import qualified Data.Vector.Generic.Sized.Internal
-- import qualified Data.Vector.Sized as V
import Control.Newtype.Generics
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(..),distributeRep)
import Data.Constraint ((\\))
import Data.Void

import ConCat.Misc ((:+), (:*), cond,nat)  -- ,int
import qualified ConCat.Rep as R
import ConCat.AltCat
import ConCat.Isomorphism
import ConCat.Known

{----------------------------------------------------------------------
   Some useful isomorphisms.
----------------------------------------------------------------------}

-- TODO: reverse the sense of finU1, finPar1, finSum and finProd

finU1 :: Void <-> Finite 0
finU1 = absurd :<-> error "no Finite 0"

finPar1 :: () <-> Finite 1
finPar1 = const (Finite 0) :<-> const ()

finSum  :: forall k m n. (FiniteCat k, KnownNat2 m n)
        => Iso k (Finite m :+ Finite n) (Finite (m + n))
finSum  = combineSum :<-> separateSum
{-# INLINE finSum #-}

finProd  :: forall k m n. (FiniteCat k, KnownNat2 m n)
         => Iso k (Finite m :* Finite n) (Finite (m * n))
finProd  = combineProd :<-> separateProd
{-# INLINE finProd #-}

-- finSum :: forall m n. KnownNat m => Finite m :+ Finite n <-> Finite (m + n)
-- finSum = Iso combineSum separateSum

-- finSum = Iso to un
--  where 
--    to (Left  (Finite l)) = Finite l
--    to (Right (Finite k)) = Finite (nat @m + k)
--    un (Finite l) | l < m     = Left  (Finite l)
--                  | otherwise = Right (Finite (l - m))
--     where
--       m = nat @m

-- finProd :: forall m n. KnownNat n => Finite m :* Finite n <-> Finite (m * n)
-- finProd = Iso combineProd separateProd

-- finProd = Iso to un
--  where
--    to (Finite l, Finite k) = Finite (nat @n * l + k)
--    un (Finite l) = (Finite q, Finite r) where (q,r) = l `divMod` nat @n

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

#if 1
toFin :: HasFin a => a -> Finite (Card a)
toFin = isoFwd fin

unFin :: HasFin a => Finite (Card a) -> a
unFin = isoRev fin
#else

toFin :: HasFin a => a -> Finite (Card a)
toFin = f where f :<-> _ = fin

unFin :: forall a. HasFin a => Finite (Card a) -> a
unFin = f' where _ :<-> f' = fin

#endif

vecU1 :: Vector 0 <--> U1
vecU1 = reindex finU1

vecPar1 :: Vector 1 <--> Par1
vecPar1 = reindex finPar1

#if 0

repIso :: Vector (m + n) a <-> Finite (m + n) -> a
dom finSum :: (Finite (m + n) -> a) <-> (Finite m :+ Finite n -> a)
inv joinIso :: (Finite m :+ Finite n -> a) <-> (Finite m -> a) :* (Finite n -> a)
inv (repIso *** repIso) :: (Finite m -> a) :* (Finite n -> a) <-> Vector m a :* Vector n a
inv newIso :: Vector m a :* Vector n a <-> (Vector m :*: Vector n) a

vecProd = inv newIso . inv (repIso *** repIso) . inv joinIso . dom finSum . repIso
        = inv (joinIso . (repIso *** repIso) . newIso) . dom finSum . repIso

#endif

#if 0

i1 :: forall m n a. KnownNat2 m n
   => Vector (m + n) a <-> (Finite (m + n) -> a)
i1 = repIso \\ knownAdd @m @n

i2 :: KnownNat2 m n
   => (Finite (m + n) -> a) <-> (Finite m :+ Finite n -> a)
i2 = dom finSum

i3 :: (Finite m :+ Finite n -> a) <-> (Finite m -> a) :* (Finite n -> a)
i3 = inv joinIso

i4 :: KnownNat2 m n
   => (Finite m -> a) :* (Finite n -> a) <-> Vector m a :* Vector n a
i4 = inv (repIso *** repIso)

i5 :: Vector m a :* Vector n a <-> (Vector m :*: Vector n) a
i5 = inv newIso

#endif

-- vecU1 :: Vector 0 <--> V1
-- vecU1 

vecProd :: forall m n. KnownNat2 m n => Vector (m + n) <--> Vector m :*: Vector n
vecProd = reindex finSum \\ knownAdd @m @n

-- vecProd = i5 . i4 . i3 . i2 . i1 @m @n

-- vecProd = inv newIso . inv (repIso *** repIso) . inv joinIso . dom finSum . repIso
--         \\ knownAdd @m @n

-- vecProd = inv (joinIso . (repIso *** repIso) . newIso) . dom finSum . repIso
--         \\ knownAdd @m @n

-- reindex :: (Representable f, Representable g)
--         => (Rep f <-> Rep g) -> (f <--> a)
-- reindex h = inv repIso . inv (dom h) . repIso

#if 0

finSum  :: KnownNat2 m n => (Finite m :+ Finite n) <-> Finite (m + n)
finProd :: KnownNat2 m n => (Finite m :* Finite n) <-> Finite (m * n)

    finSum  :: (Finite m :+ Finite n) <-> Finite (m + n)
inv finSum  :: Finite (m + n) <-> Finite m :+ Finite n
reindex     :: (Rep (Vector (m + n) <-> Rep (Vector m :*: Vector n)) -> (Vector (m + n) <--> Rep (Vector m :*: Vector n))
        :: (Finite (m + n) <-> Rep (Vector m) :* Rep (Vector n)) -> (Vector (m + n) <--> Rep (Vector m :*: Vector n))
        :: (Finite (m + n) <-> Finite m :* Finite n) -> (Vector (m + n) <--> Rep (Vector m :*: Vector n))

    finSum :: (Finite m :+ Finite n) <-> Finite (m + n)
inv finSum :: Finite (m + n) <-> Finite m :+ Finite n
           :: Rep (Vector (m + n)) <-> Rep (Vector m) :+ Rep (Vector n)
           :: Rep (Vector (m + n)) <-> Rep (Vector m :*: Vector n)
reindex (inv finSum) :: Vector (m + n) <--> Vector m :*: Vector n

    finProd :: (Finite m :* Finite n) <-> Finite (m * n)
inv finProd :: Finite (m * n) <-> Finite m :* Finite n
            :: Rep (Vector (m * n)) <-> Rep (Vector m) :* Rep (Vector n)
            :: Rep (Vector (m * n)) <-> Rep (Vector m :.: Vector n)
reindex (inv finProd) :: Vector (m * n) <--> Vector m :.: Vector n

#endif

#if 0

i1 :: forall m n a. KnownNat2 m n => Vector (m * n) a <-> (Finite (m * n) -> a)
i1 = repIso \\ knownMul @m @n

i2 :: KnownNat2 m n => (Finite (m * n) -> a) <-> (Finite m :* Finite n -> a)
i2 = dom finProd

i3 :: (Finite m :* Finite n -> a) <-> (Finite m -> Finite n -> a)
i3 = curryIso

i4 :: KnownNat n => (Finite m -> Finite n -> a) <-> (Finite m -> Vector n a)
i4 = inv (cod repIso)

i5 :: KnownNat m => (Finite m -> Vector n a) <-> Vector m (Vector n a)
i5 = inv repIso

i6 :: Vector m (Vector n a) <-> (Vector m :.: Vector n) a
i6 = inv newIso

#endif

vecComp :: forall m n. KnownNat2 m n
        => Vector (m * n) <--> Vector m :.: Vector n

-- vecComp = i6 . i5 . i4 . i3 . i2 . i1 @m @n

-- vecComp = inv newIso . inv repIso . inv (cod repIso) . curryIso . dom finProd . repIso
--         \\ knownMul @m @n

-- vecComp = inv (cod repIso . repIso . newIso) . curryIso . dom finProd . repIso
--         \\ knownMul @m @n

vecComp = reindex finProd \\ knownMul @m @n

{----------------------------------------------------------------------
   A class of types with known finite cardinalities.
----------------------------------------------------------------------}

type KnownCard a = KnownNat (Card a)

type KnownCard2 a b = (KnownCard a, KnownCard b)

class {- KnownCard a => -} HasFin a where
  type Card a :: Nat
  fin :: a <-> Finite (Card a)

-- See below.
type HasFin' a = (KnownCard a, HasFin a)

instance HasFin Void where
  type Card Void = 0
  fin = finU1

instance HasFin () where
  type Card () = 1
  fin = finPar1

instance HasFin Bool where
  type Card Bool = 2
  fin = (Finite . cond 1 0) :<-> (\ (Finite n) -> n > 0)

instance KnownNat n => HasFin (Finite n) where
  type Card (Finite n) = n
  fin = id

-- Moving KnownCard from HasFin to HasFin' solves the puzzle of persuading GHC
-- that KnownCard (a :+ b), a superclass constraint for HasFin (a :+ b). When
-- the spurious recompilation problem is fixed (GHC 8.6), and we drop the explicit
-- KnownNat entailments, move KnownCard back to HasFin.

instance (HasFin' a, HasFin' b) => HasFin (a :+ b) where
  type Card (a :+ b) = Card a + Card b
  fin = finSum . (fin +++ fin)
  -- fin = (combineSum :<-> separateSum) . (fin +++ fin)

instance (HasFin' a, HasFin' b) => HasFin (a :* b) where
  type Card (a :* b) = Card a * Card b
  fin = finProd . (fin *** fin)
  -- fin = (combineProd :<-> separateProd) . (fin *** fin)

-- instance (HasFin' a, HasFin' b) => HasFin (a :* b) where
--   type Card (a :* b) = Card a * Card b
--   fin = finProd . (fin *** fin)

-- instance (HasFin a, HasFin b) => HasFin (a :^ b) where
--   type Card (a :^ b) = Card a ^ Card b
--   fin = finExp . Iso liftFin inFin

{----------------------------------------------------------------------
  Domain-typed "arrays"
----------------------------------------------------------------------}

type VC a = Vector (Card a)

newtype Arr a b = Arr (VC a b)

instance Newtype (Arr a b) where
  type O (Arr a b) = VC a b
  pack v = Arr v
  unpack (Arr v) = v

instance R.HasRep (Arr a b) where
  type Rep (Arr a b) = O (Arr a b)
  abst = pack
  repr = unpack

-- TODO: maybe a macro for HasRep instances that mirror Newtype instances.

#if 1

deriving instance Functor (Arr a)
deriving instance KnownCard a => Applicative (Arr a)

#elif 0

instance Functor (Arr a) where
  fmap :: forall u v. (u -> v) -> Arr a u -> Arr a v
  fmap = coerce (fmap @(VC a) @u @v)

-- instance KnownCard a => Applicative (Arr a) where
--   pure = coerce (pure @(VC a))
--   (<*>) = coerce ((<*>) @(VC a))

#else

instance Functor (Arr a) where
  fmap h (Arr bs) = Arr (fmap h bs)

instance KnownCard a => Applicative (Arr a) where
  pure a = Arr (pure a)
  Arr fs <*> Arr xs = Arr (fs <*> xs)

#endif

instance HasFin' a => Distributive (Arr a) where
  distribute :: Functor f => f (Arr a b) -> Arr a (f b)
  distribute = distributeRep
  {-# INLINE distribute #-}

instance HasFin' a => Representable (Arr a) where
  type Rep (Arr a) = a
  tabulate :: (a -> b) -> Arr a b
  index :: Arr a b -> (a -> b)
  -- tabulate f = pack (tabulate (f . unFin))
  -- xs `index` a = unpack xs `index` toFin a
  index    = isoFwd arrFun
  tabulate = isoRev arrFun
  {-# INLINE tabulate #-}
  {-# INLINE index #-}

-- i.e. tabulate :<-> index = arr

-- TODO: combine tabulate and index into a single Iso
-- Did it as arr below. Reconcile the redundant definitions.

(!) :: HasFin' a => Arr a b -> (a -> b)
(!) = index
{-# INLINE (!) #-}

{--------------------------------------------------------------------
    
--------------------------------------------------------------------}

-- vecU1 :: Vector 0 <--> U1
-- vecPar1 :: Vector 1 <--> Par1
-- vecProd :: KnownNat2 m n => Vector (m + n) <--> Vector m :*: Vector n
-- vecComp :: KnownNat2 m n => Vector (m * n) <--> Vector m :.: Vector n

arrU1 :: Arr Void <--> U1
arrU1 = vecU1 . newIso

arrPar1 :: Arr () <--> Par1
arrPar1 = vecPar1 . newIso

arrProd :: forall a b. KnownCard2 a b => Arr (a :+ b) <--> Arr a :*: Arr b
-- arrProd = inv newIso . inv (newIso *** newIso) . newIso . vecProd . newIso

-- arrProd = inv ((newIso *** newIso) . newIso) . newIso . vecProd . newIso

-- arrProd = reindexFinProd ...

-- arrProd = coerce (vecProd @(Card a) @(Card b)) -- nope

-- arrProd = coerceIso . vecProd . newIso

-- arrProd = coerceIso . vecProd @(Card a) @(Card b) . coerceIso  -- okay

arrProd = coerceIso . vecProd @(Card a) @(Card b) . newIso -- for consistency with arrComp

-- arrProd = undefined . newIso
-- arrProd = undefined . vecProd @(Card a) @(Card b) . newIso

-- arrProd = undefined . reindexId @(VC (a :+ b)) @(VC a :*: VC b) . vecProd @(Card a) @(Card b) . newIso

-- i2 :: VC (a :+ b) <--> VC a :*: VC b
-- i2 = reindexId

-- foo1 :: (Vector 2 Int <-> Vector 2 Float) -> (Arr Bool Int <-> Arr Bool Float)
-- foo1 = coerce

-- arrProd' :: forall a b. KnownCard2 a b => Arr (a :+ b) <--> Arr a :*: Arr b
-- arrProd' = coerceIso . vecProd @(Card a) @(Card b) . newIso

#if 0

i1 :: Arr (a :+ b) <--> Vector (Card a + Card b)
i1 = coerceIso

i2 :: KnownCard2 a b => Vector (Card a + Card b) <--> Vector (Card a) :*: Vector (Card b)
i2 = vecProd

i3 :: Vector (Card a) :*: Vector (Card b) <--> Arr a :*: Arr b
i3 = coerceIso

#endif

#if 0

newIso :: Arr (a :+ b) <--> VC (a :+ b)
vecProd :: VC (a :+ b) <--> (VC a :*: VC b)
newIso :: (VC a :*: VC b) z <-> VC a z :* VC b z
inv (newIso *** newIso) ::
  (VC a z :* VC b z) <-> Arr a z :* Arr b z
inv newIso :: (Arr a z :* Arr b z) <-> (Arr a :*: Arr b) z

#endif

arrComp :: forall a b. KnownCard2 a b => Arr (a :* b) <--> Arr a :.: Arr b

-- arrComp = inv newIso . inv newIso . inv (fmapI newIso) . newIso . vecComp . newIso

-- arrComp = inv (fmapC newIso . newIso . newIso) . newIso . vecComp . newIso

-- arrComp = i6 . i5 . i4 @a . i3 @a @b . i2 @a @b . i1

-- arrComp = coerceIso . vecComp @(Card a) @(Card b) . newIso

arrComp = coerceIso . vecComp @(Card a) @(Card b) . newIso

#if 0

-- vecComp :: forall m n. KnownNat2 m n => Vector (m * n) <--> Vector m :.: Vector n

i1 :: Arr (a :* b) <--> Vector (Card a * Card b)
i1 = coerceIso

i2 :: KnownCard2 a b => Vector (Card a * Card b) <--> Vector (Card a) :.: Vector (Card b)
i2 = vecComp

i2' :: forall a b. KnownCard2 a b => Vector (Card a * Card b) <--> Vector (Card a) :.: Vector (Card b)
i2' = vecComp @(Card a) @(Card b)

i3 :: Vector (Card a) :.: Vector (Card b) <--> Arr a :.: Arr b
i3 = coerceIso

i4 :: KnownCard2 a b => Arr (a :* b) <--> Vector (Card a) :.: Vector (Card b)
i4 = vecComp . coerceIso

i5 :: forall a b. KnownCard2 a b => Vector (Card a * Card b) <--> Arr a :.: Arr b
i5 = coerceIso . vecComp @(Card a) @(Card b)

-- i6 :: forall a b. KnownCard2 a b => Arr (a :* b) <--> Arr a :.: Arr b
-- i6 = coerceIso . vecComp @(Card a) @(Card b) . coerceIso -- type error

i6' :: forall a b. KnownCard2 a b => Arr (a :* b) <--> Arr a :.: Arr b
i6' = i3 . i2 @a @b . i1

i6'' :: forall a b. KnownCard2 a b => Arr (a :* b) <--> Arr a :.: Arr b
i6'' = (coerceIso :: Vector (Card a) :.: Vector (Card b) <--> Arr a :.: Arr b) . vecComp . coerceIso -- type error

i6''' :: forall a b. KnownCard2 a b => Arr (a :* b) <--> Arr a :.: Arr b
i6''' = i3 . vecComp @(Card a) @(Card b) . coerceIso

z1 :: forall a b. KnownCard2 a b => Arr (a :* b) <--> Vector (Card a) :.: Vector (Card b)
z1 = vecComp @(Card a) @(Card b) . coerceIso

z2 :: forall a b. KnownCard2 a b => Arr (a :* b) <--> Arr a :.: Arr b
z2 = i3 . vecComp @(Card a) @(Card b) . coerceIso

-- z3 :: forall a b. KnownCard2 a b => Arr (a :* b) <--> Arr a :.: Arr b
-- z3 = coerceIso . vecComp @(Card a) @(Card b) . coerceIso

-- z4 :: forall a b z. KnownCard2 a b => Arr (a :* b) z <-> (Arr a :.: Arr b) z
-- z4 = coerceIso . vecComp @(Card a) @(Card b) . coerceIso


i7 :: forall a b c. KnownCard2 a b => Arr (a :* b) c <-> (Arr a :.: Arr b) c
i7 = coerceIso . vecComp @(Card a) @(Card b) . coerceIso @(->) @(Arr (a :* b) c) @(Vector (Card a * Card b) c)

i8 :: forall a b. KnownCard2 a b => Arr (a :+ b) <--> Arr a :*: Arr b
i8 = coerceIso . vecProd @(Card a) @(Card b) . coerceIso  -- okay

-- vecProd :: forall m n. KnownNat2 m n => Vector (m + n) <--> Vector m :*: Vector n
-- vecComp :: forall m n. KnownNat2 m n => Vector (m * n) <--> Vector m :.: Vector n

#endif

#if 0

i1 :: Arr (a :* b) <--> VC (a :* b)
i1 = newIso

i2 :: KnownCard2 a b => VC (a :* b) <--> VC a :.: VC b
i2 = vecComp

i3 :: (VC a :.: VC b) z <-> VC a (VC b z)
i3 = newIso

i4 :: KnownCard a => VC a (VC b z) <-> VC a (Arr b z)
i4 = fmapC (inv newIso)

i5 :: VC a (Arr b z) <-> Arr a (Arr b z)
i5 = inv newIso

i6 :: Arr a (Arr b z) <-> (Arr a :.: Arr b) z
i6 = inv newIso

#endif

#if 0

newIso :: Arr (a :* b) <--> VC (a :* b)
vecComp :: VC (a :* b) <--> VC a :.: VC b
newIso :: (VC a :.: VC b) z <-> VC a (VC b z)
fmapI (inv newIso) :: VC a (VC b z) <-> VC a (Arr b z)
inv newIso :: VC a (Arr b z) <-> Arr a (Arr b z)
inv newIso :: Arr a (Arr b z) <-> (Arr a :.: Arr b) z

#endif

#if 0

-- Generalize from Arr

-- type Funish (f :: * -> * -> *) = forall a. Rep (f a) ~ a

-- funishU1   :: Funish f => f Void     <--> U1
-- funishPar1 :: Funish f => f Unit     <--> Par1

-- funishProd :: Funish f => f (a :+ b) <--> f a :*: f b
-- funishProd = reindex id

-- funishComp :: Funish f => f (a :* b) <--> f a :.: f b

class Funish f where
  funish :: Dict (Rep (f a) ~ a)

funishProd :: forall f a b. Funish f
           => f (a :+ b) <--> f a :*: f b
funishProd | Dict <- funish @f @a
           , Dict <- funish @f @b
           , Dict <- funish @f @(a :+ b)
           = reindex id 

#endif


#if 0

reindexId :: (Representable f, Representable g, Rep f ~ Rep g) => (f <--> g)
reindexId = reindex id
          -- = inv repIso . repIso

arrU1'   :: Arr Void     <--> U1
arrU1' = reindexId

arrPar1' :: Arr ()     <--> Par1
arrPar1' = reindexId

arrProd' :: forall a b. (HasFin' a, HasFin' b)
         => Arr (a :+ b) <--> Arr a :*: Arr b
arrProd' = reindexId \\ knownAdd @(Card a) @(Card b)

arrComp' :: forall a b. (HasFin' a, HasFin' b)
         => Arr (a :* b) <--> Arr a :.: Arr b
arrComp' = reindexId \\ knownMul @(Card a) @(Card b)

#endif

-- reindexFin :: HasFin' a => VC a <--> Arr a
reindexFin :: (Representable g, Rep g ~ a, HasFin' a) => VC a <--> g
reindexFin = reindex fin

reindexFin' :: (Representable g, Rep g ~ a, HasFin' a) => Arr a <--> g
reindexFin' = reindex fin . newIso
-- reindexFin' = reindex id

reindexFinProd :: (HasFin' a, HasFin' b) => VC a :*: VC b <--> Arr a :*: Arr b
-- reindexFinProd = reindex (fin +++ fin)
reindexFinProd = coerceIso

-- reindexFinComp :: (HasFin' a, HasFin' b) => VC a :.: VC b <--> Arr a :.: Arr b
-- -- reindexFinComp = reindex (fin *** fin)
-- reindexFinComp = coerceIso

-- foo :: HasFin' b => VC b <--> Arr b
-- foo = coerceIso

-- foo :: (VC a :.: VC b) z -> (Arr a :.: Arr b) z  -- error
-- foo :: (VC a :.: VC b) z -> (VC a :.: Arr b) z  -- error
-- foo :: VC a (VC b z) -> VC a (Arr b z)  -- error
-- foo :: Vector 1 (VC b z) -> Vector 1 (Arr b z)  -- error

-- foo :: Coercible a b => Vector 1 a -> Vector 1 b -- error

-- foo :: Coercible a b => [a] -> [b] -- okay

-- foo :: (VC b z, ()) -> (Ar r b z, ())  -- okay
-- foo :: [VC b z] -> [Arr b z]  -- okay
-- foo :: VC b z -> Arr b z  -- okay
-- foo :: (VC a :.: VC b) z -> (Arr a :.: VC b) z  -- okay
-- foo :: (VC a :.: VC b) z -> VC a (VC b z)  -- okay
-- foo :: (Arr a :.: Arr b) z -> Arr a (Arr b z) -- okay

-- foo = coerce

{--------------------------------------------------------------------
    Splitting
--------------------------------------------------------------------}

chunk :: forall m n a. KnownNat2 m n => Vector (m * n) a -> Finite m -> Vector n a
chunk mn i = tabulate (index mn . curry toFin i) \\ knownMul @m @n
{-# INLINE chunk #-}

#if 0

                as                  :: Vector (m * n) a
                                 i  :: Finite m
                           toFin    :: Finite m :* Finite n -> Finite (m :* n)
                     curry toFin    :: Finite m -> Finite n -> Finite (m :* n)
                     curry toFin i  :: Finite n -> Finite (m :* n)
          index as                  :: Finite (m :* n) -> a
          index as . curry toFin i  :: Finite n -> a
tabulate (index as . curry toFin i) :: Vector n a

#endif

vecSplitSum :: forall m n a. KnownNat2 m n => Vector (m + n) a -> Vector m a :* Vector n a
vecSplitSum as = (tabulate *** tabulate) (unjoin (index as . toFin)) \\ knownAdd @m @n
{-# INLINE vecSplitSum #-}

#if 0

                             as           :: Vector (m + n) a
                       index as           :: Finite (m + n) -> a
                       index as . toFin   :: Finite m :+ Finite n -> a
               unjoin (index as . toFin)  :: (Finite m -> a) :* (Finite n -> a)
(tab *** tab) (unjoin (index as . toFin)) :: Vector m a :* Vector n a

#endif

arrSplitSum :: KnownCard2 a b => Arr (a :+ b) c -> Arr a c :* Arr b c
arrSplitSum = (pack *** pack) . vecSplitSum . unpack
{-# INLINE arrSplitSum #-}

vecSplitProd :: KnownNat2 m n => Vector (m * n) a -> Vector m (Vector n a)
vecSplitProd = tabulate . chunk
{-# INLINE vecSplitProd #-}

-- vecSplitProd as = tabulate (chunk as)
-- vecSplitProd as = tabulate (\ i -> chunk as i)

arrSplitProd :: KnownCard2 a b => Arr (a :* b) c -> Arr a (Arr b c)
arrSplitProd = pack . fmap pack . vecSplitProd . unpack
{-# INLINE arrSplitProd #-}

{--------------------------------------------------------------------
    Folds
--------------------------------------------------------------------}

#if 0

deriving instance Foldable (Arr a)

#elif 0

instance Foldable (Arr a) where
  foldMap f = foldMap f . unpack
  {-# INLINE foldMap #-}

#elif 0

instance (HasFin' a, Foldable ((->) a)) => Foldable (Arr a) where
  foldMap f = foldMap f . index
  {-# INLINE foldMap #-}

#elif 1

instance (Decomposable a, Foldable (Decomp a)) => Foldable (Arr a) where
  foldMap f = foldMap f . isoFwd decomp
  {-# INLINE foldMap #-}

-- TODO: Maybe use reindexId with just an associated functor.

class Decomposable a where
  type Decomp a :: * -> *
  decomp :: Arr a <--> Decomp a

type Decomposable' a = (Decomposable a, HasFin' a)

-- TODO: rename Decomposable to something less generic

instance Decomposable Void where
  type Decomp Void = U1
  decomp = arrU1

instance Decomposable () where
  type Decomp () = Par1
  decomp = arrPar1

instance (Decomposable' a, Decomposable' b) => Decomposable (a :+ b) where
  type Decomp (a :+ b) = Arr a :*: Arr b
  decomp = reindexId \\ knownAdd @(Card a) @(Card b)
  -- decomp = arrProd -- okay
  -- decomp = coerceIso . vecProd @(Card a) @(Card b) . newIso -- okay
  -- decomp = coerceIso . (reindex finSum \\ knownAdd @(Card a) @(Card b)) . newIso -- nope

instance (Decomposable' a, Decomposable' b) => Decomposable (a :* b) where
  type Decomp (a :* b) = Arr a :.: Arr b
  decomp = arrComp

#else

-- The explicit repetition of the fold and sum defaults below prevent premature
-- optimization that leads to exposing the representation of unsized vectors.
-- See 2018-06-07 journal notes.

#define DEFAULTS \
fold = foldMap id ; \
{-# INLINE fold #-} ; \
sum = getSum . foldMap Sum ; \
{-# INLINE sum #-}

instance Foldable (Arr Void) where
  -- foldMap _ _ = mempty
  foldMap f = foldMap f . isoFwd arrU1
  -- foldMap f = foldMap f . isoFwd vecU1 . unpack
  -- foldMap f = foldMap f . isoFwd (reindex finU1 :: Vector 0 <--> U1) . unpack
  {-# INLINE foldMap #-}
  DEFAULTS
  -- fold = foldMap id ; {-# INLINE fold #-}
  -- sum = getSum . foldMap Sum ; {-# INLINE sum #-}

instance Foldable (Arr ()) where
  -- foldMap f xs = f (xs ! ())
  foldMap f = foldMap f . isoFwd arrPar1
  -- foldMap f = foldMap f . isoFwd vecPar1 . unpack
  {-# INLINE foldMap #-}
  DEFAULTS
  -- fold = foldMap id ; {-# INLINE fold #-}
  -- sum = getSum . foldMap Sum ; {-# INLINE sum #-}

instance Foldable (Arr Bool) where
  foldMap f xs = f (xs ! False) <> f (xs ! True)
  {-# INLINE foldMap #-}
  DEFAULTS
  -- sum = getSum . foldMap Sum ; {-# INLINE sum #-}
  -- fold = foldMap id; {-# INLINE fold #-}

instance (Foldable (Arr a), Foldable (Arr b), KnownCard2 a b)
      => Foldable (Arr (a :+ b)) where
  foldMap f = foldMap f . isoFwd arrProd
  -- foldMap f u = foldMap f v <> foldMap f w where (v,w) = arrSplitSum u
  -- foldMap f = uncurry (<>) . (foldMap f *** foldMap f) . arrSplitSum
  -- foldMap f = foldMap f . isoFwd (vecProd @(Card a) @(Card b)) . unpack
  {-# INLINE foldMap #-}
  DEFAULTS
  -- sum = getSum . foldMap Sum ; {-# INLINE sum #-}
  -- fold = foldMap id; {-# INLINE fold #-}

instance (Foldable (Arr a), Foldable (Arr b), KnownCard2 a b)
      => Foldable (Arr (a :* b)) where
  foldMap f = foldMap f . isoFwd arrComp
  -- foldMap f = (foldMap.foldMap) f . arrSplitProd
  -- foldMap f = fold . fmap f
  -- foldMap f = foldMap f . isoFwd (vecComp @(Card a) @(Card b)) . unpack
  {-# INLINE foldMap #-}
  DEFAULTS
  -- fold = fold . isoFwd arrComp
  -- fold = fold . fmap fold . arrSplitProd
  -- {-# INLINE fold #-}
  -- sum = getSum . foldMap Sum ; {-# INLINE sum #-}

#endif

arrFun :: HasFin' a => Arr a b <-> (a -> b)
arrFun = dom fin . repIso . newIso

#if 0

arr :: HasFin' a => (a -> b) <-> Arr a b
arr = inv newIso . inv repIso . dom (inv fin)
-- arr = inv (dom fin . repIso . newIso)
-- arr = inv repIso

-- arr' :: HasFin' a => Arr a b <-> (a -> b)
-- arr' = dom fin . repIso . newIso

toArr :: HasFin' a => (a -> b) -> Arr a b
-- toArr = isoFwd arr
-- toArr = isoRev arr'
toArr = pack . tabulate . dom unFin
-- toArr f = Arr (tabulate (f . unFin))

unArr :: HasFin' a => Arr a b -> (a -> b)
-- unArr = isoRev arr
-- unArr = isoFwd arr'
-- unArr = isoFwd (dom fin . repIso . newIso)
-- unArr = isoFwd (dom fin) . isoFwd repIso . isoFwd newIso
-- unArr = dom (isoFwd fin) . index . unpack
unArr = dom toFin . index . unpack
-- unArr = (toFin ^^^ id) . index . unpack
-- unArr = \ z -> ((toFin ^^^ id) . index . unpack) z
-- unArr = \ z -> index (unpack z) . toFin
-- unArr = \ (Arr xs) -> index xs . toFin

-- toFlat :: HasFlat f => f a -> Flat f a
-- toFlat = \ xs -> Flat (tabulate (index xs . unFin))

#endif

-- -- reindexFin :: q
-- reindexFin :: f <--> g
-- reindexFin = reindex fin

-- reindex :: (Representable f, Representable g) => (Rep g <-> Rep f) -> (f <--> g)
-- reindex h = inv repIso . dom h . repIso


{--------------------------------------------------------------------
    Try "flattened functors" instead
--------------------------------------------------------------------}

type KnownFlat f = KnownCard (Rep f)

type HasFlat f = (Representable f, KnownFlat f, HasFin (Rep f))

#if 1

type Flat f = Arr (Rep f)

flat :: HasFlat f => f <--> Flat f
flat = reindex id
-- flat = inv repIso . repIso

toFlat :: HasFlat f => f a -> Flat f a
-- toFlat = isoFwd flat
-- toFlat = tabulate . index
-- toFlat = pack . tabulate . dom unFin . index
toFlat xs = Arr (tabulate (index xs . unFin))

unFlat :: HasFlat f => Flat f a -> f a
-- unFlat = isoRev flat
-- unFlat = isoFwd (inv repIso . repIso)
-- unFlat = tabulate . index
-- unFlat = tabulate . dom toFin . index . unpack
unFlat (Arr xs) = tabulate (index xs . toFin)

#else

newtype Flat f a = Flat (VC (Rep f) a)

instance Newtype (Flat f a) where
  type O (Flat f a) = VC (Rep f) a
  pack v = Flat v
  unpack (Flat v) = v

instance R.HasRep (Flat f a) where
  type Rep (Flat f a) = O (Flat f a)
  abst = pack
  repr = unpack

-- type HasFlat f = (KnownCard (Rep f), HasFin (Rep f))
-- type HasFlat f = HasFin' (Rep f)

-- type HasFin' a = (KnownCard a, HasFin a)
-- type HasFlat f = HasFin' (Rep f)
-- type KnownCard a = KnownNat (Card a)

deriving instance Functor (Flat f)
deriving instance HasFlat f => Applicative (Flat f)

instance HasFlat f => Distributive (Flat f) where
  distribute :: Functor g => g (Flat f a) -> Flat f (g a)
  distribute = distributeRep
  {-# INLINE distribute #-}

instance HasFlat f => Representable (Flat f) where
  type Rep (Flat f) = Rep f
  tabulate :: (Rep f -> b) -> Flat f b
  tabulate h = pack (tabulate (h . unFin))
  index :: Flat f b -> (Rep f -> b)
  Flat v `index` a = v `index` toFin a
  {-# INLINE tabulate #-}
  {-# INLINE index #-}

#if 0

-- (!) :: HasFlat f => Flat f b -> (Rep f -> b)
-- (!) = index
-- {-# INLINE (!) #-}

#endif

#if 0

-- Or maybe Flat (f :*: g) c -> (Flat f :*: Flat g) c
flatSplitProd :: KnownCard2 f g => Flat (f :*: g) c -> Flat f c :* Flat g c
flatSplitProd = (pack *** pack) . vecSplitSum . unpack
{-# INLINE flatSplitSum #-}

flatSplitProd :: KnownCard2 a b => Flat (a :*: b) c -> Flat a (Flat b c)
flatSplitProd = pack . fmap pack . vecSplitProd . unpack
{-# INLINE flatSplitProd #-}

#endif

flatIso :: HasFlat f => f a <-> Flat f a
flatIso = inv newIso . inv repIso . dom (inv fin) . repIso

unflatIso :: HasFlat f => Flat f a <-> f a
unflatIso = inv repIso . dom fin . repIso . newIso

unflatIso' :: HasFlat f => Flat f a <-> f a
unflatIso' = inv flatIso

-- In the paper, maybe use the shorter names "repIso" and "newIso".

toFlat :: HasFlat f => f a -> Flat f a
toFlat = \ xs -> Flat (tabulate (index xs . unFin))

-- toFlat xs = Flat (tabulate (dom unFin (index xs)))
-- toFlat = Flat . tabulate . dom unFin . index
-- toFlat = isoFwd flatIso

unFlat :: HasFlat f => Flat f a -> f a
unFlat = isoRev flatIso
-- unFlat = tabulate . dom toFin . index . unpack
-- unFlat = \ xs -> Flat (tabulate (index xs . unFin))


#endif

#if 0

i1 :: Representable f => f a <-> (Rep f -> a)
i1 = repIso

i2 :: HasFin (Rep f) => (Rep f -> a) <-> (Finite (Card (Rep f)) -> a)
i2 = dom (inv fin)

i3 :: KnownNat n => (Finite n -> a) <-> Vector n a
i3 = inv i1

i3' :: KnownNat (Card (Rep f))
    => (Finite (Card (Rep f)) -> a) <-> VC (Rep f) a
i3' = inv i1

i4 :: VC (Rep f) a <-> Flat f a
i4 = inv hasrepIso

-- i5 :: (KnownFlat f) => f a <-> Flat f a
-- i5 = i4 . i3 . i2 . i1

-- ii = i4 . i3 . undefined -- . i2 . i1

-- (Finite (Card (Rep f)) -> a)

-- type FinFlat f = HasFin

#endif

-- | Reverse the order of a @Representable@.
reverseF :: forall f a. (Representable f, HasFin' (Rep f)) => f a -> f a
reverseF = isoFwd (reindex reverseFinIso)
{-# INLINE reverseF #-}

reverseFinite :: forall n. KnownNat n => Finite n -> Finite n
reverseFinite i = finite (nat @n - 1) - i
{-# INLINE reverseFinite #-}

reverseFin :: forall a. HasFin' a => a -> a
reverseFin = unFin . reverseFinite . toFin
{-# INLINE reverseFin #-}

reverseFinIso :: HasFin' a => a <-> a
reverseFinIso = involution reverseFin
{-# INLINE reverseFinIso #-}

