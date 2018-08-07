{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}

-- | Orphan instances to be moved into other libraries
--
-- <https://github.com/ekmett/pointed/issues/18>

module ConCat.Orphans where

import Prelude hiding (zipWith)
-- import Control.Applicative (liftA2)
import Control.Arrow ((|||))
import Data.Monoid
import GHC.Generics (U1(..),Par1(..),(:+:)(..),(:*:)(..),(:.:)(..))
-- import Data.Foldable 

import Data.Void
import Data.Key
import Data.Pointed
-- import Data.Copointed
-- import Control.Comonad.Cofree
#if  !MIN_VERSION_vector_sized(1,0,1)
import Data.Distributive (Distributive(..))
import Data.Functor.Rep (Representable(..),distributeRep)
#endif
-- import qualified Data.Functor.Rep as Rep

-- import Data.Stream (Stream(..))
import Control.Newtype.Generics
import Text.PrettyPrint.HughesPJClass hiding ((<>))
import GHC.TypeLits (KnownNat)
import Data.Finite (Finite,finite,finites)
import Data.Vector.Sized (Vector)
import qualified Data.Vector.Sized as V

import ConCat.Misc ((:*),(:+),inNew2) -- ,inNew

#if 0
-- In keys-3.12 (2018-01-28)

{--------------------------------------------------------------------
    GHC.Generics and keys
-------------------------------------------------------------------
-}

-- Key

type instance Key U1 = Void
type instance Key Par1 = ()
type instance Key (g :.: f) = (Key g , Key f)
type instance Key (f :*: g) = Either (Key f) (Key g)

-- Keyed

instance Keyed U1 where
  mapWithKey _ U1 = U1
  {-# INLINE mapWithKey #-}

instance Keyed Par1 where
  mapWithKey q = fmap (q ())
  {-# INLINE mapWithKey #-}

instance (Keyed g, Keyed f) => Keyed (f :*: g) where
  mapWithKey q (fa :*: ga) = mapWithKey (q . Left) fa :*: mapWithKey (q . Right) ga
  {-# INLINE mapWithKey #-}

instance (Keyed g, Keyed f) => Keyed (g :.: f) where
  mapWithKey q = inNew (mapWithKey (mapWithKey . fmap q . (,)))
  {-# INLINE mapWithKey #-}

#if 0
mapWithKey :: (Key (g :.: f) -> a -> b) -> (g :.: f) a -> (g :.: f) b
           :: ((Key g, Key f) -> a -> b) -> (g :.: f) a -> (g :.: f) b

mapWithKey q
  = \ (Comp1 gfa) -> Comp1 (mapWithKey (\ gk -> mapWithKey (\ fk a -> q (gk, fk) a)) gfa)
  = inNew $ mapWithKey (\ gk -> mapWithKey (\ fk a -> q (gk, fk) a))
  = inNew $ mapWithKey (\ gk -> mapWithKey (\ fk -> q (gk, fk)))
  = inNew $ mapWithKey (\ gk -> mapWithKey (q . (gk,)))
  = inNew $ mapWithKey (\ gk -> mapWithKey . (q .) $ (gk,))
  = inNew $ mapWithKey (\ gk -> mapWithKey . (q .) $ (,) gk)
  = inNew (mapWithKey (mapWithKey . fmap q . (,)))

q   :: ((Key g, Key f) -> a -> b)
gfa :: g (f a)
gk  :: Key g
fk  :: Key f
#endif

-- Zip

instance Zip U1 where
  zipWith = liftA2
  {-# INLINE zipWith #-}

instance Zip Par1 where
  zipWith = liftA2
  {-# INLINE zipWith #-}

instance (Zip f, Zip g) => Zip (f :*: g) where
  zipWith h (fa :*: ga) (fa' :*: ga') =
    zipWith h fa fa' :*: zipWith h ga ga'
  {-# INLINE zipWith #-}

instance (Zip f, Zip g) => Zip (g :.: f) where
  zipWith = inNew2 . zipWith . zipWith
  {-# INLINE zipWith #-}


-- ZipWithKey

instance ZipWithKey U1

instance ZipWithKey Par1

instance (Keyed g, Zip g, Keyed f, Zip f) => ZipWithKey (f :*: g)

instance (Keyed g, Zip g, Keyed f, Zip f) => ZipWithKey (g :.: f)


-- Indexable

instance Indexable U1 where index U1 = \ case

instance Indexable Par1 where index (Par1 a) () = a

instance (Indexable g, Indexable f) =>
         Indexable (f :*: g) where
  index (fa :*: _) (Left  fk) = fa ! fk
  index (_ :*: ga) (Right gk) = ga ! gk
  {-# INLINE index #-}

instance (Indexable g, Indexable f) =>
         Indexable (g :.: f) where
  index (Comp1 gfa) (gk,fk) = gfa ! gk ! fk
  {-# INLINE index #-}


-- Lookup

instance Lookup U1 where lookup = lookupDefault

instance Lookup Par1 where lookup = lookupDefault

instance (Indexable g, Indexable f) => Lookup (f :*: g) where
  lookup = lookupDefault

instance (Indexable g, Indexable f) => Lookup (g :.: f) where
  lookup = lookupDefault


-- Adjustable

instance Adjustable U1 where
  adjust = const (const id)
  {-# INLINE adjust #-}

instance Adjustable Par1 where
  adjust h () = fmap h
  {-# INLINE adjust #-}

instance (Adjustable g, Adjustable f) => Adjustable (f :*: g) where
  adjust h (Left  fk) (fa :*: ga) = adjust h fk fa :*: ga
  adjust h (Right gk) (fa :*: ga) = fa :*: adjust h gk ga
  {-# INLINE adjust #-}

instance (Adjustable g, Adjustable f) => Adjustable (g :.: f) where
  adjust h (gk,fk) = inNew (adjust (adjust h fk) gk)
  {-# INLINE adjust #-}

#endif

#if 0
-- No longer needed with pointed-5.0.1 (2018-01-22)

{--------------------------------------------------------------------
    GHC.Generics and pointed
-------------------------------------------------------------------
-}

instance Pointed U1 where
  point = const U1
  {-# INLINE point #-}

instance Pointed Par1 where
  point = Par1
  {-# INLINE point #-}

instance (Pointed f, Pointed g) => Pointed (f :*: g) where
  point a = point a :*: point a
  {-# INLINE point #-}

instance (Pointed f, Pointed g) => Pointed (g :.: f) where
  point = Comp1 . point . point
  {-# INLINE point #-}

instance Copointed Par1 where
  copoint = unPar1
  {-# INLINE copoint #-}

instance (Copointed f, Copointed g) => Copointed (g :.: f) where
  copoint = copoint . copoint . unComp1
  {-# INLINE copoint #-}

-- TODO: many Pointed and Copointed instances for GHC.Generics types.
-- Offer as a pointed patch, as I did with keys.

instance Pointed f => Pointed (Cofree f) where
  point a = z where z = a :< point z

instance Copointed (Cofree f) where
  copoint (a :< _) = a

#endif

{--------------------------------------------------------------------
    Control.Newtype and keys
-------------------------------------------------------------------
-}

instance Newtype (Par1 t) where
  type O (Par1 t) = t
  pack = Par1
  unpack = unPar1

instance Newtype ((a :*: b) t) where
  type O ((a :*: b) t) = a t :* b t
  pack (a,b) = a :*: b
  unpack (a :*: b) = (a,b)

instance Newtype ((a :+: b) t) where
  type O ((a :+: b) t) = a t :+ b t
  pack = either L1 R1
  unpack = eitherF Left Right

instance Newtype ((a :.: b) t) where
  type O ((a :.: b) t) = a (b t)
  pack = Comp1
  unpack = unComp1

fstF :: (a :*: b) t -> a t
fstF (a :*: _) = a

sndF :: (a :*: b) t -> b t
sndF (_ :*: b) = b

eitherF :: (a t -> c) -> (b t -> c) -> ((a :+: b) t -> c)
eitherF f _ (L1 a) = f a
eitherF _ g (R1 b) = g b

#if 0
{--------------------------------------------------------------------
    Data.Stream
-------------------------------------------------------------------
-}

instance Pointed Stream where point   = pure
instance Zip     Stream where zipWith = liftA2
-- etc

instance Foldable Stream where
  foldMap f ~(Cons a as) = f a `mappend` foldMap f as
#endif

{--------------------------------------------------------------------
    Pretty
-------------------------------------------------------------------
-}

instance Pretty (U1 a) where
  pPrintPrec _ _ U1 = text "U1"

instance Pretty a => Pretty (Par1 a) where
  pPrintPrec l p (Par1 a) = app l p "Par1" a

instance (Pretty (f a), Pretty (g a)) => Pretty ((f :*: g) a) where
  pPrintPrec l p (fa :*: ga) =
    maybeParens (p > 6) $
     sep [pPrintPrec l 7 fa <+> text ":*:", pPrintPrec l 6 ga]

instance Pretty (g (f a)) => Pretty ((g :.: f) a) where
  pPrintPrec l p (Comp1 gfa) = app l p "Comp1" gfa

app :: Pretty a => PrettyLevel -> Rational -> String -> a -> Doc
app l p str a =
  maybeParens (p > appPrec) $
   text str <+> pPrintPrec l (appPrec+1) a

appPrec :: Rational
appPrec = 10

{--------------------------------------------------------------------
    Distributive
-------------------------------------------------------------------
-}

#if 0

-- In adjunctions-4.4

{--------------------------------------------------------------------
    Representable
-------------------------------------------------------------------
-}

instance Representable U1 where
  type Rep U1 = Void
  tabulate _ = U1
  index U1 = absurd

instance Representable Par1 where
  type Rep Par1 = ()
  tabulate h = Par1 (h ())
  index (Par1 a) () = a

instance (Representable f, Representable g) => Representable (f :*: g) where
  type Rep (f :*: g) = Rep f :+ Rep g
  tabulate h = tabulate (h . Left) :*: tabulate (h . Right)
  index (fa :*: ga) = Rep.index fa `either` Rep.index ga

instance (Representable g, Representable f) => Representable (g :.: f) where
  type Rep (g :.: f) = Rep g :* Rep f
  tabulate :: (Rep g :* Rep f -> a) -> (g :.: f) a
  tabulate h = Comp1 (tabulate <$> tabulate (curry h))
  index (Comp1 gfa) (i,j) = Rep.index (Rep.index gfa i) j

--                                     h   :: Rep g :* Rep f -> a
--                               curry h   :: Rep g -> Rep f -> a
--                     tabulate (curry h)  :: g (Rep f -> a)
--        tabulate <$> tabulate (curry h)  :: g (f a)
-- Comp1 (tabulate <$> tabulate (curry h)) :: (g :.: f) a

#endif

{--------------------------------------------------------------------
    Monoids
-------------------------------------------------------------------
-}

-- instance Zip Sum where zipWith f (Sum a) (Sum b) = Sum (f a b)
-- instance Zip Product where zipWith f (Product a) (Product b) = Product (f a b)

instance Zip Sum     where zipWith = inNew2
instance Zip Product where zipWith = inNew2


{--------------------------------------------------------------------
    Vector (Sized)
-------------------------------------------------------------------
-}

type instance Key (Vector n) = Finite n

-- mapWithKey :: (Key f -> a -> b) -> f a -> f b
-- imap :: (Int -> a -> b) -> Vector n a -> Vector n b

imap' :: KnownNat n => (Finite n -> a -> b) -> Vector n a -> Vector n b
imap' f = V.imap (f . finite . fromIntegral)
{-# INLINE imap' #-}

-- I've requested that something like imap' be added to vector-sized, preferably
-- eliminating the error condition. See
-- <https://github.com/expipiplus1/vector-sized/issues/26>

instance KnownNat n => Keyed (Vector n) where
  mapWithKey = imap'
  {-# INLINE mapWithKey #-}

instance KnownNat n => Zip (Vector n) where
  zip = V.zip
  zipWith = V.zipWith
  {-# INLINE zip #-}
  {-# INLINE zipWith #-}


#if !MIN_VERSION_vector_sized(1,0,1)
instance KnownNat n => Distributive (Vector n) where
  distribute :: Functor f => f (Vector n a) -> Vector n (f a)
  distribute = distributeRep
  {-# INLINE distribute #-}

instance KnownNat n => Representable (Vector n) where
  type Rep (Vector n) = Finite n
  tabulate = V.generate
  index = V.index
  {-# INLINE tabulate #-}
  {-# INLINE index #-}
#endif

instance KnownNat n => Pointed (Vector n) where
#if 1
  point = V.replicate
  {-# INLINE {-[0]-} point #-}
#else
  point = pointV
  {-# INLINE point #-}

pointV :: KnownNat n => a -> Vector n a
pointV = V.replicate
{-# INLINE [0] pointV #-}
#endif

{--------------------------------------------------------------------
    Foldable for functions
--------------------------------------------------------------------}

instance Foldable ((->) Void) where
  foldMap _ _ = mempty
  {-# INLINE foldMap #-}

instance Foldable ((->) ()) where
  foldMap h as = h (as ())
  {-# INLINE foldMap #-}

instance Foldable ((->) Bool) where
  foldMap h as = h (as False) <> h (as True)
  {-# INLINE foldMap #-}

instance (Foldable ((->) m), Foldable ((->) n)) => Foldable ((->) (m :+ n)) where
  foldMap h as = foldMap h (as . Left) <> foldMap h (as . Right)
  {-# INLINE foldMap #-}

instance (Foldable ((->) m), Foldable ((->) n)) => Foldable ((->) (m :* n)) where
  -- foldMap h as = (foldMap.foldMap) h (curry as)
  foldMap h = foldMap h . Comp1 . curry
  -- fold as = foldMap fold (curry as)  -- experiment
  -- fold as = fold (fmap fold (curry as))  -- experiment
  -- fold as = fold (fold . curry as)  -- experiment
  {-# INLINE foldMap #-}

instance KnownNat n => Foldable ((->) (Finite n)) where
  foldMap h as = foldMap h (as <$> finites @n)
  {-# INLINE foldMap #-}

sumToMaybe :: () :+ a -> Maybe a
sumToMaybe = const Nothing ||| Just

maybeToSum :: Maybe a -> () :+ a
maybeToSum = maybe (Left ()) Right

instance Foldable ((->) a) => Foldable ((->) (Maybe a)) where
  foldMap h as = foldMap h (as . sumToMaybe)
