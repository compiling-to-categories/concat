{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Synchronous stream transformers as Mealy machines

module ConCat.Synchronous where

import Prelude hiding (id,(.),curry,uncurry,const,scanl)
import Data.Function (fix)
import Data.Tuple (swap)

import ConCat.Misc ((:*))
import ConCat.Category

-- | Mealy stream transformer represented as Mealy machine.
data Mealy a b = forall s. Mealy (a :* s -> b :* s) s

-- TODO: generalize from (->) to other categories

-- | Semantic function
sapply :: Mealy a b -> [a] -> [b]
sapply (Mealy h s0) = go s0
  where
    go _ []     = []
    go s (a:as) = b:bs
      where (b,s') = h (a,s)
            bs     = go s' as

arr :: (a -> b) -> Mealy a b
arr f = Mealy (first f) ()

instance Category Mealy where
  id = arr id
  Mealy g t0 . Mealy f s0 = Mealy h (s0,t0)
   where
     h (a,(s,t)) = (c,(s',t'))
      where
        (b,s') = f (a,s)
        (c,t') = g (b,t)
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance ProductCat Mealy where
  exl = arr exl
  exr = arr exr
  Mealy f s0 &&& Mealy g t0 = Mealy h (s0,t0)
   where
     h (a,(s,t)) = ((c,d),(s',t'))
      where
        (c,s') = f (a,s)
        (d,t') = g (a,t)
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

instance CoproductCat Mealy where
  inl = arr inl
  inr = arr inr
  Mealy f s0 ||| Mealy g t0 = Mealy h (s0,t0)
   where
     h (Left  a,(s,t)) = (c,(s',t)) where (c,s') = f (a,s)
     h (Right b,(s,t)) = (c,(s,t')) where (c,t') = g (b,t)
  {-# INLINE inl #-}
  {-# INLINE inr #-}
  {-# INLINE (|||) #-}

instance ConstCat Mealy b where const b = arr (const b)

instance BoolCat Mealy where
  notC = arr notC
  andC = arr andC
  orC  = arr orC
  xorC = arr xorC

instance Eq a => EqCat Mealy a where
  equal    = arr equal
  notEqual = arr notEqual

instance Ord a => OrdCat Mealy a where
  lessThan           = arr lessThan
  greaterThan        = arr greaterThan
  lessThanOrEqual    = arr lessThanOrEqual
  greaterThanOrEqual = arr greaterThanOrEqual

instance Enum a => EnumCat Mealy a where
  succC = arr succC
  predC = arr predC

instance Num a => NumCat Mealy a where
  negateC = arr negateC
  addC    = arr addC
  subC    = arr subC
  mulC    = arr mulC
  powIC   = arr powIC

instance Fractional a => FractionalCat Mealy a where
  recipC  = arr recipC
  divideC = arr divideC

instance Floating a => FloatingCat Mealy a where
  expC = arr expC
  cosC = arr cosC
  sinC = arr sinC

instance RealFracCat (->) a b => RealFracCat Mealy a b where
  floorC   = arr floorC
  ceilingC = arr ceilingC

instance BottomCat (->) a b => BottomCat Mealy a b where
  bottomC = arr bottomC

instance IfCat Mealy a where
  ifC = arr ifC

-- instance (HasRep a, r ~ Rep a) => RepCat Mealy a r where
--   reprC = arr reprC
--   abstC = arr abstC

instance RepCat (->) a r => RepCat Mealy a r where
  reprC = arr reprC
  abstC = arr abstC

--     • Illegal instance declaration for ‘RepCat Mealy a r’
--         The coverage condition fails in class ‘RepCat’
--           for functional dependency: ‘a -> r’
--         Reason: lhs type ‘a’ does not determine rhs type ‘r’
--         Un-determined variable: r
--         Using UndecidableInstances might help

{--------------------------------------------------------------------
    Other operations
--------------------------------------------------------------------}

delay :: a -> Mealy a a
delay = Mealy swap

scanl :: (b -> a -> b) -> b -> Mealy a b
scanl op = Mealy (\ (a,b) -> dup (b `op` a))
{-# INLINE scanl #-}

scan :: Monoid m => Mealy m m
scan = scanl mappend mempty

{--------------------------------------------------------------------
    
--------------------------------------------------------------------}

type Stream = []  -- infinite-only. To do: use real streams.

newtype StreamX a b = StreamX (Stream a -> Stream b)

fixSX :: StreamX (a :* b) b -> StreamX a b
fixSX (StreamX h) = StreamX (\ as -> fix (\ bs -> h (as `zip` bs)))
-- fixSX (StreamX h) = StreamX (\ as -> let bs = h (as `zip` bs) in bs)

-- fixMealy :: forall a b. Mealy (a :* b) b -> Mealy a b
-- fixMealy (Mealy h s0) = Mealy (k t0)
--  where
--    ...

-- h :: (a :* b) :* s -> b :* s
--   =~ a -> (b :* s -> b :* s)

-- k :: a :* s -> b :* s
   



{--------------------------------------------------------------------
    Examples
--------------------------------------------------------------------}

fibL2 :: Num a => [a]
fibL2 = 0 : 1 : zipWith (+) fibL2 (tail fibL2)

fibL3 :: Num a => [a]
fibL3 = 0 : zipWith (+) (1 : fibL3) fibL3
