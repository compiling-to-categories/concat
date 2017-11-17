{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | Synchronous stream transformers as Mealy machines

module ConCat.Synchronous where

import Prelude hiding (id,(.),curry,uncurry,const,scanl)
import Data.Function (fix)
import Data.Tuple (swap)

import ConCat.Misc ((:*))
import ConCat.Category

-- | Synchronous stream transformer represented as Mealy machine.
data Mealy con a b = forall s. con s => Mealy (a :* s -> b :* s) s

-- TODO: generalize from (->) to other categories

-- | Semantic function
sapply :: Mealy con a b -> [a] -> [b]
sapply (Mealy h s0) = go s0
  where
    go _ []     = []
    go s (a:as) = b:bs
      where (b,s') = h (a,s)
            bs     = go s' as

type CartCon con = (con (), OpCon (:*) (Sat con))

arr :: con () => (a -> b) -> Mealy con a b
arr f = Mealy (first f) ()

-- State transition function
type X s a b = a :* s -> b :* s

-- Combine Mealy machines
op2 :: forall con a b c d e f. CartCon con
    => (forall s t. (con s, con t) => X s a b -> X t c d -> X (s :* t) e f) 
    -> (Mealy con a b -> Mealy con c d -> Mealy con  e f) 
op2 op (Mealy (f :: a :* s -> b :* s) s0) (Mealy (g :: c :* t -> d :* t) t0) =
  Mealy (f `op` g) (s0,t0) <+ inOp @(:*) @(Sat con) @s @t

instance CartCon con => Category (Mealy con) where
  id = arr id
  (.) = op2 (.@)
   where
     (g .@ f) (a,(t,s)) = (c,(t',s'))
      where
        (b,s') = f (a,s)
        (c,t') = g (b,t)
  {-# INLINE id #-}
  {-# INLINE (.) #-}

instance CartCon con => ProductCat (Mealy con) where
  exl = arr exl
  exr = arr exr
  (&&&) = op2 (&&&@)
   where
     (f &&&@ g) (a,(s,t)) = ((c,d),(s',t'))
      where
        (c,s') = f (a,s)
        (d,t') = g (a,t)
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE (&&&) #-}

instance CartCon con => CoproductCat (Mealy con) where
  inl = arr inl
  inr = arr inr
  (|||) = op2 (|||@)
   where
     (f |||@ _) (Left  a,(s,t)) = (c,(s',t)) where (c,s') = f (a,s)
     (_ |||@ g) (Right b,(s,t)) = (c,(s,t')) where (c,t') = g (b,t)
  {-# INLINE inl #-}
  {-# INLINE inr #-}
  {-# INLINE (|||) #-}

instance CartCon con => ConstCat (Mealy con) b where const b = arr (const b)

instance CartCon con => BoolCat (Mealy con) where
  notC = arr notC
  andC = arr andC
  orC  = arr orC
  xorC = arr xorC

instance (CartCon con, Eq a) => EqCat (Mealy con) a where
  equal    = arr equal
  notEqual = arr notEqual

instance (CartCon con, Ord a) => OrdCat (Mealy con) a where
  lessThan           = arr lessThan
  greaterThan        = arr greaterThan
  lessThanOrEqual    = arr lessThanOrEqual
  greaterThanOrEqual = arr greaterThanOrEqual

instance (CartCon con, Enum a) => EnumCat (Mealy con) a where
  succC = arr succC
  predC = arr predC

instance (CartCon con, Num a) => NumCat (Mealy con) a where
  negateC = arr negateC
  addC    = arr addC
  subC    = arr subC
  mulC    = arr mulC
  powIC   = arr powIC

instance (CartCon con, Fractional a) => FractionalCat (Mealy con) a where
  recipC  = arr recipC
  divideC = arr divideC

instance (CartCon con, Floating a) => FloatingCat (Mealy con) a where
  expC = arr expC
  logC = arr logC
  cosC = arr cosC
  sinC = arr sinC

instance (CartCon con, RealFracCat (->) a b) => RealFracCat (Mealy con) a b where
  floorC    = arr floorC
  ceilingC  = arr ceilingC
  truncateC = arr truncateC

instance (CartCon con, BottomCat (->) a b) => BottomCat (Mealy con) a b where
  bottomC = arr bottomC

instance CartCon con => IfCat (Mealy con) a where
  ifC = arr ifC

-- instance (HasRep a, r ~ Rep a) => (CartCon con, RepCat (Mealy con) a r where
--   reprC = arr reprC
--   abstC = arr abstC

instance (CartCon con, RepCat (->) a r) => RepCat (Mealy con) a r where
  reprC = arr reprC
  abstC = arr abstC

--     • Illegal instance declaration for ‘RepCat (Mealy con) a r’
--         The coverage condition fails in class ‘RepCat’
--           for functional dependency: ‘a -> r’
--         Reason: lhs type ‘a’ does not determine rhs type ‘r’
--         Un-determined variable: r
--         Using UndecidableInstances might help

{--------------------------------------------------------------------
    Other operations
--------------------------------------------------------------------}

delay :: con a => a -> Mealy con a a
delay = Mealy swap

scanl :: con b => (b -> a -> b) -> b -> Mealy con a b
scanl op = Mealy (\ (a,b) -> dup (b `op` a))
{-# INLINE scanl #-}

scan :: (Monoid m, con m) => Mealy con m m
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
