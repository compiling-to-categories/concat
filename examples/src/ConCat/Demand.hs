{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators, GADTs, KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, MultiParamTypeClasses #-} -- for Functor instance
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Demand
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Demand algebra
----------------------------------------------------------------------

-- TODO: Use Dual?

module ConCat.Demand {- (Demand(..),demand,(:-?)(..)) -} where

import Prelude hiding (id,(.),curry,uncurry,const)
import qualified Prelude as P

import Control.Applicative (liftA2)

import Control.Newtype.Generics (Newtype(..))

import ConCat.Misc ((:*),(:+),Unop,inNew,inNew2)
import ConCat.Category

-- | Demand pattern
data Demand :: * -> * where
  NoneD  :: Demand a
  (:***) :: Demand a -> Demand b -> Demand (a :* b)
  (:+++) :: Demand a -> Demand b -> Demand (a :+ b)
  (:~>)  :: Demand a -> Demand b -> Demand (a -> b)
  AllD   :: Demand a

deriving instance Show (Demand a)

{--------------------------------------------------------------------
    Semantics
--------------------------------------------------------------------}

-- | Semantic function. Extract just the demanded information.
demand :: Demand a -> Unop a
demand NoneD        = nothing
demand (ra :*** rb) = demand ra *** demand rb
demand (ra :+++ rb) = demand ra +++ demand rb
demand (ra :~>  rb) = demand ra ~>  demand rb
demand AllD         = id

nothing :: Unop a
nothing = P.const (error "empty demand pulled")

-- I'm uneasy about handling of functions. Does demand ra need to be inverted?

-- | Alternative Semantic function. Splits into needed info and complement.
split :: Demand a -> (Unop a,Unop a)
split NoneD        = (nothing,id)
split (ra :*** rb) = lift2Split (***) ra rb
split (ra :+++ rb) = lift2Split (+++) ra rb
split (ra :~>  rb) = lift2Split (~>)  ra rb
split AllD         = (id,nothing)

-- Alternative definition
_split :: Demand a -> (Unop a,Unop a)
_split = demand &&& demand . complementD

lift2Split :: (Unop a -> Unop b -> c) -> Demand a -> Demand b -> (c, c)
lift2Split (@@) ra rb = (pa @@ pb, qa @@ qb)
  where
    (pa,qa) = split ra
    (pb,qb) = split rb

-- | Complement of Demand
complementD :: Unop (Demand a)
complementD NoneD        = AllD
complementD (ra :*** rb) = complementD ra *: complementD rb
complementD (ra :+++ rb) = complementD ra +: complementD rb
complementD (ra :~> rb)  = complementD ra >: complementD rb
complementD AllD         = NoneD

{--------------------------------------------------------------------
    Smart constructors
--------------------------------------------------------------------}

-- | Product demand
(*:) :: Demand a -> Demand b -> Demand (a :* b)
(*:) = combineD (:***)

-- | Sum demand
(+:) :: Demand a -> Demand b -> Demand (a :+ b)
(+:) = combineD (:+++)

-- | Function demand
(>:) :: Demand a -> Demand b -> Demand (a -> b)
(>:) = combineD (:~>)

-- | Building block for smart constructor, assuming that @NoneD `op` NoneD ==
-- NoneD@ and @AllD `op` AllD == AllD@.
combineD :: Unop (Demand a -> Demand b -> Demand (a `op` b))
combineD  _   NoneD NoneD = NoneD
combineD  _   AllD  AllD  = AllD
combineD (@@) ra    rb    = ra @@ rb

{--------------------------------------------------------------------
    Construction & destruction
--------------------------------------------------------------------}

pairD :: (Demand a :* Demand b) -> Demand (a :* b)
pairD = uncurry (*:)

unpairD :: Demand (a :* b) -> (Demand a :* Demand b)
unpairD NoneD        = (NoneD,NoneD)
unpairD (ra :*** rb) = (ra   ,rb   )
unpairD AllD         = (AllD ,AllD )

inUnpairD :: (Demand a' :* Demand b' -> Demand a :* Demand b)
          -> Demand (a' :* b') -> Demand (a :* b)
inUnpairD = unpairD ~> pairD


plusD :: (Demand a, Demand b) -> Demand (a :+ b)
plusD = uncurry (+:)

unplusD :: Demand (a :+ b) -> (Demand a , Demand b)
unplusD NoneD        = (NoneD, NoneD)
unplusD (ra :+++ rb) = (ra   , rb   )
unplusD AllD         = (AllD , AllD )

inUnplusD :: (Demand a' :* Demand b' -> Demand a :* Demand b)
          -> Demand (a' :+ b') -> Demand (a :+ b)
inUnplusD = unplusD ~> plusD

funD :: (Demand a, Demand b) -> Demand (a -> b)
funD = uncurry (>:)

unfunD :: Demand (a -> b) -> (Demand a, Demand b)
unfunD NoneD       = (NoneD,NoneD)
unfunD (ra :~> rb) = (ra, rb)
unfunD AllD        = (AllD,AllD)

inUnfunD :: ((Demand a, Demand b) -> (Demand a', Demand b'))
         -> (Demand (a -> b) -> Demand (a' -> b'))
inUnfunD = unfunD ~> funD

mergeD :: Demand (a :* a) -> Demand a
mergeD = uncurry lubD . unpairD

-- mergeD NoneD        = NoneD
-- mergeD (ra :*** rb) = ra `lubD` rb
-- mergeD AllD         = AllD

{--------------------------------------------------------------------
    Lattice
--------------------------------------------------------------------}

-- Demands form a lattice with bottom = NoneD, top = AllD, and lub & glb as
-- follows. The semantic function preserves lattice structure (is a lattice
-- morphism).

-- | Least upper bound on demands. Specification: 
-- @demand (ra `lubD` rb) == demand ra `lub` demand rb@.
lubD :: Demand a -> Demand a -> Demand a
NoneD      `lubD` a            = a
a          `lubD` NoneD        = a
AllD       `lubD` _            = AllD
_          `lubD` AllD         = AllD
(a :*** b) `lubD` (a' :*** b') = (a `lubD` a') *: (b `lubD` b')
(a :+++ b) `lubD` (a' :+++ b') = (a `lubD` a') +: (b `lubD` b')
(a :~>  b) `lubD` (a' :~>  b') = (a `lubD` a') >: (b `lubD` b')

-- | Greatest lower bound on demands. Specification: 
-- @demand (ra `glbD` rb) == demand ra `glb` demand rb@.
glbD :: Demand a -> Demand a -> Demand a
NoneD      `glbD` _            = NoneD
_          `glbD` NoneD        = NoneD
AllD       `glbD` b            = b
a          `glbD` AllD         = a
(a :*** b) `glbD` (a' :*** b') = (a `glbD` a') *: (b `glbD` b')
(a :+++ b) `glbD` (a' :+++ b') = (a `glbD` a') +: (b `glbD` b')
(a :~>  b) `glbD` (a' :~>  b') = (a `glbD` a') >: (b `glbD` b')

-- The catch-all cases in lubD and glbD are sum/product.
-- Impossible, but GHC doesn't realize. :(

{--------------------------------------------------------------------
    Demand flow arrow
--------------------------------------------------------------------}

infixr 1 :-?

-- | Demand flow category, running counter to value flow
newtype a :-? b = RX (Demand b -> Demand a)

instance Newtype (a :-? b) where
  type O (a :-? b) = Demand b -> Demand a
  pack = RX
  unpack (RX f) = f

instance Category (:-?) where
  id  = pack id
  (.) = inNew2 (flip (.))                -- note flow reversal

instance MonoidalPCat (:-?) where
  (***) = inNew2 $ \ f g -> inUnpairD (f *** g)
  {-# INLINE (***) #-}

instance BraidedPCat (:-?) where

instance ProductCat (:-?) where
  exl = pack (*: NoneD)
  exr = pack (NoneD *:)
  dup = pack mergeD
  {-# INLINE exl #-}
  {-# INLINE exr #-}
  {-# INLINE dup #-}

instance UnitCat (:-?) where

instance TerminalCat (:-?)

-- need :: Demand () `k` Demand a

instance MonoidalSCat (:-?) where
  (+++) = inNew2 $ \ f g -> inUnplusD (f *** g)
  {-# INLINE (+++) #-}

instance BraidedSCat  (:-?)

instance CoproductCat (:-?) where
  inl = pack (exl . unplusD)
  inr = pack (exr . unplusD)
  jam = pack (plusD . dup)
  -- (|||) = (inNew2.liftA2) (+:)

instance ConstCat (:-?) a where
  const _ = pack (const NoneD)

instance BottomCat (:-?) a b where
  bottomC = pack (const NoneD)

hyperStrict :: a :-? b
hyperStrict = pack f
 where
   f NoneD = NoneD
   f _     = AllD

instance BoolCat (:-?) where
  notC = pack id
  andC = hyperStrict
  orC  = hyperStrict
  xorC = hyperStrict

instance EqCat (->) a => EqCat (:-?) a where
  equal    = hyperStrict
  notEqual = hyperStrict

instance Ord a => OrdCat (:-?) a where
  lessThan           = hyperStrict
  greaterThan        = hyperStrict
  lessThanOrEqual    = hyperStrict
  greaterThanOrEqual = hyperStrict

-- instance MinMaxCat (->) a => MinMaxCat (:-?) a where
--   minC = ...
--   maxC = ...

instance EnumCat (->) a => EnumCat (:-?) a where
  succC = hyperStrict
  predC = hyperStrict

-- The following instances are too conservative for instances over non-flat
-- types, such as tuples and many applicatives.
-- 
-- TODO: rework.

instance NumCat (->) a => NumCat (:-?) a where
  negateC = hyperStrict
  addC    = hyperStrict
  subC    = hyperStrict
  mulC    = hyperStrict
  powIC   = hyperStrict

instance FractionalCat (->) a => FractionalCat (:-?) a where
  recipC  = hyperStrict
  divideC = hyperStrict

instance FloatingCat (->) a => FloatingCat (:-?) a where
  expC = hyperStrict
  cosC = hyperStrict
  sinC = hyperStrict
  logC = hyperStrict

instance RealFracCat (->) a b => RealFracCat (:-?) a b where
  floorC    = hyperStrict
  ceilingC  = hyperStrict
  truncateC = hyperStrict

instance FromIntegralCat (->) a b => FromIntegralCat (:-?) a b where
  fromIntegralC = hyperStrict

-- Still to come: IfCat, UnknownCat, RepCat, CoerceCat, 

-- Every demand function must map NoneD to NoneD, so represent a :-? b
-- as Demand b -> Maybe (Demand a), and use Kleisli composition. Or represent
-- as a Kleisli in the first place.

