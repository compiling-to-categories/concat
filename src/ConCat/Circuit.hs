{-# LANGUAGE CPP #-}

-- #define NoOptimizeCircuit
-- #define NoHashCons

-- #define NoIfBotOpt
-- #define NoIdempotence

-- -- Improves hash consing, but can obscure equivalent circuits
-- #define NoCommute

-- #define NoBusLabel

#define MealyToArrow

-- -- TODO: Make dynamic, perhaps via display attributes
-- #define ShowDepths

-- -- Whether a delay/cons element is considered further from input
-- #define ShallowDelay

-- #define NoMend

#define NoSums
-- #define StaticSums
-- #define TaggedSums
-- #define ChurchSums

{-# LANGUAGE TypeFamilies, TypeOperators, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns, TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}
{-# LANGUAGE ExistentialQuantification, TypeSynonymInstances, GADTs #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-} -- see below
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-} -- for LU & BU
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE DeriveFunctor, DeriveDataTypeable #-}
{-# LANGUAGE TypeApplications, AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}  -- GenBuses

-- TODO: trim language extensions

#ifdef ChurchSums
{-# LANGUAGE LiberalTypeSynonyms, ImpredicativeTypes, EmptyDataDecls #-}
#endif

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-orphans #-} -- for OkayArr
{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}

-- This module compiles pretty slowly. Some of my pattern matching style led to
-- the following warning:
-- 
--        Pattern match checker exceeded (2000000) iterations in
--        a case alternative. (Use -fmax-pmcheck-iterations=n
--        to set the maximun number of iterations to n)
-- 
-- I've simplified my style by replacing uses of the Eql macro by explicit
-- equality checks. To find at least some problematic definitions, lower
-- -fmax-pmcheck-iterations from default of 2000000. I'd like to simplify
-- further. Ideally, use constructor pattern matching in the rewrites, instead
-- of comparing strings.

{-# OPTIONS_GHC -fmax-pmcheck-iterations=1000000 #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Circuit
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Circuit representation
----------------------------------------------------------------------

module ConCat.Circuit
  ( CircuitM, (:>)
  , PinId(..), Width, Bus(..), Source(..)
  , GenBuses(..), GS, GST, genBusesRep', delayCRep, tyRep, bottomRep, unDelayName
  , namedC, constC -- , constS
  , SourceToBuses(..)
--   , litUnit, litBool, litInt
  -- , (|||*), fromBool, toBool
  , CompS(..), compId, compName, compIns, compOuts
  , CompId, DGraph, circuitGraph, Attr
  , UU, writeDot, displayDot, mkGraph,Name,Report,GraphInfo
  , simpleComp, tagged
  , systemSuccess
  , unitize -- , unitize'
--   , MealyC(..)
--   , mealyAsArrow
--   , unitizeMealyC
--   , Complex(..),cis
  -- For AbsTy
  , BusesM, abstB,abstC,reprC,Buses(..),Ty(..)
  ) where

import Prelude hiding (id,(.),curry,uncurry,const,sequence)

import Data.Monoid ({-mempty,-}(<>),Sum,Product,All,Any)
-- import Data.Newtypes.PrettyDouble
-- import Data.Functor ((<$>))
import Control.Applicative ({-Applicative(..),-}liftA2)
import Control.Monad (unless)
import Control.Arrow (arr,Kleisli(..))
import Data.Foldable ({-foldMap,-}toList)
import qualified GHC.Generics as G
import Data.Function (on)
import Data.Maybe (fromMaybe,isJust)
import Data.List (intercalate,group,sort,stripPrefix)
import Data.Char (isAscii)
#ifndef MealyToArrow
import Data.List (partition)
#endif
import Data.Map (Map)
import qualified Data.Map as M
-- import Data.Set (Set)
import qualified Data.Set as S
import Data.Sequence (Seq,singleton)
import Text.Printf (printf)
import Debug.Trace (trace)
-- import Data.Coerce                      -- TODO: imports
#if !defined NoHashCons
import Unsafe.Coerce -- experiment
#endif
-- import GHC.Exts (Coercible) -- ,coerce
import Data.Typeable (Typeable,eqT,cast) -- ,Proxy(..),typeRep
import Data.Type.Equality ((:~:)(..))

import qualified System.Info as SI
import System.Process (system) -- ,readProcess
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode(ExitSuccess))

-- mtl
import Control.Monad.State (State,execState,StateT)

-- For AbsTy
import qualified Data.Functor.Identity as M
import qualified Control.Monad.Trans.Reader as M
import qualified Control.Monad.Trans.Writer as M
import qualified Control.Monad.State as M

-- import TypeUnary.Vec hiding (get)

-- TODO: Eliminate most of the following, as I move data types out of circat
import ConCat.Misc ((:*),Unop,Binop,Yes1) -- 
import ConCat.Complex
import ConCat.Rep
import ConCat.Category
import qualified ConCat.AltCat as A
import ConCat.AltCat (Uncurriable(..))

import qualified ConCat.Free.LinearRow as LR
import qualified ConCat.Free.LinearCol as LC

{--------------------------------------------------------------------
    Buses
--------------------------------------------------------------------}

newtype PinId = PinId Int deriving (Eq,Ord,Show,Enum)
type PinSupply = [PinId]

-- TODO: Phase out PinSupply and CompSupply in favor of simple ints.

-- TODO: Maybe stop using the name "pin", since it's a bus.

-- undefinedPinId :: PinId
-- undefinedPinId = PinId (-1)

-- | Bus width
type Width = Int

-- Data bus: Id, type
data Bus = Bus PinId Ty

-- undefinedBus :: Width -> Bus
-- undefinedBus = Bus undefinedPinId

type Sources = [Source]

-- | An information source: its bus and a description of its construction, which
-- contains the primitive, argument sources, and which output of that
-- application (usually 0th).
data Source = Source Bus PrimName Sources Int

sourceBus :: Source -> Bus
sourceBus (Source b _ _ _) = b

busId :: Bus -> PinId
busId (Bus i _) = i

sourceId :: Source -> PinId
sourceId = busId . sourceBus

instance Eq  Bus where (==) = (==) `on` busId
instance Ord Bus where compare = compare `on` busId

instance Eq  Source where (==) = (==) `on` sourceId
instance Ord Source where compare = compare `on` sourceId

instance Show Bus where
  show (Bus (PinId i) w) =
    "B" ++ show i ++ (if w /= Bool then ":" ++ show w else "")

instance Show Source where
  show (Source b prim ins o) = printf "Source %s %s %s %d" (show b) (show prim) (show ins) o

newPinId :: CircuitM PinId
newPinId = do { (p:ps',comps) <- M.get ; M.put (ps',comps) ; return p }

newBus :: Ty -> CircuitM Bus
newBus t = -- trace "newBus" $
           flip Bus t <$> newPinId

newSource ::  Ty -> String -> Sources -> Int -> CircuitM Source
newSource t prim ins o = -- trace "newSource" $
                         (\ b -> Source b prim ins o) <$> newBus t

{--------------------------------------------------------------------
    Buses representing a given type
--------------------------------------------------------------------}

-- | Typed aggregate of buses. @'Buses' a@ carries a value of type @a@.
-- 'AbstB' is for isomorphic forms. Note: b must not have one of the standard
-- forms. If it does, we'll get a run-time error when consuming.
data Buses :: * -> * where
  UnitB    :: Buses ()
  BoolB    :: Source -> Buses Bool
  IntB     :: Source -> Buses Int
  FloatB   :: Source -> Buses Float
  DoubleB  :: Source -> Buses Double
  PairB    :: Buses a -> Buses b -> Buses (a :* b)
  FunB     :: {-Ok2 (:>) a b => -} (a :> b) -> Buses (a -> b)
  ConvertB :: (T a, T b) => Buses a -> Buses b
  -- AbstB :: Buses (Rep b) -> Buses b

-- TODO: Try Buses as a type family instead of a GADT.
-- Note that I need some operations on all buses, so I'd need a class also.

-- TODO: Can I unify AbstB and ConvertB? Do those constructors really need the
-- constraints a ~ Rep b and ConvertB a b?

#if 0

-- Currently unused.
instance Eq (Buses a) where
  UnitB      == UnitB       = True
  BoolB s    == BoolB s'    = s == s'
  IntB s     == IntB s'     = s == s'
  FloatB  s  == FloatB  s'  = s == s'
  DoubleB s  == DoubleB s'  = s == s'
  PairB a b  == PairB a' b' = a == a' && b == b'
  FunB _     == FunB _      = False             -- TODO: reconsider
  ConvertB a == ConvertB b  = case cast a of
                                Just a' -> a' == b
                                Nothing -> False
  _          == _           = False

-- If I need Eq, handle ConvertB. I'll probably have to switch to heterogeneous
-- equality, perhaps via `TestEquality` in `Data.Type.Equality`.

#endif

-- deriving instance Typeable Buses
-- deriving instance Show (Buses a)

-- Deriving would need GenBuses a.

instance Show (Buses a) where
  show UnitB        = "()"
  show (BoolB b)    = show b
  show (IntB b)     = show b
  show (FloatB  b)  = show b
  show (DoubleB b)  = show b
  show (PairB a b)  = "("++show a++","++show b++")"
  show (FunB _)     = "<function>"
                      -- "<"++show (typeRep (Proxy :: Proxy a))++">"
  show (ConvertB b) = "ConvertB ("++show b++")"
  -- show (AbstB b) = "AbstB ("++show b++")"

-- TODO: Improve to Show instance with showsPrec. Maybe Pretty instead/also.

-- Component (primitive) type
data Ty = Unit | Bool | Int | Float | Double | Pair Ty Ty deriving (Eq,Ord,Show)

genBuses :: GenBuses b => Prim a b -> Sources -> CircuitM (Buses b)
genBuses prim ins = M.evalStateT (genBuses' (primName prim) ins) 0

type BusesM = StateT Int CircuitM

class Ok (:>) a => GenBuses a where
  genBuses' :: String -> Sources -> BusesM (Buses a)
  delay :: a -> (a :> a)
  ty :: a -> Ty                         -- dummy argument

type GS a = (GenBuses a, Show a)

genBus :: (Source -> Buses a) -> Ty
       -> String -> Sources -> BusesM (Buses a)
genBus wrap t prim ins = do o <- M.get
                            src <- M.lift (newSource t prim ins o)
                            M.put (o+1)
                            return (wrap src)

instance GenBuses () where
  genBuses' _ _ = return UnitB
  delay () = id
  ty = const Unit

delayPrefix :: String
delayPrefix = "Cons "
              -- "delay "

delayName :: String -> String
delayName = (delayPrefix ++)

unDelayName :: String -> Maybe String
unDelayName = stripPrefix delayPrefix

-- isDelayPrim :: Prim a b -> Bool
-- isDelayPrim = isJust . unDelayName . primName

instance GenBuses Bool where
  genBuses' = -- trace "genBuses' @ Bool" $
              genBus BoolB Bool
  delay = primDelay
  ty = const Bool

instance GenBuses Int  where
  genBuses' = genBus IntB Int
  delay = primDelay
  ty = const Int

instance GenBuses Float  where
  genBuses' = genBus FloatB Float
  delay = primDelay
  ty = const Float

instance GenBuses Double  where
  genBuses' = genBus DoubleB Double
  delay = primDelay
  ty = const Double

instance (GenBuses a, GenBuses b) => GenBuses (a :* b) where
  genBuses' prim ins =
    -- trace ("genBuses' @ " ++ show (ty (undefined :: a :* b))) $
    PairB <$> genBuses' prim ins <*> genBuses' prim ins
  delay (a,b) = delay a *** delay b
  ty ~(a,b) = Pair (ty a) (ty b)

flattenB :: String -> Buses a -> Sources
flattenB name b = fromMaybe err (flattenMb b)
 where
   err = error $ "flattenB/"++name++": unhandled " ++ show b

flattenMb :: Buses a -> Maybe Sources
flattenMb = fmap toList . flat
 where
   flat :: Buses a -> Maybe (Seq Source)
   flat UnitB        = Just mempty
   flat (BoolB b)    = Just (singleton b)
   flat (IntB b)     = Just (singleton b)
   flat (FloatB  b)  = Just (singleton b)
   flat (DoubleB b)  = Just (singleton b)
   flat (PairB a b)  = liftA2 (<>) (flat a) (flat b)
   flat (ConvertB b) = flat b
   flat (FunB _)     = Nothing
   -- flat (AbstB b) = flat b

badBuses :: forall a x. Ok (:>) a => String -> Buses a -> x
badBuses nm bs =
  error (nm ++ " got unexpected bus " ++ show bs
        -- ++ " to make bus type "++show (typeRep (Proxy :: Proxy a))
        )

-- -- Workaround for "spurious non-exhaustive warning with GADT and newtypes"
-- -- <https://ghc.haskell.org/trac/ghc/ticket/6124>.
-- #define BogusMatch(name) name _ = error "BogusMatch"
-- #define BogusAlt _ -> error "BogusMatch"

-- unUnitB :: Buses () -> ()
-- unUnitB UnitB    = ()
-- unUnitB (AbstB _) = badBuses "unUnitB"
-- -- BogusMatch(unUnitB)

unPairB :: Ok2 (:>) a b => Buses (a :* b) -> Buses a :* Buses b
#if 1
unPairB (PairB a b)            = (a,b)
unPairB (ConvertB (PairB c d)) = (convertB c, convertB d)
unPairB b                      = badBuses "unPairB" b
#else
-- Lazier
unPairB w = (a,b)
 where
   a = case w of
         PairB p _ -> p
         bs        -> badBuses "unPairB" bs
--          BogusAlt
   b = case w of
         PairB _ q -> q
         bs        -> badBuses "unPairB" bs
--          BogusAlt

--    (a,b) = case w of
--              PairB p q -> (p,q)
--              AbstB _   -> badBuses "unPairB"

#endif

exlB :: Ok2 (:>) a b => Buses (a :* b) -> Buses a
exlB = fst . unPairB

exrB :: Ok2 (:>) a b => Buses (a :* b) -> Buses b
exrB = snd . unPairB

-- Trying to eliminate Typeable from Ok (:>), since having it leads to lots of
-- large Typeable dictionary constructions.
-- My last dependency is unFunB's use of convertC.
-- type T = Typeable
type T = Yes1

#if 1

type TypeableAR a = (T a, T (Rep a))

-- TODO: if this experiment works out, eliminate AbstB, and rename ConvertB.
abstB :: TypeableAR a => Buses (Rep a) -> Buses a
abstB = convertB

reprB :: TypeableAR a => Buses a -> Buses (Rep a)
reprB = convertB

#else
abstB :: Buses (Rep a) -> Buses a
abstB = AbstB

reprB :: Buses a -> Buses (Rep a)
reprB (AbstB r) = r
reprB b = badBuses "reprB" b
-- reprB b = error ("reprB: non-AbstB: " ++ show b)

-- Alternatively,
-- 
--   abstB :: Rep a ~ a' => Buses a' -> Buses a
--   reprB :: Rep a ~ a' => Buses a -> Buses a'

#endif

convertC :: forall a b. (T a, T b) => a :> b
convertC = C (arr convertB)

convertB :: forall a b. (T a, T b)
         => Buses a -> Buses b
-- convertB a | trace ("convertB " ++ show (typeRep (Proxy :: Proxy (a -> b))) ++ ": " ++ show a ++ "\n") False = undefined
convertB (ConvertB p) = mkConvertB p  -- coalesce
convertB a            = mkConvertB a

-- Make a ConvertB if source and target types differ; otherwise id
mkConvertB :: forall a b. (T a, T b)
           => Buses a -> Buses b
mkConvertB a -- | Just Refl <- eqT @a @b = a
             | otherwise              = ConvertB a

{--------------------------------------------------------------------
    The circuit monad
--------------------------------------------------------------------}

type PrimName = String

-- | Primitive of type @a -> b@
newtype Prim a b = Prim { primName :: PrimName }

instance Show (Prim a b) where show = primName

type CompId = Int

type CompSupply = [CompId]

-- Component: primitive instance with inputs & outputs. Numbered consistently
-- with dependency partial ordering.
data Comp = forall a b. Comp CompId (Prim a b) (Buses a) (Buses b)

deriving instance Show Comp

type Reuses = Int
#if !defined NoHashCons
-- Tracks prim applications (including output type) and reuses per component.
type CompInfo = Map (PrimName,Sources,Ty) (Comp,Reuses)
#else
type CompInfo = [Comp]
#endif

-- The circuit monad.
type CircuitM = State (PinSupply,(CompSupply,CompInfo))

type BCirc a b = Buses a -> CircuitM (Buses b)

-- Instantiate a 'Prim'
genComp :: forall a b. GenBuses b => Prim a b -> BCirc a b
#if !defined NoHashCons
genComp prim a =
  do 
     mb <- M.gets (M.lookup key . snd . snd)
     case mb of
       Just (Comp _ _ _ b', _) ->
         do M.modify (second (second (M.adjust (second succ) key)))
            return (unsafeCoerce b')
       Nothing               ->
         do b <- genBuses prim ins
            (compN:_) <- M.gets (fst . snd)
            let comp = Comp compN prim a b
            M.modify (second (tail *** M.insert key (comp,0)))
            return b
 where
   ins  = flattenBHack "genComp" prim a
   name = primName prim
   key  = (name,ins,ty (undefined :: b))

-- TODO: Possibly key on argument type as well? What currently happens with Eq
-- and Ord operations on Int vs Double? Maybe it's not an issue, since
-- differently typed arguments can't be the same.

#else
genComp prim a = -- trace (printf "genComp %s %s --> %s"
                 --         (show prim) (show a) (show (ty (undefined :: b)))) $
                 do b <- genBuses prim (flattenBHack "genComp" prim a)
                    -- trace (printf "gen'd buses %s" (show b)) (return ())
                    M.modify (second (Comp prim a b :))
                    -- trace (printf "added comp %s" (show (Comp prim a b))) (return ())
                    return b
#endif

-- Treat delays specially to avoid optimization loop.
flattenBHack :: String -> Prim a b -> Buses c -> Sources
-- flattenBHack _ (Prim (unDelayName -> Just _)) _ = []
flattenBHack name _ b = flattenB name b

-- flattenBHack name p b = tweak <$> flattenB name b
--  where
--    tweak ~(Source bus nm ins n) = Source bus nm' ins' n'
--     where
--       (nm',ins',n') | isDelayPrim p = ("bloop",[],0)
--                     | otherwise     = (nm,ins,n)

-- flattenBHack name p b = tweak <$> flattenB name b
--  where
--    tweak ~(Source bus nm ins n) = Source bus nm ins' n
--     where
--       ins' = if isDelayPrim p then [] else ins

-- flattenBHack name p b = tweak <$> flattenB name b
--  where
--    tweak ~(Source bus nm ins n) = Source bus nm ins' n
--     where
--       ins' = if isDelayPrim p then [] else ins

--    tweak | isDelayPrim p = \ ~(Source bus nm _ins n) -> Source bus nm [] n 
--          | otherwise     = id

constComp' :: GenBuses b => String -> CircuitM (Buses b)
constComp' str = -- trace ("constComp' " ++ str) $
                 genComp (Prim str) UnitB

constComp :: GenBuses b => String -> BCirc a b
constComp str = const (constComp' str)

-- TODO: eliminate constComp in favor of a more restrictive version in which a
-- == (), defined as flip genComp UnitB. Add domain flexibility in lambda-ccc
-- instead.

type GST a = (GS a, Tweakable a)

constM :: GST b => b -> BCirc a b
constM b = constComp (constName b)

class Tweakable a where
  tweakVal :: a -> a
  tweakVal = id

instance Tweakable ()
instance Tweakable Bool
instance Tweakable Int
instance Tweakable Float  where tweakVal = pullZero 1e-7
instance Tweakable Double where tweakVal = pullZero 1e-14
-- TODO: tune the deltas

-- Hack to help eliminate numeric errors involved
pullZero :: (Ord a, Num a) => a -> a -> a
pullZero delta a | abs a < delta = 0
                 | otherwise     = a

constName :: (Tweakable b, Show b) => b -> String
constName = show . tweakVal

{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>, :+>

-- | Internal representation for '(:>)'.
type a :+> b = Kleisli CircuitM (Buses a) (Buses b)

-- | Circuit category
newtype a :> b = C { unC :: a :+> b }

instance (TypeableAR a, r ~ Rep a) => RepCat (:>) a r where
  reprC = C (arr reprB)
  abstC = C (arr abstB)

instance -- Coercible a b
         (T a, T b)
      => CoerceCat (:>) a b where
  coerceC = convertC

-- instance CoerceCat (:>) where
--   coerceC = C (arr coerce)

-- pattern CK bc = C (Kleisli bc)

mkCK :: BCirc a b -> (a :> b)
mkCK = C . Kleisli

unmkCK :: (a :> b) -> BCirc a b
unmkCK = runKleisli . unC

-- TODO: Eliminate mkCK in favor of CK

inCK :: (BCirc a a' -> BCirc b b')
     -> ((a :> a') -> (b :> b'))
inCK = mkCK <~ unmkCK

inCK2 :: (BCirc a a' -> BCirc b b' -> BCirc c c')
      -> ((a :> a') -> (b :> b') -> (c :> c'))
inCK2 = inCK <~ unmkCK

namedC :: GenBuses b => String -> a :> b
-- namedC name = primOpt name noOpt
namedC name = mkCK (genComp (Prim name))

type Opt b = Sources -> CircuitM (Maybe (Buses b))

justA :: Applicative f => a -> f (Maybe a)
justA = pure . Just

nothingA :: Applicative f => f (Maybe a)
nothingA = pure Nothing

newComp :: (a :> b) -> Buses a -> CircuitM (Maybe (Buses b))
newComp cir = fmap Just . unmkCK cir

newComp1 :: SourceToBuses a => (a :> b) -> Source -> CircuitM (Maybe (Buses b))
newComp1 cir a = newComp cir (toBuses a)

newComp2 :: (SourceToBuses a, SourceToBuses b) =>
            (a :* b :> c) -> Source -> Source -> CircuitM (Maybe (Buses c))
newComp2 cir a b = newComp cir (PairB (toBuses a) (toBuses b))

newComp3L :: (SourceToBuses a, SourceToBuses b, SourceToBuses c) =>
             ((a :* b) :* c :> d) -> Source -> Source -> Source -> CircuitM (Maybe (Buses d))
newComp3L cir a b c = newComp cir (PairB (PairB (toBuses a) (toBuses b)) (toBuses c))

newComp3R :: (SourceToBuses a, SourceToBuses b, SourceToBuses c) =>
             (a :* (b :* c) :> d) -> Source -> Source -> Source -> CircuitM (Maybe (Buses d))
newComp3R cir a b c = newComp cir (PairB (toBuses a) (PairB (toBuses b) (toBuses c)))

newVal :: GST b => b -> CircuitM (Maybe (Buses b))
newVal b = Just <$> constM' b

constM' :: GST b => b -> CircuitM (Buses b)
constM' b = constComp' (constName b)

-- noOpt :: Opt b
-- noOpt = const nothingA

orOpt :: Binop (Opt b)
orOpt f g a = do mb <- f a
                 case mb of
                   Nothing -> g a
                   Just _  -> return mb

primOpt :: GenBuses b => String -> Opt b -> a :> b
primOptSort :: (Ok (:>) a, GenBuses b) => String -> Opt b -> a :> b
#if !defined NoOptimizeCircuit

-- primOpt name _ = mkCK (genComp (Prim name))

primOpt name opt =
  mkCK $ \ a -> let plain = genComp (Prim name) a in
                  case flattenMb a of
                    Nothing   -> plain
                    Just srcs -> opt srcs >>= maybe plain return

tryCommute :: a :> a
tryCommute = mkCK try
 where
#if !defined NoCommute
   try (PairB (BoolB a) (BoolB a')) | a > a' = return (PairB (BoolB a') (BoolB a))
   try (PairB (IntB  a) (IntB  a')) | a > a' = return (PairB (IntB  a') (IntB  a))
   -- TODO: Float & Double
#endif
   try b = return b

-- Like primOpt, but sorts. Use for commutative operations to improve reuse
-- (cache hits).
primOptSort name opt = primOpt name opt . tryCommute
#else
primOpt name _ = namedC name
primOptSort = primOpt
#endif

primNoOpt1 :: (GST b, Read a) => String -> (a -> b) -> a :> b
primNoOpt1 name fun = 
  primOpt name $
    \ case [Val x] -> newVal (fun x)
           _       -> nothingA

-- -- | Constant circuit from source generator (experimental)
-- constSM :: CircuitM (Buses b) -> (a :> b)
-- constSM mkB = mkCK (const mkB)

-- -- | Constant circuit from source
-- constS :: Buses b -> (a :> b)
-- constS b = constSM (return b)

constC :: GST b => b -> a :> b
constC = mkCK . constM

-- Phasing out constC

-- pureC :: Buses b -> a :> b
-- pureC = mkCK . pure . pure

#if 0
litUnit :: () -> a :> ()
litUnit = pureC . const UnitB

litInt :: Int -> a :> Int
litInt = pureC . IntB . IntS

litBool :: Bool -> a :> Bool
litBool = pureC . BoolB . BoolS
#endif

inC :: (a :+> b -> a' :+> b') -> (a :> b -> a' :> b')
inC = C <~ unC

inC2 :: (a :+> b -> a' :+> b' -> a'' :+> b'')
     -> (a :>  b -> a' :>  b' -> a'' :>  b'')
inC2 = inC <~ unC

instance Category (:>) where
  type Ok (:>) = T
  id  = C id
  (.) = inC2 (.)

-- onPairBM :: Functor m =>
--             (Buses a :* Buses b -> m (Buses a' :* Buses b'))
--          -> (Buses (a :* b) -> m (Buses (a' :* b')))
-- onPairBM f = fmap pairB . f . unPairB

crossB :: (Applicative m, Ok2 (:>) a b)
       => (Buses a -> m (Buses c)) -> (Buses b -> m (Buses d))
       -> (Buses (a :* b) -> m (Buses (c :* d)))
crossB f g = (\ ~(a,b) -> liftA2 PairB (f a) (g b)) . unPairB

-- or drop crossB in favor of forkB with fstB and sndB

forkB :: Applicative m =>
         (Buses a -> m (Buses c)) -> (Buses a -> m (Buses d))
      -> (Buses a -> m (Buses (c :* d)))
forkB f g a = liftA2 PairB (f a) (g a)

-- or drop forkB in favor of dupB and crossB

dupB :: Applicative m =>
        Buses a -> m (Buses (a :* a))
dupB a = pure (PairB a a)

instance ProductCat (:>) where
  -- type Prod (:>) = (:*)
  exl   = C (arr exlB)
  exr   = C (arr exrB)
  dup   = mkCK dupB
  (***) = inCK2 crossB  -- or default
  (&&&) = inCK2 forkB   -- or default

#if 1

instance (Ok (:>) a, IfCat (:>) b) => IfCat (:>) (a -> b) where
  ifC = funIf

unFunB :: {- Ok2 (:>) a b => -} Buses (a -> b) -> (a :> b)
unFunB (FunB ab)            = ab
unFunB (ConvertB (FunB cd)) = convertC A.. cd A.. convertC
unFunB bs                   = badBuses "unFunB" bs

pairB :: Buses a :* Buses b -> Buses (a :* b)
pairB (a,b) = PairB a b

instance ClosedCat (:>) where
  -- type Exp (:>) = (->)
  apply   = C (applyK . first (arr (unC . unFunB)) . arr unPairB)
  curry   = inC $ \ h -> arr (FunB . C) . curryK (h . arr pairB)
  uncurry = inC $ \ f -> uncurryK (arr (unC . unFunB) . f) . arr unPairB 
#endif

#if defined TypeDerivation

-- ClosedCat type derivations:

type KC = Kleisli CircuitM

-- apply:

unC :: (a :> b) -> (a :+> b)
unFunB :: Buses (a -> b) -> (a :> b)
unC . unFunB :: Buses (a -> b) -> (a :+> b)
arr (unC . unFunB) :: KC (Buses (a -> b)) (a :+> b)
first (arr (unC . unFunB))
  :: KC (Buses (a -> b) :* Buses a) ((a :+> b) :* Buses a)
applyK . first (arr (unC . unFunB))
  :: KC (Buses (a -> b) :* Buses a) (Buses b)
applyK . first (arr (unC . unFunB)) . arr unPairB
  :: KC (Buses ((a -> b) :* a)) (Buses b)
  :: ((a -> b) :* a) :+> b
C (applyK . first (arr (unC . unFunB)) . arr unPairB) :: ((a -> b) :* a) :> b

-- curry:

h :: a :* b :> c
unC h :: a :* b :+> c
      :: KC (Buses (a :* b)) (Buses c)
unC h . arr pairB :: KC (Buses a :* Buses b) (Buses c)
curryK (unC h . arr pairB) :: KC (Buses a) (KC (Buses b) (Buses c))
arr C . curryK (unC h . arr pairB) :: KC (Buses a) (b :> c)
arr (FunB . C) . curryK (unC h . arr pairB) :: KC (Buses a) (Buses (b -> c))
C (arr (FunB . C) . curryK (unC h . arr pairB)) :: a :> (b -> c)

-- Derive uncurry by inverting curry:

f == arr (FunB . C) . curryK (h . arr pairB)
arr (unC . unFunB) . f == curryK (h . arr pairB)
uncurryK (arr (unC . unFunB) . f) == h . arr pairB
uncurryK (arr (unC . unFunB) . f) . arr unPairB == h

#endif

instance TerminalCat (:>) where
  -- type Unit (:>) = ()
  -- it = C (const UnitB . it)
  -- it = mkCK (const (return UnitB))
  it = C (arr (pure UnitB))

#if 0

instance GST b => ConstCat (:>) b where
  const b = -- trace ("circuit const " ++ show b) $
            constC b

#else

#define LitConst(ty) instance ConstCat (:>) (ty) where const = constC

LitConst(())
LitConst(Bool)
LitConst(Int)
LitConst(Float)
LitConst(Double)

-- -- This instance is problematic with Maybe / sums, since it leads to evaluating bottom.
-- -- See notes from 2016-01-13.
-- instance (ConstCat (:>) a, ConstCat (:>) b) => ConstCat (:>) (a :* b) where
--   const = pairConst

#endif

#if 0
class MaybeCat k where
  nothing :: () `k` Maybe a
  just    :: a `k` Maybe a
  maybe   :: (() `k` c) -> (a `k` c) -> (Maybe a `k` c)

type Maybe a = a :* Bool

nothing = (undefined,False)
just a  = (a,True )

maybe n j (a,p) = if p then n else j a

newtype a :> b = C { unC :: a :+> b }
type a :+> b = Kleisli CircuitM (Buses a) (Buses b)

constM' :: GS b => b -> CircuitM (Buses b)

#endif

#if 1

#define UNDEFINED "⊥"

bottomScalar :: GenBuses b => z :> b
bottomScalar = -- trace "bottomScalar called" $
               mkCK (constComp UNDEFINED)

#define BottomPrim(ty) \
 instance BottomCat (:>) z (ty) where { bottomC = bottomScalar }

BottomPrim(Bool)
BottomPrim(Int)
BottomPrim(Float)
BottomPrim(Double)

instance BottomCat (:>) z () where
--   bottomC = mkCK (const (return UnitB))
  bottomC = C (arr (const UnitB))

-- instance (BottomCat (:>) a, BottomCat (:>) b) => BottomCat (:>) (a :* b) where
--   bottomC = bottomC &&& bottomC

#if defined TypeDerivation
bottomC :: () :> b
bottomC . exl :: () :* a :> b
curry (bottomC . exl) :: () :> (a -> b)
#endif

#elif 0
instance GenBuses a => BottomCat (:>) a where
  bottomC = mkCK (const mkBot)
#elif 0
instance BottomCat (:>) where
  type BottomKon (:>) a = GenBuses a
  bottomC = mkCK (const (genBuses (Prim UNDEFINED) []))
-- See the note at BottomCat
#elif 0
instance BottomCat (:>) where
  type BottomKon (:>) a = GenBuses a
  bottomC = mkCK (const mkBot)
#endif

-- TODO: state names like "⊕" and "≡" just once.

class SourceToBuses a where toBuses :: Source -> Buses a
instance SourceToBuses ()     where toBuses = const UnitB
instance SourceToBuses Bool   where toBuses = BoolB
instance SourceToBuses Int    where toBuses = IntB
instance SourceToBuses Float  where toBuses = FloatB
instance SourceToBuses Double where toBuses = DoubleB

sourceB :: SourceToBuses a => Source -> CircuitM (Maybe (Buses a))
sourceB = justA . toBuses

unknownName :: PrimName
unknownName = "??"

instance GenBuses b => UnknownCat (:>) a b where
  unknownC = namedC unknownName

#define Sat(pred) ((pred) -> True)
#define Eql(x) Sat(==(x))

-- -- https://ghc.haskell.org/trac/ghc/ticket/12007
-- #define BrokenPat

#if !defined BrokenPat
pattern Read :: Read a => a -> String
pattern Read x <- (reads -> [(x,"")])

pattern ConstS :: PrimName -> Source
pattern ConstS name <- Source _ name [] 0

pattern Val :: Read a => a -> Source
pattern Val x <- ConstS (Read x)

-- pattern Val x       <- ConstS (reads -> [(x,"")])

pattern TrueS :: Source
pattern TrueS  <- ConstS("True")

pattern FalseS :: Source
pattern FalseS <- ConstS("False")

pattern NotS :: Source -> Source
pattern NotS a <- Source _ "¬" [a] 0

pattern XorS :: Source -> Source -> Source
pattern XorS a b <- Source _ "⊕" [a,b] 0

pattern EqS :: Source -> Source -> Source
pattern EqS a b <- Source _ "≡" [a,b] 0

-- pattern NeS :: Source -> Source -> Source
-- pattern NeS a b <- Source _ "≢" [a,b] 0

#else

#define Read(x) (reads -> [((x),"")])
#define ConstS(name) (Source _ name [] 0)
#define Val(x) ConstS(Read(x))

#define TrueS ConstS("True")
#define FalseS ConstS("False")
#define NotS(a) (Source _ "¬" [a] 0)
#define XorS(a,b) (Source _ "⊕" [a,b] 0)
#define EqS(a,b) <- (Source _ "≡" [a,b] 0)

-- pattern NeS :: Source -> Source -> Source
-- pattern NeS a b <- Source _ "≢" [a,b] 0

#endif

primDelay :: (SourceToBuses a, GS a) => a -> (a :> a)
primDelay a0 = primOpt (delayName a0s) $ \ case
                 [c@(ConstS (Eql(a0s)))] -> sourceB c
                 _ -> nothingA
 where
   a0s = show a0

-- primDelay a0 = namedC (delayName (show a0))

instance BoolCat (:>) where
  -- type BoolOf (:>) = Bool
  notC = primOpt "¬" $ \ case
           [NotS a]  -> sourceB a
           [Val x]   -> newVal (not x)
           _         -> nothingA
  -- TODO: I want to add more like the following:
  -- 
  --      [EqS a b] -> newComp2 notEqual a b
  --      
  -- But
  -- 
  --   Ambiguous type variable ‘b0’ arising from a use of ‘newComp2’
  --   prevents the constraint ‘(SourceToBuses b0)’ from being solved.
  -- 
  -- Optimizations are limited by not having static access to source types. I
  -- think I can fix it by adding a `Ty` (statically typed type GADT) to
  -- `Source`. Or maybe a simpler version for primitive types only.
  andC = primOptSort "∧" $ \ case
           [TrueS ,y]            -> sourceB y
           [x,TrueS ]            -> sourceB x
           [x@FalseS,_]          -> sourceB x
           [_,y@FalseS]          -> sourceB y
#if !defined NoIdempotence
           [x,x']      | x' == x -> sourceB x
#endif
           [x,NotS x'] | x' == x -> newVal False
           [NotS x,x'] | x' == x -> newVal False
           _                     -> nothingA
  orC  = primOptSort "∨" $ \ case
           [FalseS,y]            -> sourceB y
           [x,FalseS]            -> sourceB x
           [x@TrueS ,_]          -> sourceB x
           [_,y@TrueS ]          -> sourceB y
#if !defined NoIdempotence
           [x,x']      | x' == x -> sourceB x
#endif
           [x,NotS x'] | x' == x -> newVal True
           [NotS x,x'] | x' == x -> newVal True
           -- not a    || not b == not (a && b)
           -- TODO: Handle more elegantly.
           [NotS x, NotS y]      ->
             do o <- unmkCK andC (PairB (BoolB x) (BoolB y))
                newComp notC o
           _                     -> nothingA
  xorC = primOptSort "⊕" $ \ case
           [FalseS,y]            -> sourceB y
           [x,FalseS]            -> sourceB x
           [TrueS,y ]            -> newComp1 notC y
           [x,TrueS ]            -> newComp1 notC x
           [x,x']      | x' == x -> newVal False
           [x,NotS x'] | x' == x -> newVal True
           [NotS x,x'] | x' == x -> newVal True
#if 1
           -- not x `xor` y == not (x `xor` y)
           [NotS x, y]                -> newComp2 (notC . xorC) x y
           [x, NotS y]                -> newComp2 (notC . xorC) x y
           -- x `xor` (x `xor` y) == y
           [x, x' `XorS` y] | x' == x -> sourceB y
           [x, y `XorS` x'] | x' == x -> sourceB y
           [x `XorS` y, x'] | x' == x -> sourceB y
           [y `XorS` x, x'] | x' == x -> sourceB y
#endif
           _                          -> nothingA

#define BooloInt "Bool→Int"

boolToIntC :: Bool :> Int
boolToIntC = namedC BooloInt

-- instance BoolCat (:>) where
--   notC = namedC "¬"
--   andC = namedC "∧"
--   orC  = namedC "∨"
--   xorC = namedC "⊕"

-- TODO: After I have more experience with these graph optimizations, reconsider
-- the interface.

#if 1

-- noOpt :: Opt b
-- noOpt = const nothingA

eqOpt, neOpt :: forall a. (Read a, Eq a) => Opt Bool
eqOpt = \ case
  [Val (x :: a), Val y] -> newVal (x == y)
  [a,b] | a == b -> newVal True
  _              -> nothingA
neOpt = \ case
  [Val (x :: a), Val y] -> newVal (x /= y)
  [a,b] | a == b -> newVal False
  _              -> nothingA

#define EqPrim(ty) \
 instance EqCat (:>) (ty) where { \
    equal    = primOptSort "≡" (eqOpt @(ty)) ;\
    notEqual = primOptSort "≢" (neOpt @(ty))  \
  }

iffC :: EqCat k (BoolOf k) => Prod k (BoolOf k) (BoolOf k) `k` BoolOf k
iffC = equal

eqOptB, neOptB :: Opt Bool
-- eqOptB = noOpt
-- neOptB = noOpt

eqOptB = \ case
  [TrueS,y]                           -> sourceB y
  [x,TrueS]                           -> sourceB x
  [FalseS,y ]                         -> newComp1 notC y
  [x,FalseS ]                         -> newComp1 notC x
  [x,NotS x']      | x' == x          -> newVal False
  [NotS x,x']      | x' == x          -> newVal False
  -- not x == y == not (x == y)
  [NotS x, y]                         -> newComp2 (notC . iffC) x y
  [x, NotS y]                         -> newComp2 (notC . iffC) x y
  -- x == (x /= y) == not y
  [x, x' `XorS` y] | x' == x          -> newComp1 notC y
  [x, y `XorS` x'] | x' == x          -> newComp1 notC y
  [x `XorS` y, x'] | x' == x          -> newComp1 notC y
  [y `XorS` x, x'] | x' == x          -> newComp1 notC y
  -- x == (x == y) == y
  [x, x' `EqS` y]  | x' == x          -> sourceB y
  [x, y `EqS` x']  | x' == x          -> sourceB y
  [x `EqS` y, z]   | z == x || z == y -> sourceB y
  _                                   -> nothingA

--   [x `EqS` y, Eql(x)]  -> sourceB y
--   [y `EqS` x, Eql(x)]  -> sourceB y
-- 
--     Pattern match checker exceeded (2000000) iterations in
--     a case alternative.

neOptB = \ case
  [FalseS,y]                          -> sourceB y
  [x,FalseS]                          -> sourceB x
  [TrueS,y ]                          -> newComp1 notC y
  [x,TrueS ]                          -> newComp1 notC x
  [x,x']           | x' == x          -> newVal False
  [x,NotS x']      | x' == x          -> newVal True
  [NotS x,x']      | x' == x          -> newVal True
  -- not x `xor` y == not (x `xor` y)
  [NotS x, y]                         -> newComp2 (notC . xorC) x y
  [x, NotS y]                         -> newComp2 (notC . xorC) x y
  -- x `xor` (x `xor` y) == y
  [x, x' `XorS` y] | x' == x          -> sourceB y
  [x, y `XorS` x'] | x' == x          -> sourceB y
  [x `XorS` y, x'] | x' == x          -> sourceB y
  [y `XorS` x, x'] | x' == x          -> sourceB y
  -- x `xor` (x == y) == not y
  [x, x' `EqS` y]  | x' == x          -> newComp1 notC y
  [x, y `EqS` x']  | x' == x          -> newComp1 notC y
  [x `EqS` y, z]   | z == x || z == y -> newComp1 notC y
  _                                   -> nothingA

--   [x `EqS` y, Eql(x)]  -> newComp1 notC y
--   [y `EqS` x, Eql(x)]  -> newComp1 notC y
-- 
--     Pattern match checker exceeded (2000000) iterations in
--     a case alternative.

-- EqPrim(Bool)
EqPrim(Int)
EqPrim(Float)
EqPrim(Double)

instance EqCat (:>) Bool where
  equal    = primOptSort "≡" (eqOpt @Bool `orOpt` eqOptB)
  notEqual = primOptSort "⊕" (neOpt @Bool `orOpt` neOptB)

instance EqCat (:>) () where
  equal = constC True

instance (EqCat (:>) a, EqCat (:>) b) => EqCat (:>) (a,b) where
  equal = andC . (equal *** equal) . transposeP

-- TODO: optimizations.
ltOpt, gtOpt, leOpt, geOpt :: forall a. (Read a, Ord a) => Opt Bool
-- ltOpt = noOpt
-- gtOpt = noOpt
-- leOpt = noOpt
-- geOpt = noOpt

ltOpt = \ case
  [Val (x :: a), Val y] -> newVal (x < y)
  [a,b] | a == b        -> newVal False
  _                     -> nothingA
gtOpt = \ case
  [Val (x :: a), Val y] -> newVal (x > y)
  [a,b] | a == b        -> newVal False
  _                     -> nothingA
leOpt = \ case
  [Val (x :: a), Val y] -> newVal (x <= y)
  [a,b] | a == b        -> newVal True
  _                     -> nothingA
geOpt = \ case
  [Val (x :: a), Val y] -> newVal (x >= y)
  [a,b] | a == b        -> newVal True
  _                     -> nothingA

-- ltOpt = \ case
--   [Val x, Val y] -> newVal (x < y)
--   _              -> nothingA

--     No instance for (Read a0) arising from a pattern
--     The type variable ‘a0’ is ambiguous

#define OrdPrim(ty) \
 instance OrdCat (:>) (ty) where { \
   lessThan           = primOpt "<" (ltOpt @(ty)) ; \
   greaterThan        = primOpt ">" (gtOpt @(ty)) ; \
   lessThanOrEqual    = primOpt "≤" (leOpt @(ty)) ; \
   greaterThanOrEqual = primOpt "≥" (geOpt @(ty)) ; \
 }

OrdPrim(Bool)
OrdPrim(Int)
OrdPrim(Float)
OrdPrim(Double)

instance OrdCat (:>) () where
  lessThan = constC False

-- TODO:
-- 
-- instance (OrdCat (:>) a, OrdCat (:>) b) => OrdCat (:>) (a,b) where
--   ...

-- TODO: Move to a general definition in ConCat.Classes, and reference here.

#else

instance (Read a, Eq a) => EqCat (:>) a where
    equal    = primOptSort "≡" $ \ case
                 [Val (x :: a), Val y] -> newVal (x == y)
                 [a,b] | a == b -> newVal True
                 _              -> nothingA
    notEqual = primOptSort "≢" $ \ case
                 [Val (x :: a), Val y] -> newVal (x /= y)
                 [a,b] | a == b -> newVal False
                 _              -> nothingA

instance (Read a, Ord a) => OrdCat (:>) a where
   lessThan           = primOpt "<" $ \ case
                          [Val (x :: a), Val y] -> newVal (x < y)
                          [a,b] | a == b        -> newVal False
                          _                     -> nothingA
   greaterThan        = primOpt ">" $ \ case
                          [Val (x :: a), Val y] -> newVal (x > y)
                          [a,b] | a == b        -> newVal False
                          _                     -> nothingA
   lessThanOrEqual    = primOpt "≤" $ \ case
                          [Val (x :: a), Val y] -> newVal (x <= y)
                          [a,b] | a == b        -> newVal True
                          _                     -> nothingA
   greaterThanOrEqual = primOpt "≥" $ \ case
                          [Val (x :: a), Val y] -> newVal (x >= y)
                          [a,b] | a == b        -> newVal True
                          _                     -> nothingA


#endif

-- TODO: Move to a general definition in ConCat.Classes, and reference here.

-- instance NumCat (:>) Int  where { add = namedC "+" ; mul = namedC "×" }

-- More robust (works for Double as well):

#define ValT(x,ty) (Val ((x) :: ty))

#define   ZeroT(ty) ValT(0,ty)
#define    OneT(ty) ValT(1,ty)
#define NegOneT(ty) ValT((-1),ty)

pattern NegateS :: Source -> Source
pattern NegateS a <- Source _ "negate" [a] 0

pattern RecipS  :: Source -> Source
pattern RecipS  a <- Source _ "recip"  [a] 0

instance (Num a, Read a, GST a, Eq a, SourceToBuses a)
      => NumCat (:>) a where
  negateC = primOpt "negate" $ \ case
              [Val x]        -> newVal (negate x)
              [NegateS x]    -> sourceB x
              _              -> nothingA
  addC    = primOptSort "+" $ \ case
              [Val x, Val y] -> newVal (x + y)
              [ZeroT(a),y]   -> sourceB y
              [x,ZeroT(a)]   -> sourceB x
              [x,NegateS y]  -> newComp2 subC x y
              [NegateS x,y]  -> newComp2 subC y x
              _              -> nothingA
  subC    = primOpt     "−" $ \ case
              [Val x, Val y] -> newVal (x - y)
              [ZeroT(a),y]   -> newComp1 negateC y
              [x,ZeroT(a)]   -> sourceB x
              [x,NegateS y]  -> newComp2 addC x y
              [NegateS x,y]  -> newComp2 (negateC . addC) x y
              _              -> nothingA
  mulC    = primOptSort "×" $ \ case
              [Val x, Val y] -> newVal (x * y)
              [OneT(a),y]    -> sourceB y
              [x,OneT(a)]    -> sourceB x
              [x@ZeroT(a),_] -> sourceB x
              [_,y@ZeroT(a)] -> sourceB y
              [NegOneT(a) ,y] -> newComp1 negateC y
              [x,NegOneT(a) ] -> newComp1 negateC x
              _              -> nothingA
  powIC   = primOpt     "↑" $ \ case
              [Val x, Val y] -> newVal (x ^ (y :: Int))
              [x@OneT(a) ,_] -> sourceB x
              [x,   OneT(a)] -> sourceB x
              [x@ZeroT(a),_] -> sourceB x
              [_,  ZeroT(a)] -> newVal (fromInteger 1)
              _              -> nothingA

instance (Fractional a, Read a, Eq a, GST a, SourceToBuses a)
      => FractionalCat (:>) a where
  recipC  = primOpt "recip" $ \ case
              [Val x]        -> newVal (recip x)
              [RecipS x]     -> sourceB x
              [NegateS x]    -> newComp1 (negateC . recipC) x
              _              -> nothingA
  divideC = primOpt "÷" $ \ case
              [Val x, Val y] -> newVal (x / y)
              [z@ZeroT(a),_] -> sourceB z
              [x,NegateS y]  -> newComp2 (negateC . divideC) x y
              _              -> nothingA

instance (RealFrac a, Integral b, GST a, GST b, Read a)
      => RealFracCat (:>) a b where
  floorC = primNoOpt1 "floor" floor
  ceilingC = primNoOpt1 "ceiling" ceiling

instance (Floating a, Read a, GST a) => FloatingCat (:>) a where
  expC = primNoOpt1 "exp" exp
  cosC = primNoOpt1 "cos" cos
  sinC = primNoOpt1 "sin" sin

-- TODO: optimizations, e.g., sin & cos of negative angles.

instance ({-Ok (:>) a, -}Integral a, Num b, Read a, GST b)
      => FromIntegralCat (:>) a b where
  fromIntegralC = primNoOpt1 "fromIntegral" fromIntegral

instance (ConstCat (:>) a, NumCat (:>) a, Num a) => EnumCat (:>) a

-- Simplifications for all types:
-- 
--   if' (False,(_,a))     = a
--   if' (True ,(b,_))     = b
--   if' (not a,(b,c))     = if' (a,(c,b))
--   if' (_    ,(a,a))     = a
--   if' (a,(b,bottom))    = b
--   if' (a,(bottom,c))    = c
--
-- Simplifications for Bool values:
-- 
--   if' (c,(True,False))  = c
--   if' (c,(False,True))  = not c
--   if' (a,(b,False))     =     a && b
--   if' (a,(False,b))     = not a && b
--   if' (a,(True ,b))     =     a || b
--   if' (a,(b,True ))     = not a || b
--   if' (c,(not a,a))     = c `xor` a
--   if' (c,(a,not a))     = c `xor` not a
--   if' (b,(c `xor` a,a)) = (b && c) `xor` a
--   if' (b,(a `xor` c,a)) = (b && c) `xor` a

ifOptB :: Opt Bool
ifOptB = \ case
  [c,TrueS,FalseS]       -> sourceB c
  [c,FalseS,TrueS]       -> newComp1 notC c
  [a,b,FalseS]           -> newComp2 andC a b
  [a,FalseS,b]           -> newComp2 (andC . first notC) a b -- not a && b
  [a,TrueS, b]           -> newComp2 orC  a b
  [a,b ,TrueS]           -> newComp2 (orC  . first notC) a b -- not a || b
  [c,NotS a,Eql(a)]      -> newComp2 xorC c a
  [c,a,b@(NotS(Eql(a)))] -> newComp2 xorC c b
  [b,c `XorS` a,Eql(a)]  -> newComp3L (xorC . first andC) b c a -- (b && c) `xor` a
  [b,a `XorS` c,Eql(a)]  -> newComp3L (xorC . first andC) b c a -- ''
  _                      -> nothingA

#if !defined NoIfBotOpt
pattern BottomS :: Source
pattern BottomS <- ConstS UNDEFINED
#endif

ifOpt :: (IfCat (:>) a, SourceToBuses a) => Opt a
ifOpt = \ case
  [FalseS,_,a]  -> sourceB a
  [ TrueS,b,_]  -> sourceB b
  [NotS a,b,c]  -> newComp3R ifC a c b
  [_,a,Eql(a)]  -> sourceB a
#if !defined NoIfBotOpt
  [_,b,BottomS] -> sourceB b
  [_,BottomS,c] -> sourceB c
#endif
  _             -> nothingA

ifOptI :: Opt Int

#if 0

-- Zero or one, yielding the False or True, respectively.
pattern BitS :: Bool -> Source
pattern BitS b <- Source _ (readBit -> Just b) [] 0

readBit :: String -> Maybe Bool
readBit "0" = Just False
readBit "1" = Just True
readBit _   = Nothing

pattern BToIS :: Source -> Source
pattern BToIS a <- Source _ BooloInt [a] 0

-- if c then 0 else b == if c then boolToInt False else b
-- if c then 1 else b == if c then boolToInt True  else b
-- 
-- if c then a else 0 == if c then a else boolToInt False
-- if c then a else 1 == if c then a else boolToInt True
-- 
-- if c then boolToInt a else boolToInt b = boolToInt (if c then a else b)
ifOptI = \ case
  [c,BitS x,b]         -> newComp2 (ifC . second (bToIConst x &&& id)) c b
  [c,a,BitS y]         -> newComp2 (ifC . second (id &&& bToIConst y)) c a
  [c,BToIS a, BToIS b] -> newComp3R (boolToIntC . ifC) c a b
  _                    -> nothingA

bToIConst :: Bool -> (a :> Int)
bToIConst x = boolToIntC . constC x

#else

pattern ZeroS :: Source
pattern ZeroS <- ConstS "0"

pattern OneS :: Source
pattern OneS <- ConstS "1"

-- (if c then 1 else 0) = boolToInt c
-- (if c then 0 else 1) = boolToInt (not c)
ifOptI = \ case
  [c,OneS,ZeroS] -> newComp1 boolToIntC c
  [c,ZeroS,OneS] -> newComp1 (boolToIntC . notC) c
  _              -> nothingA
#endif

instance IfCat (:>) Bool   where ifC = primOpt "if" (ifOpt `orOpt` ifOptB)
instance IfCat (:>) Int    where ifC = primOpt "if" (ifOpt `orOpt` ifOptI)
instance IfCat (:>) Float  where ifC = primOpt "if" ifOpt
instance IfCat (:>) Double where ifC = primOpt "if" ifOpt

-- instance IfCat (:>) Bool where ifC = namedC "if"
-- instance IfCat (:>) Int  where ifC = namedC "if"

instance IfCat (:>) () where ifC = unitIf

instance (IfCat (:>) a, IfCat (:>) b) => IfCat (:>) (a :* b) where
  ifC = prodIf

instance (GenBuses a, Ok2 (:>) a b) => Show (a :> b) where
  show = show . runC

--     Application is no smaller than the instance head
--       in the type family application: RepT :> a
--     (Use -XUndecidableInstances to permit this)

-- Turn a circuit into a list of components, including fake In & Out.
runC :: (GenBuses a, Ok (:>) b) => (a :> b) -> [(Comp,Reuses)]
runC = runU . unitize

type UU = () :> ()

runU :: UU -> [(Comp,Reuses)]
runU cir = getComps compInfo
 where
   compInfo :: CompInfo
   (_,(_,compInfo)) = execState (unmkCK cir UnitB) (PinId <$> [0 ..],([0..],mempty))
#if !defined NoHashCons
   getComps = M.elems 
#else
   getComps = map (,0)
#endif

-- Wrap a circuit with fake input and output
unitize :: (GenBuses a, Ok (:>) b) => (a :> b) -> UU
unitize = namedC "Out" <~ namedC "In"

-- type instance OkayArr (:>) a b = GenBuses a

-- unitize' :: Uncurriable (:>) a b => (a :> b) -> UU
-- unitize' = unitize . uncurries

-- TODO: phase out unitize, and rename unitize'.

{--------------------------------------------------------------------
    Visualize circuit as dot graph
--------------------------------------------------------------------}

-- I could use the language-dot API, but it's easier not to.
-- TODO: Revisit this choice if the string manipulation gets complicated.

systemSuccess :: String -> IO ()
systemSuccess cmd = 
  do status <- system cmd
     case status of
       ExitSuccess -> return ()
       _ -> fail (printf "command \"%s\" failed." cmd)


type Attr = (String,String)

-- Some options:
-- 
-- ("pdf","")
-- ("svg","")
-- ("png","-Gdpi=200")
-- ("jpg","-Gdpi=200")

renameC :: Unop String
renameC = id
#if defined NoOptimizeCircuit
        . (++"-no-opt")
#else
#if defined NoIdempotence
        . (++"-no-idem")
#endif
#if defined NoIfBotOpt
        . (++"-no-ifbot")
#endif
#endif
#if defined NoHashCons
        . (++"-no-hash")
#endif
#if defined NoMend
        . (++"-no-mend")
#endif
#if defined ShowDepths
        . (++"-with-depths")
#endif
#if defined ShallowDelay
        . (++"-shallow-delay")
#endif

type Name = String
type Report = String

type GraphInfo = (Name,CompDepths,Report)

mkGraph :: Name -> UU -> GraphInfo
mkGraph (renameC -> name') uu = (name',depths,report)
 where
   graph  = uuGraph uu
   depths = longestPaths graph
   depth  = longestPath depths
   report | depth == 0 = "No components.\n"  -- except In & Out
          | otherwise  =
              printf "%s components: %s.%s Max depth: %d.\n"
                name' (summary graph)
#if False && !defined NoHashCons
                -- Are the reuse counts legit or an artifact of optimization?
                (let reused :: Map PrimName Reuses
                     reused = M.fromListWith (+)
                               [(nm,reuses) | CompS _ nm _ _ reuses <- graph]
                 in
                   case showCounts (M.toList reused) of
                     ""  -> ""
                     str -> printf " Reuses: %s." str)
#else          
                ""
#endif         
                depth

outDir :: String
outDir = "out"

outFile :: String -> String -> String
outFile name suff = outDir++"/"++name++"."++suff

writeDot :: [Attr] -> GraphInfo -> IO ()
writeDot attrs (name,depths,report) = 
  do createDirectoryIfMissing False outDir
     writeFile (outFile name "dot")
       (graphDot name attrs depths ++ "\n// "++ report)
     putStr report

-- backgroundRender :: Bool
-- backgroundRender = True

displayDot :: (String,String) -> String -> IO ()
displayDot (outType,res) name = 
  do putStrLn dotCommand
     systemSuccess dotCommand
     -- printf "Wrote %s\n" picFile
     systemSuccess $ printf "%s %s" open picFile
 where
   dotCommand = printf "dot %s -T%s %s -o %s" res outType dotFile picFile
   dotFile = outFile name "dot"
   picFile = outFile name outType
   open = case SI.os of
            "darwin" -> "open"
            "linux"  -> "display" -- was "xdg-open"
            _        -> error "unknown open for OS"

showCounts :: [(PrimName,Int)] -> String
showCounts = intercalate ", "
           . map (\ (nm,num) -> printf "%d %s" num nm)
           . (\ ps -> if length ps <= 1 then ps
                       else ps ++ [("total",sum (snd <$> ps))])
           . filter (\ (nm,n) -> n > 0 && not (isOuterPrim nm))

summary :: DGraph -> String
summary = showCounts
        . histogram
        . map compName

histogram :: Ord a => [a] -> [(a,Int)]
histogram = map (head &&& length) . group . sort

-- TODO: Instead of failing, emit a message about the generated file. Perhaps
-- simply use "echo".

type Input  = Bus
type Output = Bus

data CompS = CompS CompId PrimName [Input] [Output] Reuses deriving Show

compId :: CompS -> CompId
compId (CompS n _ _ _ _) = n
compName :: CompS -> PrimName
compName (CompS _ nm _ _ _) = nm
compIns :: CompS -> [Input]
compIns (CompS _ _ ins _ _) = ins
compOuts :: CompS -> [Output]
compOuts (CompS _ _ _ outs _) = outs

instance Eq CompS where (==) = (==) `on` compId
instance Ord CompS where compare = compare `on` compId

type DGraph = [CompS]

type Dot = String

type Depth = Int

uuGraph :: UU -> DGraph
uuGraph = trimDGraph
        -- . connectState
        . mendG
        . map simpleComp
        -- . (\ z -> trace ("runU result: " ++ show z) z)
        . runU
        -- . trace "uuGraph" id

circuitGraph :: (GenBuses a, Ok2 (:>) a b) => (a :> b) -> DGraph
circuitGraph = uuGraph . unitize

type CompDepths = Map CompS Depth

-- | Longest paths excluding delay/Cons elements.
longestPaths :: DGraph -> CompDepths
longestPaths g = distances
 where
   sComp = sourceComp g
   distances :: Map CompS Depth
   distances = M.fromList ((id &&& dist) <$> g)
   memoDist, dist :: CompS -> Depth
   memoDist = (distances M.!)
   -- Greatest distances a starting point.
   dist c | isStart c = 0
          | otherwise = 1 + maximumD ((memoDist . sComp) <$> compIns c)
   isStart c = null (compIns c) || isDelay c

-- longestPath is adapted from the linear-time algorithm for *acyclic* longest
-- path, using lazy evaluation in place of (explicit) topological sort. See
-- <https://en.wikipedia.org/wiki/Longest_path_problem#Acyclic_graphs_and_critical_paths>.

-- Note: if we measured the depth *before* mending, we wouldn't have to be take
-- care about cycles.

maximumD :: [Depth] -> Depth
maximumD [] = 0
maximumD ds = maximum ds

-- Greatest depth over components with outputs
longestPath :: CompDepths -> Depth
longestPath = maximumD . M.elems . withOuts
 where
   withOuts = M.filterWithKey (\ c _ -> not (null (compOuts c)))

isDelay :: CompS -> Bool
isDelay = isJust . unDelayName . compName

-- #define SkipTrim

-- Remove unused components.
-- Depth-first search from the "Out" component.
-- Explicitly include other outer prims as well, in case any are ignored.
trimDGraph :: Unop DGraph
#ifdef SkipTrim
trimDGraph = id
#else

type Trimmer = State (S.Set CompS) ()

trimDGraph g = S.elems $ execState (mapM_ searchComp outComps) S.empty
 where
   outComps = filter (isOut . compName) g
   sComp = sourceComp g
   searchComp :: CompS -> Trimmer
   searchComp c =
    do seen <- M.gets (S.member c)
       unless seen $
         do M.modify (S.insert c)
            mapM_ (searchComp . sComp) (compIns c)
   isOut = isJust . stripPrefix "Out"

-- It's important that comps is outside of the o lambda, so that it gets
-- computed just once for g.

#endif

sourceComp :: DGraph -> (Output -> CompS)
sourceComp g = \ o -> fromMaybe (error (msg o)) (M.lookup o comps)
 where
   msg o = printf "sourceComp: mystery output %s in graph %s."
             (show o) (show g)
   comps = foldMap (\ c -> M.fromList [(o,c) | o <- compOuts c]) g

-- The pred eliminates counting both In (constants) *and* Out.

graphDot :: String -> [Attr] -> CompDepths -> Dot
graphDot name attrs depths =
  printf "digraph %s {\n%s}\n" (tweak <$> name)
         (concatMap wrap (prelude ++ recordDots depths))
 where
   prelude = [ "margin=0"
             , "rankdir=LR"
             , "node [shape=Mrecord]"
             , "bgcolor=transparent"
             , "nslimit=20"  -- helps with very large rank graphs
             -- , "ratio=1"
             -- , "ranksep=1.0"
             -- , fixedsize=true
             ] ++ [a ++ "=" ++ show v | (a,v) <- attrs]
   wrap  = ("  " ++) . (++ ";\n")
   tweak '-' = '_'
   tweak c   = c

type Statement = String

simpleComp :: (Comp,Reuses) -> CompS
simpleComp (Comp n prim a b,reuses) =
  CompS n name
    (sourceBus <$> flattenBHack name prim a)
    (sourceBus <$> flattenB     name      b)
    reuses
 where
   name = show prim

-- simpleComp (n, (Comp prim a b,reuses)) = CompS n name (flat a) (flat b) reuses
--  where
--    name = show prim
--    flat :: forall t. Buses t -> [Bus]
--    flat = map sourceBus . flattenBHack name prim


-- Working here in converting away from flattening


data Dir = In | Out deriving Show
type PortNum = Int

-- -- For more succinct labels, so as not to stress Graphviz so much.
-- -- TODO: also compact the port numbers to base 64.
-- instance Show Dir where
--   show In  = "I"
--   show Out = "O"

taggedFrom :: Int -> [a] -> [(Int,a)]
taggedFrom n = zip [n ..]

tagged :: [a] -> [(Int,a)]
tagged = taggedFrom 0

hideNoPorts :: Bool
hideNoPorts = False

type SourceInfo = (Ty,CompId,PortNum,Depth)

-- Map each pin to its info about it
type SourceMap = Map PinId SourceInfo

-- TODO: Drop the comps argument, as it's already in depths

recordDots :: CompDepths -> [Statement]
recordDots depths = nodes ++ edges
 where
   comps = M.keys depths
   nodes = node <$> comps
    where
      node :: CompS -> String
      node (CompS nc prim ins outs _) =
        printf "%s%s [label=\"{%s%s%s}\"%s]" prefix (compLab nc) 
          (ports "" (labs In ins) "|")
          (escape prim)
          (ports "|" (labs Out outs) "")
          extras
       where
         extras | prim == unknownName = ",fontcolor=red,color=red,style=bold"
                | otherwise = ""
         prefix =
           if hideNoPorts && null ins && null outs then "// " else ""
         ports _ "" _ = ""
         ports l s r = printf "%s{%s}%s" l s r
         labs :: Dir -> [Bus] -> String
         -- Labels. Use Dot string concat operator to avoid lexer buffer size limit.
         -- See https://github.com/ellson/graphviz/issues/71 .
         labs dir bs = segmentedDotString $
                       intercalate "|" (portSticker <$> tagged bs)
          where
            portSticker :: (Int,Bus) -> String
            portSticker (p,b) =
                 bracket (portLab dir p) ++ showDepth b
         -- Escape angle brackets, "|", and other non-ascii
         escape :: Unop String
         escape [] = []
         escape (c:cs) = mbEsc (c : escape cs)
          where
             mbEsc | (c `elem` "<>|{}") || not (isAscii c)  = ('\\' :)
                   | otherwise     = id
   showDepth :: Bus -> String
#ifdef ShowDepths
   showDepth ((srcMap M.!) . busId -> (_,_,_,d)) = show d
#else
   showDepth _ = ""
#endif
   bracket = ("<"++) . (++">")
   portLab :: Dir -> PortNum -> String
   portLab dir np = printf "%s%d" (show dir) np
   srcMap = sourceMap (M.toList depths)
   edges = concatMap compEdges comps
    where
      compEdges _c@(CompS cnum _ ins _ _) = edge <$> tagged ins
       where
         edge (ni, Bus i t) =
           -- Show the type per edge. I think I'd rather show in the output
           -- ports, but I don't know how to use a small font for those port
           -- labels but not for the operation label.
           printf "%s -> %s [%s]"
             (port Out (ocnum,opnum)) (port In (cnum,ni))
             (intercalate "," attrs)
          where
            (_w,ocnum,opnum,_d) = srcMap M.! i
            attrs = label ++ constraint
#ifdef ShallowDelay
            constraint | isDelay _c = ["constraint=false" ]
                       | otherwise  = []
#else
            constraint = []
#endif
#ifdef NoBusLabel
            label = []
#else
            -- label | t == Bool = []
            label = [printf "label=%s,fontsize=8,fontcolor=indigo" (show t)]
#endif
   port :: Dir -> (CompId,PortNum) -> String
   port dir (cnum,np) =
     printf "%s:%s" (compLab cnum) (portLab dir np)
   compLab nc = 'c' : show nc

segmentedDotString :: Unop String
segmentedDotString = intercalate "\"+\"" . divvy
 where
   divvy [] = []
   divvy (splitAt yy_buf_size -> (pre,suf)) = pre : divvy suf
   yy_buf_size = 16370 -- 16384 - some overhead

-- showBool :: Bool -> String
-- showBool False = "F"
-- showBool True  = "T"


sourceMap :: [(CompS,Depth)] -> SourceMap
sourceMap = foldMap $ \ (comp,depth) ->
              M.fromList [ (p,(wid,compId comp,np,depth))
                         | (np,Bus p wid) <- tagged (compOuts comp) ]

{-

-- Stateful addition via StateFun

outSG :: (IsSourceP s, IsSourceP2 a b, StateCatWith sk (:>) s) =>
         String -> (a `sk` b) -> IO ()
outSG name = outG name . runState

type (:->) = StateFun (:>) Bool

-}

{-

-- TODO: Revisit this whole line of thinking now that I have a ClosedCat instance for (:>)

{--------------------------------------------------------------------
    Temporary hack for StateExp
--------------------------------------------------------------------}

-- For ClosedCat, we'll use tries.

-- instance ClosedCat (:>) where
--   type Exp (:>) u v = u :->: v
--   type ClosedKon (:>) u = HasTrie u
--   apply = muxC
--   curry = undefined
--   uncurry = undefined

--     Could not deduce (IsSource (Buses b),
--                       IsSource (Buses a),
--                       IsSource (Buses (Trie a b)))
--       arising from a use of `muxC'

{-
newtype a :> b = Circ (Kleisli CircuitM (Buses a) (Buses b))

apply   :: ((a :->: b) :* a) :> b
curry   :: ((a :* b) :> c) -> (a :> (b :->: c))
uncurry :: (a :> (b :->: c)) -> (a :* b) :> c
-}

--   apply   :: ClosedKon k a => (Exp k a b :* a) `k` b
--   curry   :: ClosedKon k b => ((a :* b) `k` c) -> (a `k` Exp k b c)
--   uncurry :: ClosedKon k b => (a `k` Exp k b c) -> (a :* b) `k` c

applyC :: ( HasTrie a, IsSource2 a b, IsSource (a :->: b) ) =>
          ((a :->: b) :* a) :> b
applyC = muxC

curryC :: ( HasTrie b, Show (b :->: b), CTraversableWith (Trie b) (:>)
          , IsSource (b :->: b)
          -- , StrongCat (:>) (Trie b), StrongKon (:>) (Trie b) a b
          , b ~ bool
          ) => 
          ((a :* b) :> c) -> (a :> (b :->: c))
curryC = traverseCurry idTrie

-- TODO: Give StrongCat instance and drop constraint the Strong or bool
-- constraint above.

-- uncurryC :: (a :> (b :->: c)) -> (a :* b) :> c

uncurryC :: (HasTrie b, IsSource2 b c, IsSource (b :->: c)) =>
            (a :> (b :->: c)) -> ((a :* b) :> c)
uncurryC h = applyC . first h

{-

h :: a :> (b :->: c)
first h :: (a :* b) :> ((b :->: c) :* b)
apply . first h :: (a :* b) :> c

-}

-- instance ClosedCatU k s => StateCat (StateExp k s) where
--   type StateKon  (StateExp k s) = ClosedKon k s
--   type StateBase (StateExp k s) = k
--   type StateT    (StateExp k s) = s
--   state    f  = StateExp (curry (f . swapP))
--   runState st = uncurry (unStateExp st) . swapP


infixr 1 :+>
-- Temporary specialization of StateExp to (:>) and bool
newtype (a :+> b) =
  BStateExp { unBStateExp :: a :> (bool :->: (b :* bool)) }

pureBState :: (a :> b) -> a :+> b
pureBState f = bstate (swapP . second f)

inBState :: (s ~ t, s ~ bool, IsSource b) =>
            (((s :* a) :> (b :* s)) -> ((t :* c) :> (d :* t)))
         -> (a :+> b                -> c :+> d)
inBState = bstate <~ runBState

inBState2 :: (s ~ t, u ~ s, s ~ bool, IsSource b, IsSource d) =>
             (((s :* a) :> (b :* s)) -> ((t :* c) :> (d :* t)) -> ((u :* e) :> (f :* u)))
         -> (a :+> b                -> c :+> d                -> e :+> f)
inBState2 = inBState <~ runBState


-- Oh. I don't think I can define a Category instance, because of the IsSource
-- constraints.


-- Temporary specialization of state and runState

bstate :: (s ~ bool) =>
          (s :* a) :> (b :* s) -> a :+> b
bstate f  = BStateExp (curryC (f . swapP))

runBState :: (s ~ bool, IsSource b) =>
             a :+> b -> (s :* a) :> (b :* s)
runBState st = uncurryC (unBStateExp st) . swapP

-- | Full adder with 'StateCat' interface
fullAddBS :: Pair bool :+> bool
fullAddBS = bstate fullAdd

-- | Structure adder with 'StateCat' interface
addBS :: CTraversableWith t (:+>) =>
         t (Pair bool) :+> t bool
addBS = traverseC fullAddBS

outBSG :: IsSource2 a b =>
          String -> (a :+> b) -> IO ()
outBSG name = outG name . runBState

type AddBS f = f (Pair bool) :+> f bool

type AddVBS n = AddBS (Vec  n)
type AddTBS n = AddBS (Tree n)

addVBS1 :: AddVBS N1
addVBS1 = addBS

-- addVBS2 :: AddVBS N2
-- addVBS2 = addBS

addTBS1 :: AddTBS N1
addTBS1 = addBS

-}

{--------------------------------------------------------------------
    Another pass at ClosedCat
--------------------------------------------------------------------}

{-
type family Unpins a

type instance Unpins PinId = Bool

-- Everything else distributes:
type instance Unpins ()         = ()
type instance Unpins ( a :* b ) = Unpins a :* Unpins b
type instance Unpins (Pair a  ) = Pair (Unpins a)
type instance Unpins (Vec n a ) = Vec  n (Unpins a)
type instance Unpins (Tree n a) = Tree n (Unpins a)

distribMF :: Monad m => m (p -> q) -> (p -> m q)
distribMF u p = liftM ($ p) u

-- instance ClosedCat (:>) where
--   type ClosedKon (:>) u =
--     (IsSource u, HasTrie (Unpins u), Traversable (Trie (Unpins u)))
--   type Exp (:>) u v = Unpins u :->: v
--   apply = muxC

--     Could not deduce (IsSource b, IsSource (Trie (Unpins a) b))
--       arising from a use of `muxC'



--   curry   = inNew $ \ f -> sequence . trie . curry f
--   uncurry = inNew $ \ h -> uncurry (distribMF . liftM untrie . h)

--   apply   :: ClosedKon k a => (Exp k a b :* a) `k` b
--   curry   :: ClosedKon k b => ((a :* b) `k` c) -> (a `k` Exp k b c)
--   uncurry :: ClosedKon k b => (a `k` Exp k b c) -> (a :* b) `k` c

  apply   :: ClosedKon (:>) a => ((Unpins a :->: b) :* a) :> b
  curry   :: ClosedKon (:>) b => ((a :* b) :> c) -> (a :> (Unpins b :->: c))
  uncurry :: ClosedKon (:>) b => (a :> (Unpins b :->: c)) -> ((a :* b) :> c)

uncurry untrie :: ((k :->: v) :* k) -> v
uncurry untrie :: ((Unpins a :->: b) :* Unpins a) -> b

-}

#if defined NoSums

-- type BusSum a b = ()

sumErr :: String -> a
sumErr str = error (str ++ " for (:>): not defined. Sorry")

instance CoproductCat (:>) where
  -- type Coprod (:>) = Either
  inl   = sumErr "inl"
  inr   = sumErr "inr"
  (|||) = sumErr "(|||)"

instance DistribCat (:>) where
  distl = sumErr "distl"
  distr = sumErr "distr"

#endif

#if defined StaticSums

type instance Buses (a :+ b) = Buses a :+ Buses b

instance CoproductCat (:>) where
  inl   = C inl
  inr   = C inr
  (|||) = inC2 (|||)

instance DistribCat (:>) where
  distl = C distl
  distr = C distr

{- Types:

Abbreviations:

> type KC = Kleisli CircuitM
> type S = Source

Consider `Source`- specialized versions of `KC`:

> inl :: KC (S a) (S a :+ S b)
>     == KC (S a) (S (a :+ b))
>     == a :+> a :+ b
>
> inr :: KC (S b) (S a :+ S b)
>     == KC (S b) (S (a :+ b))
>     == b :+> a :+ b
>
> (|||) :: KC (S a) (S c) -> KC (S b) (S c) -> KC (S a :+ S b) (S c)
>       == KC (S a) (S c) -> KC (S b) (S c) -> KC (S (a :+ b)) (S c)
>       == a :+> c -> b :+> c -> (a :+ b) :+> c
>
> distl :: KC (S a :* (S u :+ S v)) (S a :* S u :+ S a :* S v)
>       == KC (S (a :* (u :+ v))) (S (a :* u :+ a :* v))
>       == (a :* (u :+ v)) :+> (a :* u :+ a :* v)
>
> distr :: KC ((S u :+ S v) :* S b) (S u :* S b :+ S v :* S b)
>       == KC (S ((u :+ v) :* b)) (S (u :* b :+ v :* b))
>       == ((u :+ v) :* b) :+> (u :* b :+ v :* b)

-}

#elif defined TaggedSums

{--------------------------------------------------------------------
    Coproducts
--------------------------------------------------------------------}

-- Move elsewhere

infixl 6 :++

data a :++ b = UP { sumBuses :: Seq PinId, sumFlag :: PinId } deriving Show

type instance Buses (a :+ b) = Buses a :++ Buses b

instance IsSource2 a b => IsSource (a :++ b) where
  toBuses (UP ps f) = ps <> singleton f
  genSource =
    liftM2 UP (Seq.replicateM (numBuses (undefined :: (a :++ b)) - 1) newPinId)
              newPinId
  numBuses _ =
    (numBuses (undefined :: a) `max` numBuses (undefined :: b)) + 1

unsafeInject :: forall q a b. (IsSourceP q, IsSourceP2 a b) =>
                Bool -> q :> a :+ b
unsafeInject flag = mkCK $ \ q ->
  do x <- constM flag q
     let nq  = numBuses (undefined :: Buses q)
         na  = numBuses (undefined :: Buses a)
         nb  = numBuses (undefined :: Buses b)
         pad = Seq.replicate (max na nb - nq) x
     return (UP (toBuses q <> pad) x)

inlC :: IsSourceP2 a b => a :> a :+ b
inlC = unsafeInject False

inrC :: IsSourceP2 a b => b :> a :+ b
inrC = unsafeInject True

infixr 2 |||*

{-
(|||*) :: (IsSourceP2 a b, IsSourceP c) =>
          (a :> c) -> (b :> c) -> (a :+ b :> c)
f |||* g = muxC . ((f *** g) . extractBoth &&& pureC sumFlag)

cond :: IsSource (Buses c) => ((c :* c) :* Bool) :> c
cond = muxCT . first toPair

muxCT :: (IsSourceP2 ((u :->: v) :* u) v, HasTrie u) =>
         ((u :->: v) :* u) :> v
muxCT = namedC "mux"
-}

(|||*) :: (IsSourceP2 a b, IsSourceP c) =>
          (a :> c) -> (b :> c) -> (a :+ b :> c)
f |||* g = muxC . (pureC sumFlag &&& (f *** g) . extractBoth)

-- TODO: Reduce muxC to several one-bit muxes.

-- unsafeExtract :: IsSource (Buses c) => a :+ b :> c
-- unsafeExtract = pureC (pinsSource . sumBuses)

extractBoth :: IsSourceP2 a b => a :+ b :> a :* b
extractBoth = pureC ((pinsSource &&& pinsSource) . sumBuses)

pinsSource :: IsSource a => Seq PinId -> a
pinsSource pins = M.evalState genSource (toList pins)

pureC :: (Buses a -> Buses b) -> (a :> b)
pureC = C . arr

-- TODO: Generalize CoproductCat to accept constraints like IsSourceP, and then
-- move inlC, inrC, (|||*) into a CoproductCat instance. Tricky.

#elif defined ChurchSums

{--------------------------------------------------------------------
    Yet another sum experiment: Church encoding
--------------------------------------------------------------------}

type instance Buses (a :+ b) = PSum a b

newtype PSum a b =
  PSum { unPSum :: forall c. CondCat (:>) c => (a :=> c) :* (b :=> c) :> c }

psc :: (forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Buses c)) -> PSum a b
psc q = PSum (mkCK q)

unPsc :: PSum a b -> (forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Buses c))
unPsc ps = unmkCK (unPSum ps)

inlC :: a :> a :+ b
inlC = mkCK (\ a -> return (psc (\ (f,_) -> unmkCK f a)))

inrC :: b :> a :+ b
inrC = mkCK (\ b -> return (psc (\ (_,g) -> unmkCK g b)))

infixr 2 |||*

(|||*) :: forall a b c. CondCat (:>) c =>
          (a :> c) -> (b :> c) -> (a :+ b :> c)
f |||* g = mkCK (\ q -> unPsc q (f,g))

distlC :: forall u a b. (u :* (a :+ b)) :> (u :* a :+ u :* b)
distlC = mkCK (\ (u,q) -> return (psc (\ (f,g) -> unPsc q (injl u f, injl u g))))

{-
u :: Buses u
q :: Buses (a :+ b)
  == PSum a b
unPSum q :: forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Buses c)

f :: u :* a :> c
g :: u :* b :> c

injl u f :: a :> c
injl u g :: b :> c

unPSum q (injl u f) (injl v f) :: CircuitM (Buses c)

-}

distrC :: forall v a b. ((a :+ b) :* v) :> (a :* v :+ b :* v)
distrC = mkCK (\ (q,v) -> return (psc (\ (f,g) -> unPsc q (injr v f, injr v g))))

injl :: Buses u -> (u :* a :> c) -> (a :> c)
injl u = inCK (. (u,))

injr :: Buses v -> (a :* v :> c) -> (a :> c)
injr v = inCK (. (,v))

-- (. (u,)) :: (Buses (u :* a) -> CircuitM (Buses c)) -> (Buses a -> CircuitM (Buses c))
-- inCK (. (u,)) :: (u :* a : c) -> (a :> c)

#if 0
instance                        CondCat (:>) ()      where cond = it
instance                        CondCat (:>) Bool      where cond = mux
instance (CondCat2 (:>) a b) => CondCat (:>) (a :*  b) where cond = prodCond
instance (CondCat (:>) b)    => CondCat (:>) (a :=> b) where cond = funCond
instance CondCat (:>) (a :+ b)                         where cond = sumCond
#endif

sumToFun' :: (t :> a :+ b)
          -> forall c. CondCat (:>) c => t :> ((a :=> c) :* (b :=> c) :=> c)
sumToFun' = (inCK.fmap.fmap) unPSum

sumToFun :: forall a b c. CondCat (:>) c => (a :+ b :> ((a :=> c) :* (b :=> c) :=> c))
sumToFun = sumToFun' id

-- sumToFun = (inCK.fmap.fmap) unPSum (id :: a :+ b :> a :+ b)

funToSum' :: forall t a b.
             (forall c. CondCat (:>) c => t :> ((a :=> c) :* (b :=> c) :=> c))
          -> (t :> a :+ b)
funToSum' q = mkCK (return . foo)
 where
   foo :: Buses t -> Buses (a :+ b)
   foo t = PSum (mkCK r)
    where
      r :: forall c. CondCat (:>) c => (a :> c) :* (b :> c) -> CircuitM (Buses c)
      r fg = do h <- unmkCK q t
                unmkCK h fg

#if 0

q :: forall c. CondCat (:>) c => t :> ((a :=> c) :* (b :=> c) :=> c)

unmkCK q :: forall c. CondCat (:>) c => Buses t -> CircuitM (Buses ((a :=> c) :* (b :=> c) :=> c))
         :: forall c. CondCat (:>) c => Buses t -> CircuitM ((a :=> c) :* (b :=> c) :> c)

fg :: (a :> c) :* (b :> c)

unmkCK q t :: forall c. CondCat (:>) c => CircuitM ((a :=> c) :* (b :=> c) :> c)
h :: (a :=> c) :* (b :=> c) :> c
unmkCK h :: (a :> b) :* (b :> c) -> CircuitM (Buses c)
unmkCK h fg :: CircuitM (Buses c)

#endif

type CondArr a = Bool :* (a :* a) :> a
type CondFun a = forall t. (t :> Bool) -> Binop (t :> a)

condArrToFun :: CondArr a -> CondFun a
condArrToFun condArr p q r = condArr . (p &&& (q &&& r))

condFunToArr :: CondFun a -> CondArr a
condFunToArr condFun = condFun exl (exl . exr) (exr . exr)

cond' :: CondCat (:>) a => CondFun a
cond' = condArrToFun cond
-- cond' p q r = cond . (p &&& (q &&& r))

-- cond'' :: CondCat a => CondArr a
-- cond'' = condFunToArr cond'
-- -- cond'' = cond' exl (exl . exr) (exr . exr)

sumCond' :: (t :> Bool) -> Binop (t :> a :+ b)
sumCond' p q r = funToSum' (cond' p (sumToFun' q) (sumToFun' r))
-- sumCond' p q r = funToSum' (condArrToFun cond p (sumToFun' q) (sumToFun' r))
-- sumCond' p q r = funToSum' (cond . (p &&& (sumToFun' q &&& sumToFun' r)))

sumCond :: Bool :* ((a :+ b) :* (a :+ b)) :> a :+ b
sumCond = condFunToArr sumCond'
-- sumCond = sumCond' exl (exl . exr) (exr . exr)
-- sumCond = funToSum' (cond . (exl &&& (sumToFun' (exl . exr) &&& sumToFun' (exr . exr))))

-- The CondCat (:>) constraint in cond as used in 'fromBool' is what leads to CondCat in
-- PSum and hence breaks (|||). I'm looking for an alternative.

fromBool :: Bool :> () :+ ()
fromBool = cond . (id &&& (inl &&& inr) . it)

toBool :: () :+ () :> Bool
toBool = constC False |||* constC True

instance CoproductCat (:>) where
  inl   = inlC
  inr   = inrC
  (|||) = error "(|||) for (:>): Sorry -- no unconstrained method yet. Use (|||*)"

instance DistribCat (:>) where
  distl = distlC
  distr = distrC

#endif

#if 0

instance DelayCat (:>) where
  type DelayKon (:>) s = GenBuses s
  delayC = delay

{--------------------------------------------------------------------
    Mealy machines
--------------------------------------------------------------------}

data MealyC a b = forall s. GenBuses s => MealyC (a :* s :> b :* s) s

#if 0

loop :: (a :* c :> b :* c) -> (a :> b)
loop (C f) = C (loop (arr unPairB . f . arr (uncurry PairB)))

#ifdef TypeDerivation
f :: KC (Buses (a :* c)) (Buses (b :* c))
arr (uncurry PairB) :: KC (Buses a :* Buses c) (Buses (a :* c))
arr unPairB :: KC (Buses (b :* c)) (Buses b :* Buses c)
arr unPairB . f . arr (uncurry PairB)
 :: KC (Buses a :* Buses c) (Buses b :* Buses c)
#endif

-- I'm getting a <<loop>> (black hole).
-- Try some experiments

#else

instance LoopCat (:>) where
  type LoopKon (:>) s = GenBuses s
  loopC h = mkCK f
   where
     f a = do PinId n  <- newPinId         -- really newPatchId
              sIn      <- genRip "In" n UnitB
              (b,sOut) <- unPairB <$> unmkCK h (PairB a sIn)
              ()       <- unUnitB <$> genRip "Out" n sOut
              return b

-- TODO: Replace "rip" with a word that suggests needing to be riped later.

ripPrefix :: String -> String
ripPrefix pre = pre++"Rip "

genRip :: GenBuses v => String -> Int -> BCirc u v
genRip pre n = genComp (Prim (ripName pre n))

ripName :: String -> Int -> String
ripName pre n = ripPrefix pre ++ show n
mendG :: Unop DGraph
#if defined NoMend
mendG = id
#else
mendG = fixRips . extractRips

unRipName :: String -> String -> Maybe Int
unRipName pre (stripPrefix (ripPrefix pre) -> Just (Read n)) = Just n
unRipName _ _ = Nothing

pattern InRip :: Int -> String
pattern InRip  n <- (unRipName "In"  -> Just n)

pattern OutRip :: Int -> String
pattern OutRip n <- (unRipName "Out" -> Just n)

type Unripped = (DGraph, (Map Int [Output], Map Int [Input]))

extractRips :: DGraph -> Unripped
extractRips = foldr extract mempty
 where
   extract :: CompS -> Unop Unripped
   extract (CompS _ (InRip  r) [] os _) = (second.first ) (M.insert r os)
   extract (CompS _ (OutRip r) is [] _) = (second.second) (M.insert r is)
   extract c                            = first (c :)

-- data CompS = CompS CompId PrimName [Input] [Output] Reuses

#endif

patchMap :: (Map Int [Output], Map Int [Input]) -> Map Output Input
patchMap oi =
  M.unions ((M.fromList . uncurry zip) <$> M.elems (uncurry mapZip oi))

fixRips :: Unripped -> DGraph
fixRips (g, patchMap -> pm) = map patchC g
 where
   patchC :: Unop CompS
   patchC = (onInputs.fmap) patchIn
   patchIn :: Unop Bus
   patchIn b = fromMaybe b (M.lookup b pm)

onInputs :: Unop [Input] -> Unop CompS
onInputs f (CompS n p i o m) = CompS n p (f i) o m

mapZip :: Ord k => Map k a -> Map k b -> Map k (a,b)
mapZip as bs = M.mapWithKey (\ k a -> (a,bs M.! k)) as

-- TODO: Consider more efficient mapZip alternatives. On the other hand, I
-- expect the maps to be very small, usually having only zero or one element.

#endif

mealyAsArrow :: MealyC a b -> (a :> b)
mealyAsArrow (MealyC f s0) = loopC (f . second (delay s0))

unitizeMealyC :: GenBuses a => MealyC a b -> UU

#ifdef MealyToArrow
unitizeMealyC = unitize . mealyAsArrow
#else
unitizeMealyC = unitizeLoopC . preLoopC

-- Ready for loop.
data LoopC a b = forall s. GenBuses s => LoopC (a :* s :> b :* s)

-- Like mealyAsArrow but without the loop.
preLoopC :: GenBuses a => MealyC a b -> LoopC a b
preLoopC (MealyC f s0) = LoopC (f . second (delay s0))

unitizeLoopC :: GenBuses a => LoopC a b -> UU
unitizeLoopC (LoopC f) = undup . f' . dup
 where
   f' = (namedC "Out" *** namedC "NewState")
      . f
      . (namedC "In"  *** namedC "OldState")
   undup :: () :* () :> ()
   undup = it

#endif

#else
mendG :: Unop DGraph
mendG = id
#endif

outerPrims :: [PrimName]
outerPrims = ["In","Out", "OldState","NewState"]

isOuterPrim :: PrimName -> Bool
isOuterPrim = flip S.member (S.fromList outerPrims)

{--------------------------------------------------------------------
    Type-specific support
--------------------------------------------------------------------}

-- GenBuses needed for data types appearing the external interfaces (and hence
-- not removed during compilation).

genBusesRep' :: (TypeableAR a, GenBuses (Rep a)) =>
                String -> Sources -> BusesM (Buses a)
genBusesRep' prim ins = abstB <$> genBuses' prim ins

-- tweakValRep :: (HasRep a, Tweakable (Rep a)) => Unop a
-- tweakValRep = abst . tweakVal . repr

tyRep :: forall a. GenBuses (Rep a) => a -> Ty
tyRep = const (ty (undefined :: Rep a))

delayCRep :: (HasRep a, TypeableAR a, GenBuses (Rep a)) => a -> (a :> a)
delayCRep a0 = abstC . delay (repr a0) . reprC

#include "AbsTy.inc"

AbsTy((a,b,c))
AbsTy((a,b,c,d))
AbsTy(Maybe a)  -- Problematic ConstCat. See 2016-01-13 notes.
-- AbsTy(Either a b)
AbsTy(Complex a)

-- Moving types to ShapedTypes

-- AbsTy(Pair a)  -- See below
-- AbsTy(RTree.Tree Z a)
-- AbsTy(RTree.Tree (S n) a)
-- AbsTy(LTree.Tree Z a)
-- AbsTy(LTree.Tree (S n) a)
-- AbsTy(Rag.Tree LU a)
-- AbsTy(Rag.Tree (BU p q) a)
-- AbsTy(Vec Z a)
-- AbsTy(Vec (S n) a)
-- TODO: Remove Vec instances & import. Switching to ShapedTypes.Vec
-- Newtypes. Alternatively, don't use them in external interfaces.

AbsTy(Sum a)
AbsTy(Product a)
AbsTy(All)
AbsTy(Any)

-- TODO: Rework instances for Vec n as well, since it has the same redundancy
-- issue as Pair, in a subtler form. Probably also Ragged.

-- Better yet, rework the Pair instances in a more generic form, e.g., using
-- Traversable for genBuses', so that they become easy to generalize and apply
-- easily and efficiently to Vec n and others.

AbsTy(G.U1 p)
AbsTy(G.Par1 p)
AbsTy(G.K1 i c p)
AbsTy(G.M1 i c f p)
AbsTy((G.:+:) f g p)
AbsTy((G.:*:) f g p)
AbsTy((G.:.:) f g p)

AbsTy(M.Identity a)
AbsTy(M.ReaderT e m a)
AbsTy(M.WriterT w m a)
AbsTy(M.StateT s m a)

-- I put the following two here instead of in LinearRow and LinearCol to avoid
-- the GHCi problem with this module.
AbsTy(LR.L s a b)
AbsTy(LC.L s a b)
