{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE CPP #-}

-- #define NoOptimizeCircuit

-- #define NoHashCons

-- #define NoIfBotOpt
-- #define NoIdempotence

-- -- Improves hash consing, but can obscure equivalent circuits
-- #define NoCommute

-- #define NoBusLabel

#define MealyToArrow

-- -- Whether a delay/cons element is considered further from input
-- #define ShallowDelay

-- #define NoMend

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

-- {-# OPTIONS_GHC -fdefer-typed-holes #-}  -- TEMP
-- {-# OPTIONS_GHC -fdefer-type-errors #-}  -- TEMP

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
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

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
  , Bus(..),Comp(..),Input,Output, Ty(..), busTy, Source(..), Template(..)
  , GenBuses(..), GS, genBusesRep', tyRep, bottomRep
  -- , delayCRep, unDelayName
  , namedC, constC -- , constS
  , genUnflattenB'
  , SourceToBuses(..), CompS(..), simpleComp
  , mkGraph
  , Attr
  , writeDot, displayDot,Name,Report,Graph
  -- , simpleComp
  , tagged
  , systemSuccess
  -- For AbsTy
  , BusesM, abstB,abstC,reprC,Buses(..)
  , OkCAR
  -- , Ty(..)
  ) where

import Prelude hiding (id,(.),curry,uncurry,const,sequence,zip)

import Data.Monoid ({-mempty,-}(<>),Sum,Product,All,Any)
-- import Data.Newtypes.PrettyDouble
-- import Data.Functor ((<$>))
import Control.Applicative ({-Applicative(..),-}liftA2)
import Control.Monad (unless)
import Control.Arrow (arr,Kleisli(..))
import Data.Foldable ({-foldMap,-}toList)
import qualified GHC.Generics as G
import Data.Functor.Classes (Show1,showsPrec1)
import Data.Void (Void)
import Data.Function (on)
import Data.Maybe (fromMaybe,isJust,maybeToList)
import Data.List (intercalate,group,sort,stripPrefix)
import Data.Char (isAscii)
import Data.Complex (Complex)
import Data.Proxy (Proxy(..))
import GHC.TypeLits (natVal)
#ifndef MealyToArrow
import Data.List (partition)
#endif
import Data.Map (Map)
import qualified Data.Map as M  -- accidental qualifier clash with mtl. Change one.
-- import Data.Set (Set)
import qualified Data.Set as S
import Data.Sequence (Seq,singleton)
import Text.Printf (printf)
import Debug.Trace (trace)
-- import Data.Coerce                      -- TODO: imports
import Unsafe.Coerce
-- import GHC.Exts (Coercible) -- ,coerce
import Data.Typeable (TypeRep,Typeable,eqT,cast) -- ,Proxy(..),typeOf
import Data.Type.Equality ((:~:)(..))

import Data.Constraint (Dict(..),(:-)(..))
import Data.Pointed (Pointed)
import Data.Key (Zip(..))
import Data.Distributive (Distributive)
import Data.Distributive (distribute)
import Data.Functor.Rep (Representable(tabulate,index))
import qualified Data.Functor.Rep as R
import Data.Vector.Sized (Vector)

import qualified System.Info as SI
import System.Process (system) -- ,readProcess
import System.Directory (createDirectoryIfMissing)
import System.Exit (ExitCode(ExitSuccess))

#ifdef VectorSized
import GHC.TypeLits (Nat,KnownNat)
import Data.Finite (Finite)
#endif

-- mtl
import Control.Monad.State (State,execState,StateT)

-- For AbsTy
import qualified Data.Functor.Identity as M
import qualified Control.Monad.Trans.Reader as M
import qualified Control.Monad.Trans.Writer as M
import qualified Control.Monad.State as M

-- import TypeUnary.Vec hiding (get)

import ConCat.Misc ((:*),(:+),Unop,Binop,Yes1,typeR,transpose)
-- import ConCat.Complex (Complex(..))
import ConCat.Rep
import ConCat.Additive (Additive(..),Add)
import ConCat.Category  -- AltCat instead?
import qualified ConCat.AltCat  -- for AbsTy
import qualified ConCat.AltCat as A
import ConCat.AltCat (Uncurriable(..),funIf,repIf,unitIf,prodIf)

{--------------------------------------------------------------------
    Buses
--------------------------------------------------------------------}

-- Component (primitive) type
data Ty = Void | Unit | Bool | Int | Integer | Float | Double
        | Finite Integer  -- Remove?
        | Vector Integer Ty
        | Prod Ty Ty
        | Sum Ty Ty
        | Fun Ty Ty
  deriving (Eq,Ord)

instance Show Ty where
  showsPrec _ Void    = showString "Void"
  showsPrec _ Unit    = showString "()"
  showsPrec _ Bool    = showString "Bool"
  showsPrec _ Int     = showString "Int"
  showsPrec _ Integer = showString "Integer"
  showsPrec _ Float   = showString "Float"
  showsPrec _ Double  = showString "Double" -- "R"
  showsPrec p (Sum a b) = showParen (p >= 6) $
    showsPrec 6 a . showString " + " . showsPrec 6 b
  showsPrec p (Prod a b) = showParen (p >= 7) $
    showsPrec 7 a . showString " × " . showsPrec 7 b
  showsPrec p (Finite n) = showParen (p >= 9) $
    showString "Finite " . showsPrec 9 n
  showsPrec p (Vector n b) = showParen (p >= 9) $
    showString "Vector " . showsPrec 9 n . showString " " . showsPrec 9 b
  showsPrec p (Fun a b) = showParen (p >= 1) $
    showsPrec 1 a . showString " → " . showsPrec 0 b

-- Data bus: component id, output index, type; *or* subgraph ID
data Bus = Bus CompId Int Ty deriving Show

type Input  = Bus
type Output = Bus

-- Identifying information for a bus. Faster comparisons without the type.
busId :: Bus -> (CompId,Int)
busId (Bus c o _) = (c,o)

busTy :: Bus -> Ty
busTy (Bus _ _ t) = t

instance Eq  Bus where (==) = (==) `on` busId
instance Ord Bus where compare = compare `on` busId

-- type Sources = [Source]

-- | An information source: its bus and a description of its construction, which
-- contains the primitive and argument sources.
data Source = forall a b. Source Bus (Template a b) [Source]

pattern PSource :: Bus -> PrimName -> [Source] -> Source
pattern PSource b p ss = Source b (Prim p) ss

deriving instance Show Source

sourceBus :: Source -> Bus
sourceBus (Source b _ _) = b

instance Eq  Source where (==) = (==) `on` sourceBus
instance Ord Source where compare = compare `on` sourceBus

newBus :: Ty -> Int -> CircuitM Bus
newBus t o = -- trace "newBus" $
              (\ c -> Bus c o t) <$> M.gets fst

newSource ::  Ty -> Template a b -> [Source] -> Int -> CircuitM Source
newSource t templ ins o = -- trace "newSource" $
                         (\ b -> Source b templ ins) <$> newBus t o

{--------------------------------------------------------------------
    Buses representing a given type
--------------------------------------------------------------------}

-- | Typed aggregate of buses. @'Buses' a@ carries a value of type @a@.
-- 'AbstB' is for isomorphic forms. Note: b must not have one of the standard
-- forms. If it does, we'll get a run-time error when consuming.
data Buses :: * -> * where
  UnitB    :: Buses ()
  PrimB    :: Source -> Buses b
  ProdB    :: Ok2 (:>) a b => Buses a -> Buses b -> Buses (a :* b)
  IxProdB  :: (OkIxProd (:>) h, Show1 h, Foldable h, Ok (:>) a) => h (Buses a) -> Buses (h a)
  -- FunB     :: SubgraphId -> Buses (a -> b)
  ConvertB :: Ok2 (:>) a b => Buses a -> Buses b
  -- AbstB :: Buses (Rep b) -> Buses b

-- deriving instance Show (Buses a) -- not with IxProdB

instance Show (Buses a) where
  showsPrec _ UnitB        = showString "UnitB"
  showsPrec p (PrimB s)    = showsApp1 p "PrimB" s
  showsPrec p (ProdB a b)  = showsApp2 p "ProdB" a b
  showsPrec p (IxProdB as) = showsAppF p "IxProdB " as
  showsPrec p (ConvertB a) = showsApp1 p "ConvertB " a

-- TODO: use operations from Data.Functor.Classes, such as showsUnaryWith.
-- Give a Show1 instance for Buses in the style below, and then use
-- 
--   showsPrec1 :: (Show1 f, Show a) => Int -> f a -> ShowS

{- From Data.Functor.Classes:

> data T f a = Zero a | One (f a) | Two a (f a)

a standard 'Read1' instance may be defined as

> instance (Read1 f) => Read1 (T f) where
>     liftReadsPrec rp rl = readsData $
>         readsUnaryWith rp "Zero" Zero `mappend`
>         readsUnaryWith (liftReadsPrec rp rl) "One" One `mappend`
>         readsBinaryWith rp (liftReadsPrec rp rl) "Two" Two

and the corresponding 'Show1' instance as

> instance (Show1 f) => Show1 (T f) where
>     liftShowsPrec sp _ d (Zero x) =
>         showsUnaryWith sp "Zero" d x
>     liftShowsPrec sp sl d (One x) =
>         showsUnaryWith (liftShowsPrec sp sl) "One" d x
>     liftShowsPrec sp sl d (Two x y) =
>         showsBinaryWith sp (liftShowsPrec sp sl) "Two" d x y

-}

appParen :: Int -> Unop ShowS
appParen p = showParen (p >= 10)

shap :: Show a => a -> ShowS
shap a = showChar ' ' . showsPrec 10 a

showsApp1 :: Show a => Int -> String -> a -> ShowS
showsApp1 p f a = appParen p $ showString f . shap a

showsApp2 :: (Show a, Show b) => Int -> String -> a -> b -> ShowS
showsApp2 p f a b = appParen p $ showString f . shap a . shap b

showsAppF :: (Show1 h, Show a) => Int -> String -> h a -> ShowS
showsAppF p f as = appParen p $ showString f . showChar ' ' . showsPrec1 10 as

-- TODO: move these showsApp* functions elsewhere.

#if 0

-- Currently unused.
instance Eq (Buses a) where
  UnitB      == UnitB       = True
  PrimB s    == PrimB s'    = s == s'
  ProdB a b  == ProdB a' b' = a == a' && b == b'
  -- FunB _     == FunB _      = False             -- TODO: reconsider
  ConvertB a == ConvertB b  = case cast a of
                                Just a' -> a' == b
                                Nothing -> False
  _          == _           = False

-- If I need Eq, handle ConvertB. I'll probably have to switch to heterogeneous
-- equality, perhaps via `TestEquality` in `Data.Type.Equality`.

#endif

genBuses :: GenBuses b => Template a b -> [Source] -> CircuitM (Buses b)
genBuses templ ins = -- trace ("genBuses " ++ show templ ++ " " ++ show ins) $
                     M.evalStateT (genBuses' templ ins) 0

type BusesM = StateT Int CircuitM

class GenBuses a where
  genBuses' :: Template u v -> [Source] -> BusesM (Buses a)
  -- delay :: a -> (a :> a)
  ty :: Ty
  unflattenB' :: State [Source] (Buses a)

type GS a = (GenBuses a, Show a)

genBus :: (Source -> Buses a) -> Ty
       -> Template u v -> [Source] -> BusesM (Buses a)
genBus wrap t templ ins = seq (show t) $  -- * [Note seq]
                          -- seq t $
                          -- trace ("genBus " ++ show t) $
                          do o <- M.get
                             src <- M.lift (newSource t templ ins o)
                             M.put (o+1)
                             return (wrap src)

-- [Note seq]: Without this seq, I'm getting non-termination with
-- `id @(Vector 4 Bool :* Bool)`. I don't know why. seq t isn't enough.

unflattenB :: GenBuses a => [Source] -> Buses a
unflattenB sources | [] <- rest = a
                   | otherwise  = error ("unflattenB: extra sources " ++ show rest)
 where
   (a,rest) = M.runState unflattenB' sources

-- TODO: Remove this instance when we stop needing GenBuses for Vector index
instance GenBuses Void where
  genBuses' = error "genBuses' for Void"
  ty = Void
  unflattenB' = error "unflattenB' for Void"

instance GenBuses () where
  genBuses' _ _ = return UnitB
  -- delay () = id
  ty = Unit
  unflattenB' = return UnitB

-- delayPrefix :: String
-- delayPrefix = "Cons "
--               -- "delay "

-- delayName :: String -> String
-- delayName = (delayPrefix ++)

-- unDelayName :: String -> Maybe String
-- unDelayName = stripPrefix delayPrefix

-- isDelayTemplate :: Template a b -> Bool
-- isDelayTemplate = isJust . unDelayName . primName

genPrimBus :: forall a u v. GenBuses a => Template u v -> [Source] -> BusesM (Buses a)
genPrimBus = genBus PrimB (ty @a)

-- TODO: Combine genBus and genPrimBus.

-- flattenB :: GenBuses a => Buses a -> [Source]
-- flattenB = toList . flat
--  where
--    flat :: forall a. GenBuses a => Buses a -> Seq Source
--    flat UnitB        = mempty
--    flat (PrimB s)    = singleton s
--    flat (ProdB a b)  = flat a <> flat b
--    flat (ConvertB b) = flat b

unflattenPrimB :: GenBuses a => State [Source] (Buses a)
unflattenPrimB = do (s:ss) <- M.get
                    M.put ss
                    return (PrimB s)

instance GenBuses Bool where
  genBuses' = genPrimBus
  -- delay = primDelay
  ty = Bool
  unflattenB' = unflattenPrimB

instance GenBuses Int  where
  genBuses' = genPrimBus
  -- delay = primDelay
  ty = Int
  unflattenB' = unflattenPrimB

instance GenBuses Integer  where
  genBuses' = genPrimBus
  -- delay = primDelay
  ty = Integer
  unflattenB' = unflattenPrimB

instance GenBuses Float  where
  genBuses' = genPrimBus
  -- delay = primDelay
  ty = Float
  unflattenB' = unflattenPrimB

instance GenBuses Double  where
  genBuses' = genPrimBus
  -- delay = primDelay
  ty = Double
  unflattenB' = unflattenPrimB

instance KnownNat n => GenBuses (Finite n) where
  genBuses' = genPrimBus
  -- delay = primDelay
  ty = Finite (natVal (Proxy @n))
  unflattenB' = unflattenPrimB

instance (KnownNat n, GenBuses b) => GenBuses (Vector n b)  where
  genBuses' = genPrimBus
  -- delay = primDelay
  ty = Vector (natVal (Proxy @n)) (ty @b)
  unflattenB' = unflattenPrimB

-- TODO: perhaps give default definitions for genBuses', delay, and unflattenB',
-- and eliminate the definitions in Bool,...,Double,Vector a.


instance (GenBuses a, GenBuses b) => GenBuses (a :+ b)  where
  genBuses' = genPrimBus
  -- delay = primDelay
  ty = Sum (ty @a) (ty @b)
  unflattenB' = unflattenPrimB

instance (GenBuses a, GenBuses b) => GenBuses (a :* b) where
  genBuses' templ ins =
    -- trace ("genBuses' @ " ++ show (ty (undefined :: a :* b))) $
    ProdB <$> genBuses' templ ins <*> genBuses' templ ins
  -- delay (a,b) = delay a *** delay b
  ty = Prod (ty @a) (ty @b)
  unflattenB' = liftA2 ProdB unflattenB' unflattenB'

instance (GenBuses a, GenBuses b) => GenBuses (a -> b) where
  genBuses' = genPrimBus
  -- delay = error "delay for functions: not yet implemented"
  ty = ty @a `Fun` ty @b
  unflattenB' = unflattenPrimB

flattenB :: GenBuses a => Buses a -> [Source]
flattenB = toList . flat
 where
   flat :: forall a. GenBuses a => Buses a -> Seq Source
   flat UnitB        = mempty
   flat (PrimB s)    = singleton s
   flat (ProdB a b)  = flat a <> flat b
   flat (IxProdB as) = foldMap flat as
   flat (ConvertB b) = flat b

badBuses :: forall a x. Ok (:>) a => String -> Buses a -> x
badBuses nm bs = error (nm ++ " got unexpected bus " ++ show bs)

unProdB :: Ok2 (:>) a b => Buses (a :* b) -> Buses a :* Buses b
unProdB (ProdB a b)            = (a,b)
unProdB (ConvertB (ProdB c d)) = (convertB c, convertB d)
unProdB b                      = badBuses "unProdB" b

exlB :: Ok2 (:>) a b => Buses (a :* b) -> Buses a
exlB = fst . unProdB

exrB :: Ok2 (:>) a b => Buses (a :* b) -> Buses b
exrB = snd . unProdB

type OkCAR a = Ok2 (:>) a (Rep a)

-- TODO: if this experiment works out, eliminate AbstB, and rename ConvertB.
abstB :: OkCAR a => Buses (Rep a) -> Buses a
abstB = convertB

reprB :: OkCAR a => Buses a -> Buses (Rep a)
reprB = convertB

convertC :: forall a b. Ok2 (:>) a b => a :> b
convertC = C (arr convertB)

convertB :: forall a b. Ok2 (:>) a b => Buses a -> Buses b
-- convertB a | trace ("convertB " ++ show (typeRep (Proxy :: Proxy (a -> b))) ++ ": " ++ show a ++ "\n") False = undefined
convertB (ConvertB p) = mkConvertB p  -- coalesce
convertB a            = mkConvertB a

-- Make a ConvertB if source and target types differ; otherwise id
mkConvertB :: forall a b. Ok2 (:>) a b => Buses a -> Buses b
mkConvertB a -- | Just Refl <- eqT @a @b = a
             | otherwise              = ConvertB a

{--------------------------------------------------------------------
    The circuit monad
--------------------------------------------------------------------}

type PrimName = String

-- | Primitive of type @a -> b@
data Template :: * -> * -> * where
  Prim :: PrimName -> Template a b
  Subgraph :: Graph -> BCirc a b -> Template () (a -> b)

-- TODO: maybe add (a :> b) as a Subgraph argument for easier optimization later.
-- If so, change the Show instance to show only the graph.

instance Show (Template a b) where
  show (Prim p) = p
  show (Subgraph comps _) = "Template:" ++ show comps

-- Transform a subgraph if any. Must preserve meaning, since we leave the
-- generator unchanged.
onCompSubgraph :: Unop Graph -> Unop Comp
onCompSubgraph h (Comp nc (Subgraph g circ) a b) =
  Comp nc (Subgraph (h g) circ) a b
onCompSubgraph _ c = c

type Id = Int

type CompId = Id

type IdSupply = Id

-- Component: primitive instance with inputs & outputs. Numbered consistently
-- with dependency partial ordering.
data Comp = forall a b. Ok2 (:>) a b => Comp CompId (Template a b) (Buses a) (Buses b)

deriving instance Show Comp

compId :: Comp -> CompId
compId (Comp n _ _ _) = n

instance Eq  Comp where (==) = (==) `on` compId
instance Ord Comp where compare = compare `on` compId


#if !defined NoHashCons
-- Tracks prim applications (including output type) and reuses per component.
type CompInfo = Map (PrimName,[Source],Ty) Comp
#else
type CompInfo = [Comp]
#endif

type Graph = [Comp]

-- The circuit monad.
type CircuitM = State (IdSupply,CompInfo)

genId :: CircuitM Id
genId = do n <- M.gets fst
           M.modify (first succ)
           return n

type BCirc a b = Buses a -> CircuitM (Buses b)

-- Instantiate a 'Prim'
genComp :: forall a b. Ok2 (:>) a b => Template a b -> BCirc a b
#if !defined NoHashCons
genComp templ a =
  -- trace ("genComp " ++ name ++ ". b == " ++ show (ty @b)) $
  do mb <- M.gets (M.lookup key . snd)
     case mb of
       Just (Comp _ _ _ b') ->
         -- trace ("genComp " ++ name ++ ": hit --> " ++ show b') $
         return (unsafeCoerce b')
       Nothing               ->
         -- trace ("genComp " ++ name ++ ": ins == " ++ show ins) $
         do b <- genBuses templ ins
            -- trace ("genComp: genBuses --> " ++ show b) (return ())
            c <- genId
            let comp = Comp c templ a b
            M.modify (second (M.insert key comp))
            -- trace ("genComp " ++ name ++ ": miss --> " ++ show b) $
            return b
 where
   ins  = flattenB a
   name = show templ
   key  = (name,ins,ty @b)

-- TODO: maybe look for cache hits only on Prim templates.

#else
genComp templ a = -- trace (printf "genComp %s %s --> %s"
                  --         (show templ) (show a) (show (ty (undefined :: b)))) $
                  do b <- genBuses templ (flattenB a)
                     -- trace (printf "gen'd buses %s" (show b)) (return ())
                     c <- genId
                     M.modify (second (Comp c templ a b :))
                     -- trace (printf "added comp %s" (show (Comp templ a b))) (return ())
                     return b
#endif

constComp' :: GenBuses b => PrimName -> CircuitM (Buses b)
constComp' str = -- trace ("constComp' " ++ str) $
                 genComp (Prim ({- "const " ++ -} str)) UnitB

constComp :: GenBuses b => PrimName -> BCirc a b
constComp str = const (constComp' str)

-- TODO: maybe have constComp and constComp' take a template, and use for curry as well.

constM :: GS b => b -> BCirc a b
constM b = constComp (constName b)

#if 0

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

#else

constName :: Show b => b -> String
constName = show
#endif


{--------------------------------------------------------------------
    Circuit category
--------------------------------------------------------------------}

infixl 1 :>, :+>

-- | Internal representation for '(:>)'.
type a :+> b = Kleisli CircuitM (Buses a) (Buses b)

-- | Circuit category
newtype a :> b = C { unC :: a :+> b }

-- type a :> b =~ Buses a -> CircuitM (Buses b)

instance (OkCAR a, r ~ Rep a) => RepCat (:>) a r where
  reprC = C (arr reprB)
  abstC = C (arr abstB)

instance Ok2 (:>) a b => CoerceCat (:>) a b where coerceC = convertC

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

inCKF1 :: Functor h => (h (BCirc a a') -> BCirc b b') -> (h (a :> a') -> (b :> b'))
inCKF1 = mkCK <~ fmap unmkCK

namedC :: Ok2 (:>) a b => PrimName -> a :> b
-- namedC name = primOpt name noOpt
namedC name = -- trace ("namedC " ++ name) $
              mkCK (genComp (Prim name))

type Opt b = [Source] -> CircuitM (Maybe (Buses b))

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
newComp2 cir a b = newComp cir (ProdB (toBuses a) (toBuses b))

newComp3L :: (SourceToBuses a, SourceToBuses b, SourceToBuses c) =>
             ((a :* b) :* c :> d) -> Source -> Source -> Source -> CircuitM (Maybe (Buses d))
newComp3L cir a b c = newComp cir (ProdB (ProdB (toBuses a) (toBuses b)) (toBuses c))

newComp3R :: (SourceToBuses a, SourceToBuses b, SourceToBuses c) =>
             (a :* (b :* c) :> d) -> Source -> Source -> Source -> CircuitM (Maybe (Buses d))
newComp3R cir a b c = newComp cir (ProdB (toBuses a) (ProdB (toBuses b) (toBuses c)))

newVal :: GS b => b -> CircuitM (Maybe (Buses b))
newVal b = Just <$> constM' b

constM' :: GS b => b -> CircuitM (Buses b)
constM' b = constComp' (constName b)

-- noOpt :: Opt b
-- noOpt = const nothingA

orOpt :: Binop (Opt b)
orOpt f g a = do mb <- f a
                 case mb of
                   Nothing -> g a
                   Just _  -> return mb

primOpt, primOptSort :: Ok2 (:>) a b => PrimName -> Opt b -> a :> b
#if !defined NoOptimizeCircuit

-- primOpt name _ = mkCK (genComp (Template name))

primOpt name opt =
  mkCK $ \ a -> let plain = genComp (Prim name) a in
                  opt (flattenB a) >>= maybe plain return

tryCommute :: a :> a
tryCommute = mkCK try
 where
#if !defined NoCommute
   -- TODO: Add an Ord constraint to PrimB for this line
   try (ProdB (PrimB a) (PrimB a')) | a > a' = return (ProdB (PrimB a') (PrimB a))
#endif
   try b = return b

-- Like primOpt, but sorts. Use for commutative operations to improve reuse
-- (cache hits).
primOptSort name opt = primOpt name opt . tryCommute
#else
primOpt name _ = namedC name
primOptSort = primOpt
#endif

primNoOpt1 :: (Ok2 (:>) a b, Read a, Show b)
           => PrimName -> (a -> b) -> a :> b
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

constC :: GS b => b -> a :> b
constC = mkCK . constM

inC :: (a :+> b -> a' :+> b') -> (a :> b -> a' :> b')
inC = C <~ unC

inC2 :: (a :+> b -> a' :+> b' -> a'' :+> b'')
     -> (a :>  b -> a' :>  b' -> a'' :>  b'')
inC2 = inC <~ unC

instance Category (:>) where
  type Ok (:>) = GenBuses
  id  = C id
  (.) = inC2 (.)

crossB :: (Applicative m, Ok4 (:>) a b c d)
       => (Buses a -> m (Buses c)) -> (Buses b -> m (Buses d))
       -> (Buses (a :* b) -> m (Buses (c :* d)))
crossB f g = (\ ~(a,b) -> liftA2 ProdB (f a) (g b)) . unProdB

-- or drop crossB in favor of forkB with fstB and sndB

forkB :: (Applicative m, Ok3 (:>) a c d) =>
         (Buses a -> m (Buses c)) -> (Buses a -> m (Buses d))
      -> (Buses a -> m (Buses (c :* d)))
forkB f g a = liftA2 ProdB (f a) (g a)

-- or drop forkB in favor of dupB and crossB

dupB :: (Applicative m, Ok (:>) a) =>
        Buses a -> m (Buses (a :* a))
dupB a = pure (ProdB a a)

instance OpCon (:*) (Sat GenBuses) where inOp = Entail (Sub Dict)

instance ProductCat (:>) where
  -- type Prod (:>) = (:*)
  exl   = C (arr exlB)
  exr   = C (arr exrB)
  dup   = mkCK dupB
  (***) = inCK2 crossB  -- or default
  (&&&) = inCK2 forkB   -- or default

-- instance OpCon (:+) (Sat GenBuses) where inOp = Entail (Sub Dict)

-- instance CoproductCat (:>) where
--   inl = namedC "inl"
--   inr = namedC "inr"
--   f ||| g = namedC "|||" . (f &&& g) -- not quite

instance CoproductPCat (:>) where
  inlP   = namedC "inlP"
  inrP   = namedC "inrP"
  jamP   = namedC "jamP"
  swapPS = swapP
  (++++) = inCK2 crossB

-- TODO: indexed biproducts


{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

instance (Ok (:>) a, IfCat (:>) b) => IfCat (:>) (a -> b) where
  ifC = funIf

instance OpCon (->) (Sat GenBuses) where inOp = Entail (Sub Dict)

genSubgraph :: Ok2 (:>) b c => BCirc b c -> CircuitM (Buses (b -> c))
genSubgraph bcirc =
  do supply <- M.gets fst
     let (g,supply') = mkGraph' (mkCK bcirc) supply
     M.modify (first (const supply'))
     genComp (Subgraph g bcirc) UnitB

curryB :: Ok3 (:>) a b c => BCirc (a :* b) c -> BCirc a (b -> c)
curryB f a = genSubgraph (\ b -> f (ProdB a b))

-- primOpt, primOptSort :: Ok2 (:>) a b => PrimName -> Opt b -> a :> b
-- type Opt b = [Source] -> CircuitM (Maybe (Buses b))

-- data Source = forall a b. Source Bus (Template a b) [Source]

instance ClosedCat (:>) where
  -- type Exp (:>) = (->)
  -- apply = namedC "apply"
  apply :: forall a b. Ok2 (:>) a b => (a -> b) :* a :> b
  apply = primOpt "apply" $ \ case
            (Source _ (Subgraph _ gen) _ : rest)
              -> Just <$> (unsafeCoerce gen :: BCirc a b) (unflattenB rest)
            _ -> nothingA
  curry = mkCK . curryB . unmkCK

-- TODO: Try to make Source keep the unflattened bus structures instead of or in
-- addition to the untyped sources. Then eliminate this unsafeCoerce and
-- flattening and unflattening.

-- TODO: use Newtype and inNew in curry and elsewhere.

instance TerminalCat (:>)

{--------------------------------------------------------------------
    Indexed co/products
--------------------------------------------------------------------}

instance OkIxProd (:>) G.U1   where okIxProd = Entail (Sub Dict)
instance OkIxProd (:>) G.Par1 where okIxProd = Entail (Sub Dict)

instance (OkIxProd (:>) f, OkIxProd (:>) g)
      => OkIxProd (:>) (f G.:*: g) where
  okIxProd :: forall a. Ok' (:>) a |- Ok' (:>) ((f G.:*: g) a)
  okIxProd = Entail (Sub (Dict <+ okIxProd @(:>) @f @a <+ okIxProd @(:>) @g @a))

instance (OkIxProd (:>) f, OkIxProd (:>) g)
      => OkIxProd (:>) (g G.:.: f) where
  okIxProd :: forall a. Ok' (:>) a |- Ok' (:>) ((g G.:.: f) a)
  okIxProd = Entail (Sub (Dict <+ okIxProd @(:>) @g @(f a) <+ okIxProd @(:>) @f @a))

instance KnownNat i => OkIxProd (:>) (Vector i) where
  okIxProd = Entail (Sub Dict)

instance (OkIxProd (:>) h, Representable h, Show (R.Rep h), Zip h, Traversable h, Show1 h)
      => IxProductCat (:>) h where
  exF :: forall a . Ok (:>) a => h (h a :> a)
  exF = tabulate $ \ i -> namedC ("ex " ++ showsPrec 10 i "") <+ okIxProd @(:>) @h @a
  replF :: forall a . Ok (:>) a => a :> h a
  replF = namedC "replF" <+ okIxProd @(:>) @h @a
  crossF :: forall a b. Ok2 (:>) a b => h (a :> b) -> (h a :> h b)
  crossF = inCKF1 crossFB

instance ( OkIxProd (:>) h, Representable h, Zip h, Traversable h
         , Show (R.Rep h), Show1 h )
      => IxCoproductPCat (:>) h where
  inPF :: forall a. (Additive a, Ok  (:>) a  ) => h (a :> h a)
  inPF = tabulate $ \ i -> namedC ("inP " ++ showsPrec 10 i "") <+ okIxProd @(:>) @h @a
  jamPF :: forall a. (Additive a, Ok  (:>) a  ) => h a :> a
  jamPF = namedC "jamPF" <+ okIxProd @(:>) @h @a
  plusPF :: forall a b. Ok2 (:>) a b => h (a :> b) -> (h a :> h b)
  plusPF = crossF

unIxProdB :: Buses (h a) -> h (Buses a)
unIxProdB (IxProdB bs) = bs
unIxProdB b = error ("unIxProdB: unexpected bus: " ++ show b)

crossFB :: ( OkIxProd (:>) h, Zip h, Traversable h, Show1 h
           , Ok (:>) a, GenBuses b, Applicative m)
        => h (Buses a -> m (Buses b)) -> (Buses (h a) -> m (Buses (h b)))
crossFB fs = fmap IxProdB . transpose . zap fs . unIxProdB

--                                    fs             :: h (Buses a -> m (Buses b))
--                              cross fs             :: h (Buses a) -> h (m (Buses b))
--                  transpose . cross fs             :: h (Buses a) -> m (h (Buses b))
--                  transpose . cross fs . toIxProdB :: Buses (h a) -> m (h (Buses b))
-- fmap unIxProdB . transpose . cross fs . toIxProdB :: Buses (h a) -> m (Buses (h b))



{--------------------------------------------------------------------
    Ad hoc Functor-level operations, to be removed
--------------------------------------------------------------------}

instance OkFunctor (:>) G.U1   where okFunctor = Entail (Sub Dict)
instance OkFunctor (:>) G.Par1 where okFunctor = Entail (Sub Dict)

instance (OkFunctor (:>) f, OkFunctor (:>) g)
      => OkFunctor (:>) (f G.:*: g) where
  okFunctor :: forall a. Ok' (:>) a |- Ok' (:>) ((f G.:*: g) a)
  okFunctor = Entail (Sub (Dict
                             <+ okFunctor' @(:>) @f @a
                             <+ okFunctor' @(:>) @g @a))

instance (OkFunctor (:>) f, OkFunctor (:>) g)
      => OkFunctor (:>) (g G.:.: f) where
  okFunctor :: forall a. Ok' (:>) a |- Ok' (:>) ((g G.:.: f) a)
  okFunctor = Entail (Sub (Dict
                             <+ okFunctor' @(:>) @g @(f a)
                             <+ okFunctor' @(:>) @f @a))

instance KnownNat i => OkFunctor (:>) (Vector i) where
  okFunctor = Entail (Sub Dict)

-- Use *uncurried* fmap and zipWith primitives.

instance (Functor h, OkFunctor (:>) h) => FunctorCat (:>) h where
  fmapC :: forall a b. Ok2 (:>) a b => (a :> b) -> (h a :> h b)
  fmapC = inCK $ \ f as ->
            do ab <- genSubgraph f
               genComp (Prim "fmap") (ProdB ab as)
                 <+ okFunctor' @(:>) @h @a
                 <+ okFunctor' @(:>) @h @b
  unzipC :: forall a b. Ok2 (:>) a b => h (a :* b) :> (h a :* h b)
  unzipC = namedC "unzip"
             <+ okFunctor' @(:>) @h @(a :* b)
             <+ okFunctor' @(:>) @h @a
             <+ okFunctor' @(:>) @h @b

-- genSubgraph :: BCirc a b -> CircuitM (Buses (a -> b))
-- f :: BCirc a b
-- genSubgraph f :: CircuitM (Buses (a -> b))

instance (Zip h, OkFunctor (:>) h) => ZipCat (:>) h where
#if 0
  zipWithC  :: forall a b c. Ok3 (:>) a b c => (a :* b -> c) :> (h a :* h b -> h c)
  zipWithC = curry (namedC "zipWith")
               <+ okFunctor' @(:>) @h @a
               <+ okFunctor' @(:>) @h @b
               <+ okFunctor' @(:>) @h @c
#else
  zipC  :: forall a b. Ok2 (:>) a b => (h a :* h b) :> h (a :* b)
  zipC = namedC "zip"
           <+ okFunctor' @(:>) @h @(a :* b)
           <+ okFunctor' @(:>) @h @a
           <+ okFunctor' @(:>) @h @b
#endif

-- TODO: ZapCat instance? I don't think so, but we'll see.

instance ({- Pointed h, -} OkFunctor (:>) h, Ok (:>) a) => PointedCat (:>) h a where
  pointC :: a :> h a
  pointC = namedC "point"
             <+ okFunctor' @(:>) @h @a

instance (OkFunctor (:>) h, Additive a, Ok (:>) a) => AddCat (:>) h a where
  sumAC :: h a :> a
  sumAC = namedC "sumA" <+ okFunctor' @(:>) @h @a

-- instance () => IxSummableCat (:>) n a where
--   -- ixSumC :: forall a. (Additive a, Ok (:>) a) => a :^ n :> a
--   ixSumC = namedC "ixSum" -- <+ okFunctor' @(:>) @n @a

-- instance (Functor h, OkFunctor (:>) h) => Strong (:>) h where
--   strength :: forall a b. Ok2 (:>) a b => (a :* h b) :> h (a :* b)
--   strength = namedC "strength"
--               <+ okFunctor' @(:>) @h @(a :* b)
--               <+ okFunctor' @(:>) @h @b

okFunctor' :: forall k h a. OkFunctor k h => Ok' k a |- Ok' k (h a)
okFunctor' = {- trace "" $ -} okFunctor @k @h @a
{-# INLINE okFunctor' #-}

-- okFunctor' :: forall k h a. (k ~ (:>), OkFunctor k h, Ok k a) => Ok' k a |- Ok' k (h a)
-- okFunctor' = trace ("okFunctor: " ++ show (ty @(h a) <+ ok)) $
--              (case ok of Entail (Sub Dict) -> trace  "(okFunctor evaluated)") $
--              ok
--  where
--    ok = okFunctor @k @h @a
-- {-# INLINE okFunctor' #-}

-- Without the trace, `distributeC (:>) @Pair @(Vector n) @R` fails to terminate.
-- Ditto for `distributeC (:>) @(Vector n) @Pair @R`. Other combinations seem fine.
-- TODO: track down the cause.

instance (OkFunctor (:>) g, OkFunctor (:>) f) => DistributiveCat (:>) g f where
  distributeC :: forall a. Ok (:>) a => f (g a) :> g (f a)
  distributeC = namedC "distribute"
                  <+ okFunctor' @(:>) @g @(f a) <+ okFunctor' @(:>) @f @a
                  <+ okFunctor' @(:>) @f @(g a) <+ okFunctor' @(:>) @g @a

instance (GenBuses (R.Rep f), OkFunctor (:>) f) => RepresentableCat (:>) f where
  tabulateC :: forall a. Ok (:>) a => (R.Rep f -> a) :> f a
  tabulateC = -- trace "tabulateC @(:>)" $
              namedC "tabulate" <+ okFunctor' @(:>) @f @a
  indexC :: forall a. Ok (:>) a => f a :> (R.Rep f -> a)
  indexC = namedC "index" <+ okFunctor' @(:>) @f @a

#if 0

instance GS b => ConstCat (:>) b where
  const b = -- trace ("circuit const " ++ show b) $
            constC b

#else

#define LitConst(ty) instance ConstCat (:>) (ty) where const = constC

LitConst(())
LitConst(Bool)
LitConst(Int)
LitConst(Integer)
LitConst(Float)
LitConst(Double)
-- LitConst(Vector n a)

instance (Ok (:>) a, Show a, KnownNat n) => ConstCat (:>) (Vector n a) where const = constC

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

bottomG :: Ok2 (:>) z b => z :> b
bottomG = -- trace "bottomG called" $
          namedC "bottom"
          -- mkCK (constComp "undefined")

#if 0

#define BottomTemplate(ty) \
 instance BottomCat (:>) z (ty) where { bottomC = bottomG }

BottomTemplate(Bool)
BottomTemplate(Int)
BottomTemplate(Integer)
BottomTemplate(Float)
BottomTemplate(Double)
-- BottomTemplate(Vector n)

#endif

#if 0

instance BottomCat (:>) z () where
--   bottomC = mkCK (const (return UnitB))
  bottomC = C (arr (const UnitB))

instance (BottomCat (:>) a, BottomCat (:>) b) => BottomCat (:>) (a :* b) where
  bottomC = bottomC &&& bottomC

#if defined TypeDerivation
bottomC :: () :> b
bottomC . exl :: () :* a :> b
curry (bottomC . exl) :: () :> (a -> b)
#endif

#elif 1
instance Ok2 (:>) a b => BottomCat (:>) a b where
  bottomC = bottomG
#elif 0
instance GenBuses a => BottomCat (:>) a where
  bottomC = mkCK (const mkBot)
#elif 0
instance BottomCat (:>) where
  type BottomKon (:>) a = GenBuses a
  bottomC = mkCK (const (genBuses (Template "undefined") []))
-- See the note at BottomCat
#elif 0
instance BottomCat (:>) where
  type BottomKon (:>) a = GenBuses a
  bottomC = mkCK (const mkBot)
#endif

#endif

-- TODO: state names like "⊕" and "≡" just once.

class GenBuses a => SourceToBuses a where toBuses :: Source -> Buses a
instance SourceToBuses ()      where toBuses = const UnitB
instance SourceToBuses Bool    where toBuses = PrimB
instance SourceToBuses Int     where toBuses = PrimB
instance SourceToBuses Integer where toBuses = PrimB
instance SourceToBuses Float   where toBuses = PrimB
instance SourceToBuses Double  where toBuses = PrimB

#ifdef VectorSized
instance (KnownNat n, GenBuses b) => SourceToBuses (Vector n b) where
  toBuses = PrimB
#else
instance (GenBuses i {-Typeable i-}, GenBuses b) => SourceToBuses (Vector i b) where
  toBuses = PrimB
#endif

sourceB :: SourceToBuses a => Source -> CircuitM (Maybe (Buses a))
sourceB = justA . toBuses

unknownName :: PrimName
unknownName = "??"

instance Ok2 (:>) a b => UnknownCat (:>) a b where
  unknownC = namedC unknownName

#define Sat(pred) ((pred) -> True)
#define Eql(x) Sat(==(x))

pattern Read :: Read a => a -> String
pattern Read x <- (reads -> [(x,"")])

pattern ConstS :: PrimName -> Source
pattern ConstS name <- PSource _ name []

pattern Val :: Read a => a -> Source
pattern Val x <- ConstS (Read x)

-- pattern Val x       <- ConstS (reads -> [(x,"")])

pattern TrueS :: Source
pattern TrueS  <- ConstS("True")

pattern FalseS :: Source
pattern FalseS <- ConstS("False")

pattern NotS :: Source -> Source
pattern NotS a <- PSource _ "not" [a]

pattern XorS :: Source -> Source -> Source
pattern XorS a b <- PSource _ "xor" [a,b]

pattern EqS :: Source -> Source -> Source
pattern EqS a b <- PSource _ "==" [a,b]

-- pattern NeS :: Source -> Source -> Source
-- pattern NeS a b <- PSource _ "/=" [a,b]

-- primDelay :: (SourceToBuses a, GS a) => a -> (a :> a)
-- primDelay a0 = primOpt (delayName a0s) $ \ case
--                  [c@(ConstS (Eql(a0s)))] -> sourceB c
--                  _ -> nothingA
--  where
--    a0s = show a0

-- primDelay a0 = namedC (delayName (show a0))

instance BoolCat (:>) where
  -- type BoolOf (:>) = Bool
  notC = primOpt "not" $ \ case
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
  -- think I can fix it by adding a statically typed type GADT to
  -- `Source`. Or maybe a simpler version for primitive types only.
  andC = primOptSort "&&" $ \ case
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
  orC  = primOptSort "||" $ \ case
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
             do o <- unmkCK andC (ProdB (PrimB x) (PrimB y))
                newComp notC o
           _                     -> nothingA
  xorC = primOptSort "xor" $ \ case
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

boolToIntC :: Bool :> Int
boolToIntC = namedC "boolToInt"

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

#define EqTemplate(ty) \
 instance (Read (ty), Eq (ty), GenBuses (ty)) => EqCat (:>) (ty) where { \
    equal    = primOptSort "==" (eqOpt @(ty)) ;\
    notEqual = primOptSort "/=" (neOpt @(ty))  \
  }

-- TODO: give one overlappable EqCat instance and one or more overlapping.

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

-- EqTemplate(Bool)
EqTemplate(Int)
EqTemplate(Integer)
EqTemplate(Float)
EqTemplate(Double)
EqTemplate(a :+ b)

instance EqCat (:>) Bool where
  equal    = primOptSort "=="  (eqOpt @Bool `orOpt` eqOptB)
  notEqual = primOptSort "xor" (neOpt @Bool `orOpt` neOptB)

instance EqCat (:>) () where
  equal = constC True

-- instance (EqCat (:>) a, EqCat (:>) b) => EqCat (:>) (a :* b) where
--   equal = andC . (equal *** equal) . transposeP

-- Use EqTemplate for (a :* b) ?

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

#define OrdTemplate(ty) \
 instance OrdCat (:>) (ty) where { \
   lessThan           = primOpt "<" (ltOpt @(ty)) ; \
   greaterThan        = primOpt ">" (gtOpt @(ty)) ; \
   lessThanOrEqual    = primOpt "<=" (leOpt @(ty)) ; \
   greaterThanOrEqual = primOpt ">=" (geOpt @(ty)) ; \
 }

OrdTemplate(Bool)
OrdTemplate(Int)
OrdTemplate(Integer)
OrdTemplate(Float)
OrdTemplate(Double)

instance OrdCat (:>) () where
  lessThan = constC False

-- TODO:
--
-- instance (OrdCat (:>) a, OrdCat (:>) b) => OrdCat (:>) (a,b) where
--   ...

-- TODO: Move to a general definition in ConCat.Classes, and reference here.

#else

instance (Read a, Eq a) => EqCat (:>) a where
    equal    = primOptSort "==" $ \ case
                 [Val (x :: a), Val y] -> newVal (x == y)
                 [a,b] | a == b -> newVal True
                 _              -> nothingA
    notEqual = primOptSort "/=" $ \ case
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
   lessThanOrEqual    = primOpt "<=" $ \ case
                          [Val (x :: a), Val y] -> newVal (x <= y)
                          [a,b] | a == b        -> newVal True
                          _                     -> nothingA
   greaterThanOrEqual = primOpt ">=" $ \ case
                          [Val (x :: a), Val y] -> newVal (x >= y)
                          [a,b] | a == b        -> newVal True
                          _                     -> nothingA


#endif

instance Ok (:>) a => MinMaxCat (:>) a where
  minC = namedC "min"
  maxC = namedC "max"

-- TODO: Move to a general definition in ConCat.Classes, and reference here.

-- instance NumCat (:>) Int  where { add = namedC "+" ; mul = namedC "×" }

-- More robust (works for Double as well):

#define ValT(x,ty) (Val ((x) :: ty))

#define   ZeroT(ty) ValT(0,ty)
#define    OneT(ty) ValT(1,ty)
#define NegOneT(ty) ValT((-1),ty)

pattern NegateS :: Source -> Source
pattern NegateS a <- PSource _ "negate" [a]

pattern RecipS  :: Source -> Source
pattern RecipS  a <- PSource _ "recip"  [a]

instance (Num a, Read a, GS a, Eq a, SourceToBuses a)
      => NumCat (:>) a where
  negateC = primOpt "negate" $ \ case
              [Val x]         -> newVal (negate x)
              [NegateS x]     -> sourceB x
              _               -> nothingA
  addC    = primOptSort "+" $ \ case
              [Val x, Val y]  -> newVal (x + y)
              [ZeroT(a),y]    -> sourceB y
              [x,ZeroT(a)]    -> sourceB x
              [x,NegateS y]   -> newComp2 subC x y
              [NegateS x,y]   -> newComp2 subC y x
              _               -> nothingA
  subC    = primOpt     "-" $ \ case
              [Val x, Val y]  -> newVal (x - y)
              [ZeroT(a),y]    -> newComp1 negateC y
              [x,ZeroT(a)]    -> sourceB x
              [x,NegateS y]   -> newComp2 addC x y
              [NegateS x,y]   -> newComp2 (negateC . addC) x y
              _               -> nothingA
  mulC    = primOptSort "*" $ \ case
              [Val x, Val y]  -> newVal (x * y)
              [OneT(a),y]     -> sourceB y
              [x,OneT(a)]     -> sourceB x
              [x@ZeroT(a),_]  -> sourceB x
              [_,y@ZeroT(a)]  -> sourceB y
              [NegOneT(a) ,y] -> newComp1 negateC y
              [x,NegOneT(a) ] -> newComp1 negateC x
              [NegateS x,y]   -> newComp2 (negateC . mulC) x y
              [x,NegateS y]   -> newComp2 (negateC . mulC) x y
              _               -> nothingA
  powIC   = primOpt     "^" $ \ case
              [Val x, Val y]  -> newVal (x ^ (y :: Int))
              [x@OneT(a) ,_]  -> sourceB x
              [x,   OneT(a)]  -> sourceB x
              [x@ZeroT(a),_]  -> sourceB x
              [_,  ZeroT(a)]  -> newVal (fromInteger 1)
              _               -> nothingA

-- instance Integral a => IntegralCat (:>) a where
--   divC = primNoOpt1 "div" div
--   modC = primNoOpt1 "mod" mod

instance (Integral a, Read a, GS a, SourceToBuses a) => IntegralCat (:>) a where
  divC = primOpt "div" $ \case
              [Val x, Val y] -> newVal (x `div` y)
              [x,OneT(a)]    -> sourceB x
              [x@ZeroT(a),_] -> sourceB x
              _              -> nothingA
  modC = primOpt "mod" $ \case
              [Val x, Val y] -> newVal (x `mod` y)
              [_,OneT(a)]    -> newVal 0
              [x@ZeroT(a),_] -> sourceB x
              _              -> nothingA

instance (Fractional a, Read a, Eq a, GS a, SourceToBuses a)
      => FractionalCat (:>) a where
  recipC  = primOpt "recip" $ \ case
              [Val x]        -> newVal (recip x)
              [RecipS x]     -> sourceB x
              [NegateS x]    -> newComp1 (negateC . recipC) x
              _              -> nothingA
  divideC = primOpt "/" $ \ case
              [Val x, Val y] -> newVal (x / y)
              [z@ZeroT(a),_] -> sourceB z
              [x,OneT(a)]    -> sourceB x
              [x,NegateS y]  -> newComp2 (negateC . divideC) x y
              _              -> nothingA

instance (RealFrac a, Integral b, GS a, GS b, Read a)
      => RealFracCat (:>) a b where
  floorC    = primNoOpt1 "floor"   floor
  ceilingC  = primNoOpt1 "ceiling" ceiling
  truncateC = primNoOpt1 "truncate" truncate

instance (Floating a, Read a, GS a) => FloatingCat (:>) a where
  expC = primNoOpt1 "exp" exp
  cosC = primNoOpt1 "cos" cos
  sinC = primNoOpt1 "sin" sin
  logC = primNoOpt1 "log" log

-- TODO: optimizations, e.g., sin & cos of negative angles.

instance (Ok (:>) a, Integral a, Num b, Read a, GS b)
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
pattern BottomS <- ConstS "undefined"
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
pattern BitS b <- PSource _ (readBit -> Just b) []

readBit :: String -> Maybe Bool
readBit "0" = Just False
readBit "1" = Just True
readBit _   = Nothing

pattern BToIS :: Source -> Source
pattern BToIS a <- PSource _ BooloInt [a]

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
  -- [c,OneS,ZeroS] -> newComp1 boolToIntC c
  -- [c,ZeroS,OneS] -> newComp1 (boolToIntC . notC) c
  _              -> nothingA
#endif

instance IfCat (:>) Bool    where ifC = primOpt "if" (ifOpt `orOpt` ifOptB)
instance IfCat (:>) Int     where ifC = primOpt "if" (ifOpt `orOpt` ifOptI)
instance IfCat (:>) Integer where ifC = primOpt "if" ifOpt
instance IfCat (:>) Float   where ifC = primOpt "if" ifOpt
instance IfCat (:>) Double  where ifC = primOpt "if" ifOpt

-- TODO: Would we rather zip the conditional over the vector?
instance (GenBuses b, KnownNat n) => IfCat (:>) (Vector n b) where
  ifC = primOpt "if" ifOpt

instance IfCat (:>) () where ifC = unitIf

instance (IfCat (:>) a, IfCat (:>) b) => IfCat (:>) (a :* b) where
  ifC = prodIf

{--------------------------------------------------------------------
    Running
--------------------------------------------------------------------}

instance (GenBuses a, Ok2 (:>) a b) => Show (a :> b) where
  -- show = show . mkGraph -- runC
  show = show . fmap simpleComp . mkGraph

--     Application is no smaller than the instance head
--       in the type family application: RepT :> a
--     (Use -XUndecidableInstances to permit this)

-- -- Turn a circuit into a list of components, including fake In & Out.
-- runC :: (GenBuses a, Ok (:>) b) => (a :> b) -> Graph
-- runC = runU . unitize

type UU = () :> ()

-- runU :: UU -> Graph
-- runU cir = fst (runU' cir 0)

runU' :: UU -> IdSupply -> (Graph,IdSupply)
runU' cir supply = (getComps compInfo, supply')
 where
   compInfo :: CompInfo
   (supply',compInfo) = execState (unmkCK cir UnitB) (supply,mempty)
#if !defined NoHashCons
   getComps = M.elems
#else
   getComps = id
#endif

-- Wrap a circuit with fake input and output
unitize :: (GenBuses a, Ok (:>) b) => (a :> b) -> UU
unitize = namedC "Out" <~ namedC "In"

-- uuGraph :: UU -> Graph
-- uuGraph uu = fst (uuGraph' uu 0)

uuGraph' :: UU -> IdSupply -> (Graph,IdSupply)
uuGraph' = runU'  -- for now

mkGraph :: Ok2 (:>) a b => (a :> b) -> Graph

-- mkGraph g = sort $ trimGraph $ fst (mkGraph' g 0)

mkGraph g = -- trace "mkGraph" $
            -- trace ("fst (mkGraph' g 0)" ++ show (fst (mkGraph' g 0))) $
            -- trace ("trimGraph --> " ++ show (trimGraph $ fst (mkGraph' g 0))) $
            -- trace ("sort --> " ++ show (sort $ trimGraph $ fst (mkGraph' g 0))) $
            sort $ trimGraph $ fst (mkGraph' g 0)

mkGraph' :: Ok2 (:>) a b => (a :> b) -> IdSupply -> (Graph,IdSupply)
mkGraph' g n = uuGraph' (unitize g) n


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
#if defined NoCommute
        . (++"-no-commute")
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
#if defined ShallowDelay
        . (++"-shallow-delay")
#endif

-- Remove while I'm sorting things out
#if 1

type Name = String
type Report = String

outDir :: String
outDir = "out"

outFile :: String -> String -> String
outFile name suff = outDir++"/"++name++"."++suff

writeDot :: String -> [Attr] -> Graph -> IO ()
writeDot (renameC -> name) attrs g =
  do createDirectoryIfMissing False outDir
     writeFile (outFile name "dot")
       (graphDot name attrs g {- ++"// "++ report -})
     putStrLn ("Wrote " ++ name)
     -- putStr report

displayDot :: (String,String) -> String -> IO ()
displayDot (outType,res) (renameC -> name) =
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

#if 0

showCounts :: [(PrimName,Int)] -> String
showCounts = intercalate ", "
           . map (\ (nm,num) -> printf "%d %s" num nm)
           . (\ ps -> if length ps <= 1 then ps
                       else ps ++ [("total",sum (snd <$> ps))])
           . filter (\ (nm,n) -> n > 0 && not (isOuterTemplate nm))

summary :: Graph -> String
summary = showCounts
        . histogram
        . map compName
        . gather
 where
   gather :: Graph -> [Comp]
   gather (Graph comps) = comps

histogram :: Ord a => [a] -> [(a,Int)]
histogram = map (head &&& length) . group . sort

-- TODO: Instead of failing, emit a message about the generated file. Perhaps
-- simply use "echo".

#endif

type Dot = String

#if 0

-- type Depth = Int

type CompDepths = Map CompS Depth

-- | Longest paths excluding delay/Cons elements.
longestPaths :: Graph -> CompDepths
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

sourceComp :: Graph -> (Output -> Comp)
sourceComp g = \ o -> fromMaybe (error (msg o)) (M.lookup o comps)
 where
   msg o = printf "sourceComp: mystery output %s in graph %s."
             (show o) (show g)
   comps = foldMap (\ c -> M.fromList [(o,c) | o <- compOuts c]) g

-- The pred eliminates counting both In (constants) *and* Out.

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

#endif

-- Trim unused components. Construct the transitive closure of immediate
-- dependencies starting from the top-level graph's output component. For each
-- key/value pair in the map, find the immediate predecessor IDs.

trimGraph :: Unop Graph
-- trimGraph g | trace (printf "trimGraph %s" (show g)) False = undefined
trimGraph g = go g
 where
   isUsed = (`S.member` usedComps g)
   go = map (onCompSubgraph go) . filter (isUsed . compId)

usedComps :: Graph -> S.Set CompId
usedComps g = transitiveClosure (compUses g) [outId g]

compUses :: Graph -> CompId -> [CompId]
compUses g = -- trace (printf "compUses: gmap == %s" (show gmap))
             (M.!) (preds <$> gmap)
  where
    gmap = graphMap g
    preds (Comp _ templ (flatB -> ins) _) =
      [c | Bus c _ _ <- ins] ++
      case templ of Prim _ -> []
                    Subgraph g' _ -> [outId g']

graphMap :: Graph -> Map Id Comp
graphMap comps =
     M.fromList [(compId c,c) | c <- comps]
  <> M.unions (graphMap <$> [g | Comp _ (Subgraph g _) _ _ <- comps])

transitiveClosure :: forall a. ({- Show a, -} Ord a) => (a -> [a]) -> [a] -> S.Set a
transitiveClosure nexts = go mempty
 where
   go :: S.Set a -> [a] -> S.Set a
   -- go seen as | trace (printf "go %s %s" (show (S.toList seen)) (show as)) False = undefined
   go seen     [] = seen
   go seen (a:as) | a `S.member` seen = go seen as
                  | otherwise         = go (S.insert a seen) (nexts a ++ as)

graphDot :: String -> [Attr] -> Graph -> Dot
graphDot name attrs comps =
  printf "digraph %s {\n%s}\n" (tweak <$> name)
         (unlines $ map indent $
          (  prelude
          ++ recordDots comps
          -- ++ concatMap subgraphDot (M.toList subgraphs)
          ))
 where
   prelude = [ "margin=0"
             , "compound=true"
             , "rankdir=LR"
             , "node [shape=Mrecord]"
             , "edge [fontsize=8,fontcolor=indigo]"
             , "bgcolor=transparent"
             , "nslimit=20"  -- helps with very large rank graphs
             -- , "ratio=1"
             -- , "ranksep=1.0"
             -- , fixedsize=true
             ] ++ [a ++ "=" ++ show v | (a,v) <- attrs]
   tweak '-' = '_'
   tweak c   = c

indent :: Unop String
indent = ("  " ++)

subgraphDot :: CompId -> Graph -> [Statement]
subgraphDot nc comps =
     [printf "subgraph cluster_%d {" nc]
  ++ map indent (prelude ++ recordDots comps)
  ++ ["}"]
 where
   prelude = [ "margin=8" , "fontsize=20", "labeljust=r", "color=DarkGreen" ]

-- TODO: refactor graphDot & subgraphDot

type Statement = String

data CompS = CompS CompId PrimName [Input] [Output] deriving Show

#if 0

compSId :: CompS -> CompId
compSId (CompS n _ _ _) = n
compSName :: CompS -> PrimName
compSName (CompS _ nm _ _) = nm
compSIns :: CompS -> [Input]
compSIns (CompS _ _ ins _) = ins
compSOuts :: CompS -> [Output]
compSOuts (CompS _ _ _ outs) = outs

instance Eq  CompS where (==)    = (==)    `on` compSId
instance Ord CompS where compare = compare `on` compSId

#endif

simpleComp :: Comp -> CompS
simpleComp (Comp n prim a b) = CompS n (show prim) (flatB a) (flatB b)

-- pattern CompS :: CompId -> String -> [Bus] -> [Bus] -> Comp
-- pattern CompS cid name ins outs <- Comp cid (Prim name) (flatB -> ins) (flatB -> outs)

flatB :: GenBuses c => Buses c -> [Bus]
flatB = fmap sourceBus . flattenB

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

-- Prettier names for graph display
prettyName :: Unop String
prettyName str = fromMaybe str (M.lookup str prettyNames)

prettyNames :: Map String String
prettyNames = M.fromList
 [ ("not","¬") , ("&&","∧") , ("||","∨") , ("xor","⊕")
 , ("==","≡") , ("/=","≢")
 , ("<=","≤") , (">=","≥")
 , ("-","−"), ("*","×") , ("^","↑") , ("/","÷")
 , ("undefined","⊥")
 , ("boolToInt", "Bool→Int")
 , ("arrAt","!")
 ]

outId :: Graph -> CompId
outId (filter isOut -> [Comp cid _ _ _]) = cid
outId g = error ("outId: no Out found in graph: " ++ show g)

isOut :: Comp -> Bool
isOut (Comp _ (Prim "Out") _ _) = True
isOut _                         = False

recordDots :: [Comp] -> [Statement]
recordDots comps = nodes ++ edges
 where
   nodes = concatMap node comps
    where
      node :: Comp -> [Statement]
      node (Comp nc (Subgraph g _) UnitB (PrimB _)) = subgraphDot nc g
      node (simpleComp -> CompS nc (prettyName -> prim) ins outs) =
        [prefix ++ mbCluster
         (printf "%s [label=\"{%s%s%s}\"%s]"
           (compLab nc)
           (ports "" (labs In ins) "|")
           (escape prim)
           (ports "|" (labs Out outs) "")
           extras)]
       where
         isSubgraph (Subgraph {}) = True
         isSubgraph _ = False
         wrapNodes = any (\ (Comp _ p _ _) -> isSubgraph p) comps
         mbCluster :: Unop String
         mbCluster | wrapNodes =
           printf "subgraph clusterc%d { label=\"\"; color=white; margin=0; %s }" nc
                   | otherwise = id
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
            portSticker (p,_) = bracket (portLab dir p)
         -- Escape angle brackets, "|", and other non-ascii
         escape :: Unop String
         escape [] = []
         escape (c:cs) = mbEsc (c : escape cs)
          where
             mbEsc | (c `elem` "<>|{}") || not (isAscii c)  = ('\\' :)
                   | otherwise     = id
      -- node comp = error ("recordDots/node: unexpected comp " ++ show comp)
   bracket = ("<"++) . (++">")
   edges = concatMap compEdges comps
    where
      compEdges _c@(Comp cnum _ a _) = edge <$> tagged (flattenB a)
       where
         edge (ni, Source (Bus ocnum opnum t) templ _) =
           printf "%s -> %s [%s]"
             (maybe (port Out (ocnum,opnum)) compLab mbSubOut)
             (port In (cnum,ni))
             (intercalate "," attrs)
          where
            mbSubOut :: Maybe CompId  -- Output component if a subgraph
            mbSubOut = case templ of Prim _       -> Nothing
                                     Subgraph g _ -> Just (outId g)
            attrs = (if isJust mbSubOut then [printf "ltail=cluster_%d" ocnum] else []) ++
                    label ++ constraint
#ifdef ShallowDelay
            constraint | isDelay _c = ["constraint=false" ]
                       | otherwise  = []
#else
            constraint = []
#endif
#ifdef NoBusLabel
            label = const [] t -- []
#else
            -- Show the type per edge. I think I'd rather show in the output
            -- ports, but I don't know how to use a small font for those port
            -- labels but not for the operation label.
            -- label | t == Bool = []
            label = [printf "label=\"%s\"" (show t)]
#endif
   port :: Dir -> (CompId,PortNum) -> String
   port dir (cnum,np) =
     printf "%s:%s" (compLab cnum) (portLab dir np)
   compLab :: CompId -> String
   compLab nc = 'c' : show nc
   portLab :: Dir -> PortNum -> String
   portLab dir np = printf "%s%d" (show dir) np

-- sourceMap :: [Comp] -> SourceMap
-- sourceMap = foldMap $ \ (Comp nc _ _ b) ->
--               M.fromList [ (o,(busTy o,nc,np))
--                          | (np,o) <- tagged (flatB b) ]

segmentedDotString :: Unop String
segmentedDotString = intercalate "\"+\"" . divvy
 where
   divvy [] = []
   divvy (splitAt yy_buf_size -> (pre,suf)) = pre : divvy suf
   yy_buf_size = 16370 -- 16384 - some overhead

-- showBool :: Bool -> String
-- showBool False = "F"
-- showBool True  = "T"

#endif

{--------------------------------------------------------------------
    Type-specific support
--------------------------------------------------------------------}

-- GenBuses needed for data types appearing the external interfaces (and hence
-- not removed during compilation).

genBusesRep' :: (OkCAR a, GenBuses (Rep a)) =>
                Template u v -> [Source] -> BusesM (Buses a)
genBusesRep' templ ins = abstB <$> genBuses' templ ins

-- tweakValRep :: (HasRep a, Tweakable (Rep a)) => Unop a
-- tweakValRep = abst . tweakVal . repr

bottomRep :: (Ok3 (:>) a b (Rep b), BottomCat (:>) a (Rep b)) => a :> b
bottomRep = abstC . bottomC

tyRep :: forall a. GenBuses (Rep a) => Ty
tyRep = ty @(Rep a)

-- delayCRep :: (HasRep a, OkCAR a, GenBuses a, GenBuses (Rep a)) => a -> (a :> a)
-- delayCRep a0 = abstC . delay (repr a0) . reprC

genUnflattenB' :: (GenBuses a, GenBuses (Rep a)) => State [Source] (Buses a)
genUnflattenB' = abstB <$> unflattenB'

-- Omit temporarily for faster compilation
#if 1

#include "ConCat/AbsTy.inc"

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

AbsTy(Add a)

#endif
