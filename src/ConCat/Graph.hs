{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fdefer-typed-holes #-} -- TEMP

-- | Experimenting with a replacement for Circuit

module ConCat.Graph where

import Prelude hiding (id,(.),curry,uncurry,const)

import Control.Arrow (Kleisli(..),arr)
import Control.Applicative (liftA2)
import Control.Monad ((<=<))
import Data.Sequence (Seq,singleton)

import Control.Newtype
-- mtl
import qualified Control.Monad.State  as M
import qualified Control.Monad.Writer as M

import ConCat.Misc ((:*),(:=>),inNew,inNew2)
import ConCat.Category

-- Primitive operation, including literals and subgraphs
data Prim :: * -> * -> * where
  Not :: Prim Bool Bool
  And, Or, Xor :: Prim (Bool :* Bool) Bool
  -- ...
  MkArray :: Int -> Prim (Int -> a) (Arr a)
  ArrAt :: Prim (Arr a :* Int) a 
  -- In :: Prim () b
  -- Out :: Prim a ()
  Literal :: b -> Prim () b
  SubGraph :: Graph a b -> Prim a b

type PortNum = Int

data Ports :: * -> * where
  UnitP    :: Ports ()
  BoolP    :: PortNum -> Ports Bool
  IntP     :: PortNum -> Ports Int
  FloatP   :: PortNum -> Ports Float
  DoubleP  :: PortNum -> Ports Double
  PairP    :: Ports a -> Ports b -> Ports (a :* b)
  FunP     :: Graph a b -> Ports (a -> b)

  -- ConvertP :: (T a, T b) => Ports a -> Ports b

data Graph a b = Graph (Ports a) Comps (Ports b)

type Comps = Seq (Exists2 Comp)

-- type CompNum = Int

-- Instantiated component with inputs and defining outputs
data Comp a b = Comp (Ports a) (Prim a b) (Ports b)

-- Existential wrapper
data Exists2 f = forall a b. Exists2 (f a b)

{--------------------------------------------------------------------
    Graph monad
--------------------------------------------------------------------}

type GraphM = M.StateT PortNum (M.Writer Comps)

newPortNum :: GraphM PortNum
newPortNum = do { !n <- M.get ; M.put (n+1) ; return n }

addComp :: Comp a b -> GraphM ()
addComp comp = M.tell (singleton (Exists2 comp))

genPorts :: GraphM (Ports b)
genPorts = _ -- error "genPorts: not yet defined"

type BG a b = Ports a -> GraphM (Ports b)

runG :: BG a b -> Ports a -> PortNum -> (Graph a b,PortNum)
runG f a n = (Graph a comps b,n')
 where
   ((b,n'),comps) = M.runWriter (M.runStateT (f a) n)

exlP :: Ok2 (:>) a b => BG (a :* b) a
exlP (PairP a _) = return a

exrP :: Ok2 (:>) a b => BG (a :* b) b
exrP (PairP _ b) = return b

forkP :: BG a c -> BG a d -> BG a (c :* d)
forkP f g a = liftA2 PairP (f a) (g a)

-- type PortMap = Map PortMap PortMap

substG :: Graph a b -> Ports a -> GraphM (Ports b)
substG = _

applyP :: BG ((a -> b) :* a) b
applyP (PairP (FunP g) a) = substG g a

-- applyP (PairP (FunP (PrimG prim)) a) =
--   do b <- genPorts
--      return (CompositeG a (singleton prim)

curryP :: BG (a :* b) c -> BG a (b -> c)

curryP f a = do b <- genPorts
                n <- M.get
                let (Graph _ comps c,n') = runG f (PairP a b) n
                M.put n'
                return (FunP (Graph b comps c))

-- It's awkward to have runG insert the given ports just to replace them later.
-- Maybe split Graph into a part without input ports (produced by runG) and the
-- input ports.

-- runG :: BG a b -> Ports a -> PortNum -> (Graph a b,PortNum)

-- runG :: BG (a :* b) c -> Ports (a :* b) -> PortNum -> (Graph (a :* b) c,PortNum)


{--------------------------------------------------------------------
    Graph category
--------------------------------------------------------------------}

infixl 1 :>

-- | Graph generator category
newtype a :> b = C (Kleisli GraphM (Ports a) (Ports b))

instance Newtype (a :> b) where
  type O (a :> b) = BG a b
  pack f = C (Kleisli f)
  unpack (C (Kleisli f)) = f

instance Category (:>) where
  id  = pack return
  (.) = inNew2 (<=<)

instance ProductCat (:>) where
  exl   = pack exlP
  exr   = pack exrP
  (&&&) = inNew2 forkP

instance ClosedCat (:>) where
  apply   = pack applyP
  curry   = inNew curryP

-- instance ClosedCat (:>) where
--   apply   = pack  $ \ (PairP (FunP f) a) -> f a
--   curry   = inNew $ \ f -> return . FunP . curry (f . uncurry PairP)
--   uncurry = inNew $ \ g (PairP a b) -> do { FunP f <- g a ; f b }

#if 0

f :: BG (a :* b) c
  :: Ports (a :* b) -> GraphM (Ports c)
f . uncurry PairP :: Ports a :* Ports b -> GraphM (Ports c)
curry (f . uncurry PairP) :: Ports a -> Ports b -> GraphM (Ports c)
                          :: Ports a -> BG b c
FunB' . curry (f . uncurry PairP) :: Ports a -> Ports (b -> c)
return . FunB' . curry (f . uncurry PairP) :: BG a (b -> c)

#endif

instance TerminalCat (:>) where
  it = pack (const (return UnitP))

-- instance GST b => ConstCat (:>) b where
--   const b = -- trace ("circuit const " ++ show b) $
--             constC b

addPrim :: Prim a b -> (a :> b)
addPrim p = pack $ \ a ->
            do b <- genPorts
               addComp (Comp a p b)
               return b

instance BoolCat (:>) where
  notC = addPrim Not
  andC = addPrim And
  orC  = addPrim Or
  xorC = addPrim Xor

-- TODO optimization

#if 0
type Arr = Array Int

class ArrayCat k a where
  mkArr :: Int -> (Exp k Int a `k` Arr a)
  arrAt :: (Arr a :* Int) `k` a
#endif

-- instance ArrayCat (:>) a where
--   mkArr n = pack (\ (FunP f) -> _)
--   arrAt = addPrim ArrAt

-- genG :: BG a b -> GraphM (Graph a b)
