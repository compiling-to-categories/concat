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

-- Primitive operation, including literals
data Prim :: * -> * -> * where
  Literal :: b -> Prim () b
  Not :: Prim Bool Bool
  And, Or, Xor :: Prim (Bool :* Bool) Bool
  -- ...
  ArrAt :: Prim (Arr a :* Int) a 
  In :: Prim () b
  Out :: Prim a ()

data Buses :: * -> * where
  UnitB    :: Buses ()
  -- BoolB    :: Source -> Buses Bool
  -- IntB     :: Source -> Buses Int
  -- FloatB   :: Source -> Buses Float
  -- DoubleB  :: Source -> Buses Double
  PairB    :: Buses a -> Buses b -> Buses (a :* b)
  FunB     :: BG (e :* a) b -> Buses e -> Buses (a -> b)

  FunB'    :: BG a b -> Buses (a -> b)

  -- ConvertB :: (T a, T b) => Buses a -> Buses b

-- Primitive or composed kernel
data Graph a b = PrimG (Prim a b) 
               | CompositeG (Buses a) Comps (Buses b)

type Comps = Seq (Exists2 Comp)

type CompNum = Int

-- Instantiated component with inputs and defining outputs
data Comp a b = Comp CompNum (Graph a b) (Buses a) (Buses b)

-- Existential wrapper
data Exists2 f = forall a b. Exists2 (f a b)

{--------------------------------------------------------------------
    Graph monad
--------------------------------------------------------------------}

type GraphM = M.StateT CompNum (M.Writer Comps)

newCompNum :: GraphM CompNum
newCompNum = do { !n <- M.get ; M.put (n+1) ; return n }

addComp :: Comp a b -> GraphM ()
addComp comp = M.tell (singleton (Exists2 comp))

genBuses :: CompNum -> Buses b
genBuses = error "genBuses: not yet defined"

type BG a b = Buses a -> GraphM (Buses b)

addG :: Graph a b -> BG a b
addG g a = do n <- newCompNum
              let b = genBuses n
              addComp (Comp n g a b)
              return b

exlB :: Ok2 (:>) a b => BG (a :* b) a
exlB (PairB a _) = return a

exrB :: Ok2 (:>) a b => BG (a :* b) b
exrB (PairB _ b) = return b

forkB :: BG a c -> BG a d -> BG a (c :* d)
forkB f g a = liftA2 PairB (f a) (g a)

{--------------------------------------------------------------------
    Graph category
--------------------------------------------------------------------}

infixl 1 :>

-- | Graph category
newtype a :> b = C (Kleisli GraphM (Buses a) (Buses b))

runG :: (a :> b) -> CompNum -> Buses a -> ((Buses b, CompNum), Comps)
runG f n a = M.runWriter (M.runStateT (unpack f a) n)

runG2 :: (a :> b) -> CompNum -> (CompNum, Comps)
runG2 f n = first snd (M.runWriter (M.runStateT q n))
 where
   q = do a <- addG (PrimG In) UnitB
          b <- unpack f a
          UnitB <- addG (PrimG Out) b
          return ()

runG3 :: (a :> b) -> CompNum -> (CompNum, Comps)
runG3 f n = first snd (M.runWriter (M.runStateT (q UnitB) n))
 where
   q = addG (PrimG Out) <=< unpack f <=< addG (PrimG In)

runG4 :: (() :> ()) -> CompNum -> (CompNum, Comps)
runG4 f n = first snd (M.runWriter (M.runStateT (unpack f UnitB) n))

unitize :: (a :> b) -> (() :> ())
unitize = addPrim Out <~ addPrim In
-- unitize f = addPrim Out . f . addPrim In

runG5 :: forall a b. (a :> b) -> CompNum -> (CompNum, Graph a b)
runG5 f n = (n',CompositeG i comps o)
 where
   (((i,o),n'),comps) = M.runWriter (M.runStateT q n)
   q :: GraphM (Buses a, Buses b)
   q = do a <- addG (PrimG In) UnitB
          b <- unpack f a
          UnitB <- addG (PrimG Out) b
          return (a,b)

-- Don't add In and Out components
runG6 :: forall a b. (a :> b) -> CompNum -> (CompNum, Graph a b)
runG6 f n = (n',CompositeG i comps o)
 where
   (((i,o),n'),comps) = M.runWriter (M.runStateT q n)
   q :: GraphM (Buses a, Buses b)
   q = do a <- genBuses <$> newCompNum
          b <- unpack f a
          return (a,b)

-- Stylistic variation
runG7 :: forall a b. (a :> b) -> CompNum -> (CompNum, Graph a b)
runG7 f n = tweak (M.runWriter (M.runStateT q n))
 where
   tweak (((a,b),n'),comps) = (n',CompositeG a comps b)
   q :: GraphM (Buses a, Buses b)
   q = do a <- genBuses <$> newCompNum
          b <- unpack f a
          return (a,b)

genG :: (a :> b) -> GraphM (Graph a b)
genG f = do n <- M.get
            let (n',g) = runG7 f n
            M.put n'
            return g

-- genG f = do (n',g) <- runG7 f <$> M.get
--             g <$ M.put n'

instance Newtype (a :> b) where
  type O (a :> b) = BG a b
  pack f = C (Kleisli f)
  unpack (C (Kleisli f)) = f

instance Category (:>) where
  id  = pack return
  (.) = inNew2 (<=<)

instance ProductCat (:>) where
  exl   = pack exlB
  exr   = pack exrB
  (&&&) = inNew2 forkB

-- instance ClosedCat (:>) where
--   apply   = pack  $ \ (PairB (FunB f e) a) -> f (PairB e a)
--   curry   = inNew $ \ f e -> return (FunB f e)
--   uncurry = inNew $ \ g (PairB a b) -> do { FunB f e <- g a ; f (PairB e b) }

instance ClosedCat (:>) where
  apply   = pack  $ \ (PairB (FunB' f) a) -> f a
  curry   = inNew $ \ f -> return . FunB' . curry (f . uncurry PairB)
  uncurry = inNew $ \ g (PairB a b) -> do { FunB' f <- g a ; f b }

-- f :: BG (a :* b) c
--   :: Buses (a :* b) -> GraphM (Buses c)
-- f . uncurry PairB :: Buses a :* Buses b -> GraphM (Buses c)
-- curry (f . uncurry PairB) :: Buses a -> Buses b -> GraphM (Buses c)
--                           :: Buses a -> BG b c
-- FunB' . curry (f . uncurry PairB) :: Buses a -> Buses (b -> c)
-- return . FunB' . curry (f . uncurry PairB) :: BG a (b -> c)

instance TerminalCat (:>) where
  it = pack (const (return UnitB))

-- instance GST b => ConstCat (:>) b where
--   const b = -- trace ("circuit const " ++ show b) $
--             constC b

addPrim :: Prim a b -> (a :> b)
addPrim = pack . addG . PrimG

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
--   mkArr n = pack (\ (FunB f e) -> _)
--   arrAt = addPrim ArrAt

#if 0

f :: BG (e :* a) b
  :: Buses (e :* a) -> GraphM (Buses b)
e :: Buses e

#endif
