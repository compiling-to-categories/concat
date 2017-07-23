{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -Wno-orphans #-} -- OpCon

-- | GUI category

module ConCat.Gui where

import Prelude hiding (id,(.),curry,uncurry,const)
import Control.Applicative (liftA2)
import Data.IORef
import GHC.Exts (Coercible,coerce)

import Data.Default
import Control.Newtype
import Data.Constraint ((:-)(..),Dict(..))

import ConCat.Misc ((:*),(:+),inNew,inNew2)
import ConCat.Category
import ConCat.AltCat (ccc)

data In   :: * -> * where
  NoI     :: {- Show a => -} a -> In a
  -- | label, low, high, initial value
  SliderI :: String -> Int -> Int -> Int -> In Int
  PairI   :: {- (Show a, Show b) => -} In a -> In b -> In (a :* b)

-- deriving instance Show (In a)

-- Initial value
initI :: In a -> a
initI (NoI a) = a
initI (SliderI _ _ _ a) = a
initI (PairI a b) = (initI a, initI b)

unPairI :: {- (Show a, Show b) => -} In (a :* b) -> In a :* In b
unPairI (PairI a b) = (a,b)
unPairI i = (NoI a,NoI b) where (a,b) = initI i

instance Monoid (Out a) where
  mempty = NoO
  NoO `mappend` b = b
  a   `mappend` _ = a

infixr 9 :-->

data Out  :: * -> * where
  NoO     :: Out a
  -- | label, low, high
  SliderO :: String -> Int -> Int -> Out Int
  PairO   :: Out a -> Out b -> Out (a :* b)
  (:-->)  :: In a -> Out b -> Out (a -> b)

unPairO :: Out (a :* b) -> Out a :* Out b
unPairO (PairO a b) = (a,b)
unPairO _ = (NoO,NoO)

unFunO :: {- (Show a, Show b) => -} Out (a -> b) -> In a :* Out b
unFunO (a :--> b) = (a,b)
unFunO _o = error ("unFunO: given a non-lambda " {- ++ show _o -})
-- unFunO ab = (NoI ?,NoO)

-- deriving instance Show (Out a)

data Gui a b = Gui (In a) (Out b) -- deriving Show

instance Newtype (Gui a b) where
  type O (Gui a b) = In a :* Out b
  pack (a,b) = Gui a b
  unpack (Gui a b) = (a,b)

input :: In a -> Gui a a
input = pack . (,NoO)

instance Default a => Monoid (In a) where
  mempty = NoI def
  NoI _ `mappend` b = b
  a     `mappend` _ = a

output :: Default a => Out a -> Gui a a
output = pack . (mempty,)

noGui :: Default a => Gui a b
noGui = pack mempty

instance Category Gui where
  type Ok Gui = Default
  id = noGui
  (.) = inNew2 (\ (_,c) (a,_) -> (a,c))

instance OpCon (Prod Gui) (Sat Default) where inOp = Entail (Sub Dict)

instance ProductCat Gui where
  exl = noGui
  exr = noGui
  (&&&) = inNew2 (\ (a,c) (a',d) -> (a `mappend` a', c `PairO` d))

-- How to render sums?

instance OpCon (Exp Gui) (Sat Default) where inOp = Entail (Sub Dict)

instance ClosedCat Gui where
  apply = noGui
  curry (Gui (unPairI -> (a,b)) c) = Gui a (b :--> c)
  uncurry (Gui a (unFunO -> (b,c))) = Gui (PairI a b) c

{--------------------------------------------------------------------
    Instantiating GUIs --- a sketch for now
--------------------------------------------------------------------}

-- | Consumer / call-back / setter
type OI c = c -> IO ()

mkSliderI :: String -> Int -> Int -> Int -> OI Int -> IO (IO Int)
mkSliderI = error "mkSliderI: not yet implemented"

mkSliderO :: String -> Int -> Int -> Int -> IO (OI Int)
mkSliderO = error "mkSliderO: not yet implemented"

-- | Instantiate an input, given a value consumer/setter.
-- Returns a getter.
runI :: In c -> OI c -> IO (IO c)
runI (NoI a) _ = return (return a)
runI (SliderI label lo hi c0) k = mkSliderI label lo hi c0 k
runI (PairI ia ib) k =
  mdo let ka a = do { b <- getb ; k (a,b) }
          kb b = do { a <- geta ; k (a,b) }
          -- ka a = getb >>= k . (a,)
          -- kb b = geta >>= k . (,b)
      -- TODO: horizontal layout
      geta <- runI ia ka
      getb <- runI ib kb
      return (liftA2 (,) geta getb)

-- | Instantiate an output, given an initial value.
-- Returns a setter.
runO ::  Out c -> c -> IO (OI c)
runO NoO _ = return (const (return ()))
runO (SliderO label lo hi) c0 = mkSliderO label lo hi c0
runO (PairO oa ob) (a0,b0) =
  do -- TODO: horizontal layout
     ka <- runO oa a0
     kb <- runO ob b0
     return (\ (a,b) -> ka a >> kb b)
runO (ia :--> ob) f0 =
  do reff <- newIORef f0
     -- TODO: vertical layout
     kb   <- runO ob (f0 (initI ia)) -- or use geta and mdo
     let ka a = do { f <- readIORef reff ; kb (f a) }
                -- readIORef reff >>= kb . ($ a)
     geta <- runI ia ka
     return (\ f -> do { writeIORef reff f0 ; a <- geta ; kb (f a) })

-- Note that initial values are contained in an In but are given to runO. I
-- don't want to put initial values into outputs, since they'll get replaced
-- immediately with a sensible value. I think I need initial input values,
-- because I don't know what initial input value to use in a lambda.

