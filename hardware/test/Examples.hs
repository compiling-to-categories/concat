-- To run:
--
--   stack build :hardware-examples
--
--   stack build :hardware-trace >& ~/Haskell/concat/hardware/out/o1
--
-- You might also want to use stack's --file-watch flag for automatic recompilation.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DeriveFoldable      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}
-- {-# OPTIONS_GHC -fsimpl-tick-factor=250 #-}  -- default 100

-- {-# OPTIONS -fplugin-opt=ConCat.Plugin:trace #-}

{-# OPTIONS_GHC -fno-do-lambda-eta-expansion #-}

module Main where

import Control.Applicative (liftA2,liftA3)
import Data.Complex
import Data.List           (mapAccumL)
import GHC.Float (int2Double)   -- TEMP
import GHC.Generics hiding (S)
-- import ShapedTypes.FFT

import ConCat.Pair
import ConCat.FFT
import ConCat.Misc ((:*),R,sqr,magSqr,Unop,Binop,inNew,inNew2,(:+))
import ConCat.Circuit (GenBuses(..),(:>),Ty(..),Buses(..))
import qualified ConCat.RunCircuit as RC
import ConCat.Syntactic (Syn,render)
import ConCat.AltCat (Ok2,ccc,(:**:)(..))
import qualified ConCat.AltCat as A

import ConCat.Rebox () -- necessary for reboxing rules to fire

import ConCat.Hardware.Verilog
import ConCat.Rep

main :: IO ()
main = sequence_
  [ putChar '\n' -- return ()
    -- Unary
  -- , runVerilog' "neg" $ \ (x :: Int) -> - x  -- Yields bit inversion, not 2's complement!
  -- , runVerilog' "odd" $ \ (x :: Int) -> x `mod` 2

    -- Binary
  -- , runVerilog' "adder" $ \ (x :: Int, y :: Int) -> x + y

    -- Conditional
  -- , runVerilog' "cond" $ \ (p :: Bool, x :: Int, y :: Int) -> if p then x else y

    -- FFT, via functor composition
  -- , runVerilog' "fft_fc_pair" $ \ ( pr :: (UPair (Complex Double)) ) -> fft pr
  -- , runVerilog' "fft_fc_pair" $ \ ( (x0::(Complex Double)) :# x1 ) -> fft (x0 :# x1)
  -- , runVerilog' "fft_fc_quad" $ \ ( fc :: ( (UPair :. UPair) (Complex Double) ) ) -> fft fc
  -- , runVerilog' "fft_fc_quad" $ \ ( fc :: ( (UPair :.: UPair) (Complex Double) ) ) -> fft fc
  -- , runVerilog' "fft_fc_quad" $ \ (x0::(Complex Double),x1,x2,x3) -> fft $ O (Comp1 ( (x0 :# x1) :# (x2 :# x3) ))
  -- , runVerilog' "fft_fc_quad" $ \ (Par1 x0, Par1 x1, Par1 x2, Par1 x3) -> fft $ O (Comp1 ( (x0 :# x1) :# (x2 :# x3) ))
  -- , runVerilog' "fft_fc_quad" $ \ (Par1 (x0::(Complex Double)), Par1 x1, Par1 x2, Par1 x3) -> fft $ Comp1 ( (x0 :# x1) :# (x2 :# x3) )
  , runVerilog' "fft_fc_quad" $ \ ( fc :: ( (Pair :.: Pair) (Complex Double) )) -> fft fc
  ]

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

runVerilog' :: (GenBuses a, GenBuses b) => String -> (a -> b) -> IO ()
runVerilog' _ _ = error "runVerilog' called directly"
{-# NOINLINE runVerilog' #-}
{-# RULES "runVerilog'"
  forall n f. runVerilog' n f = runVerilog n $ ccc f #-}

{--------------------------------------------------------------------
    FFT, via functor composition, machinery.
--------------------------------------------------------------------}
-- TODO: Does Conal maintain this in a library, which I should import from?
{-
-- Generic
type UPair = Par1  :*: Par1
type UQuad = UPair :.: UPair

pattern (:#) :: forall t. t -> t -> (:*:) Par1 Par1 t
pattern x :# y = Par1 x :*: Par1 y

instance FFT UPair where
  type Reverse UPair = UPair
  fft (x :# y) = (x + y) :# (x - y)
  fft _        = undefined

instance Sized Par1 where
  size = 1

instance (Sized f, Sized g) => Sized (g :*: f) where
    size = size @f + size @g

instance (Sized f, Sized g) => Sized (g :.: f) where
    size = size @f * size @g

instance ( Traversable f, Traversable g, Traversable (Reverse g)
         , Applicative f, Applicative (Reverse f) , Applicative (Reverse g)
         , FFT f, FFT g
         , Sized f , Sized (Reverse g) ) => FFT (g :.: f) where
  type Reverse (g :.: f) = Reverse f :.: Reverse g
  fft = Comp1 . fft' . transpose . twiddle . fft' . unComp1

-- Concrete
newtype (g :. f) a = O (g (f a))
  deriving (Eq, Functor, Foldable, Traversable)

instance (Show (g (f a))) => Show ((g :. f) a) where
  show (O x) = "O (" ++ show x ++ ")"

instance (Applicative f, Applicative g) => Applicative (g :. f) where
  pure = O . pure . pure
  O h <*> (O x) = O $ fmap (<*>) h <*> x

class Sized (f :: * -> *) where
    size :: Integer

instance (Sized f, Sized g) => Sized (g :. f) where
    size = size @f * size @g

class FFT f where
  type Reverse f :: * -> *
  fft :: RealFloat a => f (Complex a) -> Reverse f (Complex a)

instance (Traversable g, Traversable (Reverse g),
          Applicative (Reverse g),
          FFT g,
          Traversable f,
          Applicative f, Applicative (Reverse f),
          FFT f, Sized f, Sized (Reverse g) ) =>
  FFT (g :. f) where
    type Reverse (g :. f) = Reverse f :. Reverse g
    fft = O . fft' . transpose . twiddle . fft' . unO

fft' :: ( Traversable g
        , Applicative (Reverse g)
        , FFT g
        , Traversable f
        , Applicative f
        , RealFloat a ) =>
  g (f (Complex a)) -> Reverse g (f (Complex a))
fft' = transpose . fmap fft . transpose

twiddle :: forall g f a. ( Applicative g, Traversable g, Sized g
                         , Applicative f, Traversable f, Sized f
                         , RealFloat a ) =>
  g (f (Complex a)) -> g (f (Complex a))
twiddle = (liftA2 . liftA2) (*) (omegas (size @(g :. f)))

omegas :: ( Applicative g, Traversable g
          , Applicative f, Traversable f
          , RealFloat a) =>
  Integer -> g (f (Complex a))
omegas n = powers <$> powers (cis (2 * pi / fromIntegral n))

powers :: ( Applicative f, Traversable f
          , Fractional a) => a -> f a
powers w = fmap (/ w) . snd . mapAccumL (\x y -> (x * y, x * y)) 1 $ pure w

unO :: (g :. f) a -> g (f a)
unO (O x) = x

transpose :: (Traversable g, Applicative f) => g (f a) -> f (g a)
transpose = sequenceA
-}

