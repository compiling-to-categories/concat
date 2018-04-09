{-# LANGUAGE CPP                    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ParallelListComp       #-}
{-# LANGUAGE PartialTypeSignatures  #-}
{-# LANGUAGE PatternGuards          #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-} -- See below

-- experiment
-- {-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- #define TESTING

#ifdef TESTING
{-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP
#endif

-- #define GenericPowFFT

----------------------------------------------------------------------
-- | Generic FFT
----------------------------------------------------------------------

module ConCat.FFT
  ( dft, FFT(..), DFTTy, genericFft, GFFT
  -- -- Temporary while debugging
  , twiddle, twiddles, omega, cis
  , o8sq
  ) where

import Prelude hiding (zipWith)

import Data.Complex
-- import Control.Applicative (liftA2)
import GHC.Generics hiding (C,S)

import Data.Key (Zip(..))
import Data.Pointed

#ifdef TESTING
import Data.Foldable (toList)
-- import Test.QuickCheck (quickCheck)
import Test.QuickCheck.All (quickCheckAll)
import ShapedTypes.ApproxEq
#endif

import ConCat.Misc (Unop,transpose,C,inGeneric1,inComp)
import ConCat.Sized
import ConCat.Scan (LScan,lproducts)
import ConCat.Pair
import ConCat.Free.LinearRow (($*))

{--------------------------------------------------------------------
    DFT
--------------------------------------------------------------------}

type AS  h = (Pointed h, Zip h, LScan h)
type ASZ h = (AS h, Sized h)

-- To resolve: Zip vs Applicative. traverse/transpose needs Applicative.

dft :: forall f a. (ASZ f, Foldable f, RealFloat a) => Unop (f (Complex a))
dft xs = omegas (size @f) $* xs
{-# INLINE dft #-}

omegas :: (AS f, AS g, RealFloat a) => Int -> g (f (Complex a))
omegas = fmap powers . powers . omega
-- omegas n = powers <$> powers (omega n)
-- omegas n = powers <$> powers (exp (- i * 2 * pi / fromIntegral n))
{-# INLINE omegas #-}

omegas' :: forall f g a. (ASZ f, ASZ g, RealFloat a) => g (f (Complex a))
omegas' = fmap powers (powers (cis (- 2 * pi / fromIntegral (size @(g :.: f)))))

-- i :: Num a => Complex a
-- i = 0 :+ 1

omega :: RealFloat a => Int -> Complex a
omega n = cis (- 2 * pi / fromIntegral n)
-- omega n = exp (0 :+ (- 2 * pi / fromIntegral n))
-- omega n = exp (- 2 * (0:+1) * pi / fromIntegral n)
{-# INLINE omega #-}

{--------------------------------------------------------------------
    FFT
--------------------------------------------------------------------}

type DFTTy f = forall a. RealFloat a => f (Complex a) -> FFO f (Complex a)

class FFT f where
  type FFO f :: * -> *
  fft :: DFTTy f
  -- default fft :: ( Generic1 f, Generic1 (FFO f)
  --                , FFT (Rep1 f), FFO (Rep1 f) ~ Rep1 (FFO f) ) => DFTTy f
  -- fft = genericFft
  -- Temporary hack to avoid newtype-like representation.
  fftDummy :: f a
  fftDummy = undefined

-- TODO: Eliminate FFO, in favor of fft :: Unop (f (Complex a)).
-- Use dft as spec.

twiddle :: forall g f a. (ASZ g, ASZ f, RealFloat a) => Unop (g (f (Complex a)))
-- twiddle = (zipWith.zipWith) (*) twiddles
twiddle = (zipWith.zipWith) (*) omegas'
-- twiddle = (zipWith.zipWith) (*) (omegas (size @(g :.: f)))
{-# INLINE twiddle #-}

twiddles :: forall g f a. (ASZ g, ASZ f, RealFloat a) => g (f (Complex a))
twiddles = omegas (size @(g :.: f))
{-# INLINE twiddles #-}

o8sq :: C
o8sq = omega (8 :: Int) ^ (2 :: Int)

-- Powers of x, starting x^0. Uses 'LScan' for log parallel time
powers :: (LScan f, Pointed f, Num a) => a -> f a
powers = fst . lproducts . point
{-# INLINE powers #-}

-- TODO: Consolidate with powers in TreeTest and rename sensibly. Maybe use
-- "In" and "Ex" suffixes to distinguish inclusive and exclusive cases.

{--------------------------------------------------------------------
    Generic support
--------------------------------------------------------------------}

instance FFT Par1 where
  type FFO Par1 = Par1
  fft = id

#if 0
inTranspose :: (Traversable f', Traversable g, Applicative g', Applicative f)
            => (f (g a) -> f' (g' a)) -> g (f a) -> g' (f' a)
inTranspose = transpose <-- transpose

ffts' :: ( FFT g, Traversable f, Traversable g
         , Applicative (FFO g), Applicative f, RealFloat a) =>
     g (f (Complex a)) -> FFO g (f (Complex a))
ffts' = transpose . fmap fft . transpose
#endif

#if 0

transpose :: g (f C)     -> f (g C)
fmap fft  :: f (g C)     -> f (FFO g C)
transpose :: f (FFO g C) -> FFO g (f C)

#endif

instance ( Zip f,  Traversable f , Traversable g
         , Applicative f, Applicative (FFO f), Applicative (FFO g), Zip (FFO g)
         , Pointed f, Traversable (FFO g), Pointed (FFO g)
         , FFT f, FFT g, LScan f, LScan (FFO g), Sized f, Sized (FFO g) )
      => FFT (g :.: f) where
  type FFO (g :.: f) = FFO f :.: FFO g
  fft = inComp (traverse fft . twiddle . traverse fft . transpose)
  -- fft = inComp (ffts' . transpose . twiddle . ffts')
  {-# INLINE fft #-}

#if 0
  fft = Comp1 . transpose . fmap fft . twiddle . transpose . fmap fft . transpose . unComp1
  fft = Comp1 . traverse fft . twiddle . traverse fft . transpose . unComp1

-- Types in fft for (g :. f):
  unComp1   :: (g :. f) a -> g  (f  a)
  transpose :: g  (f  a)  -> f  (g  a)
  fmap fft  :: f  (g  a)  -> f  (g' a)
  transpose :: f  (g' a)  -> g' (f  a)
  twiddle   :: g' (f  a)  -> g' (f  a)
  fmap fft  :: g' (f  a)  -> g' (f' a)
  transpose :: g' (f' a)  -> f' (g' a)
  Comp1     :: f' (g' a)  -> (f' :. g') a
#endif

#if 0

--   fft = inComp (ffts' . transpose . twiddle . ffts')

ffts'     :: g (f C)     -> FFO g (f C)
twiddle   :: FFO g (f C) -> FFO g (f C)
transpose :: FFO g (f C) -> f (FFO g C)
ffts'     :: f (FFO g C) -> FFO f (FFO g C)

#endif

-- -- Generalization of 'dft' to traversables. Note that liftA2 should
-- -- work zippily (unlike with lists).
-- dftT :: forall f a. (ASZ f, Traversable f, RealFloat a)
--      => Unop (f (Complex a))
-- dftT xs = out <$> indices
--  where
--    out k   = sum (liftA2 (\ n x -> x * ok^n) indices xs) where ok = om ^ k
--    indices = fst iota :: f Int
--    om      = omega (size @f)
-- {-# INLINE dftT #-}

-- | Generic FFT
genericFft :: ( Generic1 f, Generic1 (FFO f)
              , FFT (Rep1 f), FFO (Rep1 f) ~ Rep1 (FFO f) ) => DFTTy f
genericFft = inGeneric1 fft

type GFFT f = (Generic1 f, Generic1 (FFO f), FFT (Rep1 f), FFO (Rep1 f) ~ Rep1 (FFO f))

#define GenericFFT(f,g) instance GFFT (f) => FFT (f) where { type FFO (f) = (g); fft = genericFft }

-- #define GenericFFT(f,g) instance GFFT (f) => FFT (f) where { type FFO (f) = g; INLINE }

-- TODO: Replace Applicative with Zippable.
-- Can't, because Traversable needs Applicative.

-- Perhaps dftT isn't very useful. Its result and argument types match, unlike fft.

{--------------------------------------------------------------------
    Specialized FFT instances.
--------------------------------------------------------------------}

-- I put the specific instances here in order to avoid an import loop between
-- the LPow and RPow modules. I'd still like to find an elegant FFT that maps f
-- to f, and then move the instances to RPow and LPow.

-- Radix 2 butterfly
instance FFT Pair where
  type FFO Pair = Pair
  -- bogus "non-exhaustive" warning in ghc 8.0.2
  -- fft (a :# b) = (a + b) :# (a - b)
  fft = \ (a :# b) -> (a + b) :# (a - b)
  -- fft = dft
  {-# INLINE fft #-}

#ifdef TESTING

#if 0
twiddles :: (ASZ g, ASZ f, RealFloat a) => g (f (Complex a))

as :: f C
(<.> as) :: f C -> C
twiddles :: f (f C)
(<.> as) <$> twiddles :: f C
#endif

-- -- Binary dot product
-- infixl 7 <.>
-- (<.>) :: (Foldable f, Applicative f, Num a) => f a -> f a -> a
-- u <.> v = sum (liftA2 (*) u v)

{--------------------------------------------------------------------
    Simple, quadratic DFT (for specification & testing)
--------------------------------------------------------------------}

-- Adapted from Dave's definition
dftL :: RealFloat a => Unop [Complex a]
dftL xs = [ sum [ x * ok^n | x <- xs | n <- [0 :: Int ..] ]
          | k <- [0 .. length xs - 1], let ok = om ^ k ]
 where
   om = omega (length xs)

{--------------------------------------------------------------------
    Tests
--------------------------------------------------------------------}

-- > powers 2 :: LTree N2 Int
-- B (B (L ((1 :# 2) :# (4 :# 8))))
-- > powers 2 :: LTree N3 Int
-- B (B (B (L (((1 :# 2) :# (4 :# 8)) :# ((16 :# 32) :# (64 :# 128))))))

fftl :: (FFT f, Foldable (FFO f), RealFloat a) => f (Complex a) -> [Complex a]
fftl = toList . fft

type LTree = L.Pow Pair
type RTree = R.Pow Pair

type LC n = LTree n C
type RC n = RTree n C

p1 :: Pair C
p1 = 1 :# 0

tw1 :: LTree N1 (Pair C)
tw1 = twiddles

tw2 :: RTree N2 (Pair C)
tw2 = twiddles

tw3 :: RTree N2 (RTree N2 C)
tw3 = twiddles

tw3' :: [[C]]
tw3' = toList (toList <$> tw3)


-- Adapted from Dave's testing

-- test :: (FFT f, Foldable f, Foldable (FFO f)) => f C -> IO ()
-- test fx =
--   do ps "\nTesting input" xs
--      ps "Expected output" (dftL xs)
--      ps "Actual output  " (toList (fft fx))
--  where
--    ps label z = putStrLn (label ++ ": " ++ show z)
--    xs = toList fx

#if 0
t0 :: LC N0
t0 = L.fromList [1]

t1 :: LC N1
t1 = L.fromList [1, 0]

t2s :: [LC N2]
t2s = L.fromList <$>
        [ [1,  0,  0,  0]  -- Delta
        , [1,  1,  1,  1]  -- Constant
        , [1, -1,  1, -1]  -- Nyquist
        , [1,  0, -1,  0]  -- Fundamental
        , [0,  1,  0, -1]  -- Fundamental w/ 90-deg. phase lag
       ]

tests :: IO ()
tests = do test p1
           test t0
           test t1
           mapM_ test t2s
#endif

infix 4 ===
(===) :: Eq b => (a -> b) -> (a -> b) -> a -> Bool
(f === g) x = f x == g x

infix 4 =~=
(=~=) :: ApproxEq b => (a -> b) -> (a -> b) -> a -> Bool
(f =~= g) x = f x =~ g x

fftIsDftL :: (FFT f, Foldable f, Foldable (FFO f), RealFloat a, ApproxEq a) =>
             f (Complex a) -> Bool
fftIsDftL = toList . fft =~= dftL . toList

dftTIsDftL :: (ASZ f, Traversable f, RealFloat a, ApproxEq a) =>
              f (Complex a) -> Bool
dftTIsDftL = toList . dftT =~= dftL . toList

dftIsDftL :: (ASZ f, Foldable f, RealFloat a, ApproxEq a) =>
             f (Complex a) -> Bool
dftIsDftL = toList . dft =~= dftL . toList

-- -- TEMP:
-- dftDft :: (ASZ f, Traversable f, RealFloat a, ApproxEq a) =>
--           f (Complex a) -> ([Complex a], [Complex a])
-- dftDft xs = (toList . dft $ xs, dftL . toList $ xs)

{--------------------------------------------------------------------
    Properties to test
--------------------------------------------------------------------}

transposeTwiddleCommutes :: (ASZ g, Traversable g, ASZ f, (ApproxEq (f (g C))))
                         => g (f C) -> Bool
transposeTwiddleCommutes =
 twiddle . transpose =~= transpose . twiddle

prop_transposeTwiddle_L3P :: LTree N3 (Pair C) -> Bool
prop_transposeTwiddle_L3P = transposeTwiddleCommutes

prop_transposeTwiddle_R3P :: RTree N3 (Pair C) -> Bool
prop_transposeTwiddle_R3P = transposeTwiddleCommutes

-- dft tests fail. Hm!

-- prop_dft_R3 :: RTree N3 C -> Bool
-- prop_dft_R3 = dftIsDftL

-- prop_dft_L3 :: LTree N3 C -> Bool
-- prop_dft_L3 = dftIsDftL

prop_dftT_p :: Pair C -> Bool
prop_dftT_p = dftTIsDftL

prop_dftT_L3 :: LTree N3 C -> Bool
prop_dftT_L3 = dftTIsDftL

prop_dftT_R3 :: RTree N3 C -> Bool
prop_dftT_R3 = dftTIsDftL

prop_fft_p :: Pair C -> Bool
prop_fft_p = fftIsDftL

prop_fft_L1 :: LTree N1 C -> Bool
prop_fft_L1 = fftIsDftL

prop_fft_L2 :: LTree N2 C -> Bool
prop_fft_L2 = fftIsDftL

prop_fft_L3 :: LTree N3 C -> Bool
prop_fft_L3 = fftIsDftL

prop_fft_L4 :: LTree N4 C -> Bool
prop_fft_L4 = fftIsDftL

prop_fft_R1 :: RTree N1 C -> Bool
prop_fft_R1 = fftIsDftL

prop_fft_R2 :: RTree N2 C -> Bool
prop_fft_R2 = fftIsDftL

prop_fft_R3 :: RTree N3 C -> Bool
prop_fft_R3 = fftIsDftL

prop_fft_R4 :: RTree N4 C -> Bool
prop_fft_R4 = fftIsDftL

-- TH oddity
return []

runTests :: IO Bool
runTests = $quickCheckAll

-- end of tests
#endif

