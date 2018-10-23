{-# LANGUAGE FlexibleContexts #-}
-- To run:
-- 
--   stack build :graphics-examples
--
--   stack build :graphics-trace >& ~/Haskell/concat/graphics/out/o1
-- 
-- You might also want to use stack's --file-watch flag for automatic recompilation.

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

{-# OPTIONS_GHC -dsuppress-idinfo #-}
{-# OPTIONS_GHC -dsuppress-uniques #-}
{-# OPTIONS_GHC -dsuppress-module-prefixes #-}

-- {-# OPTIONS_GHC -ddump-simpl #-}

-- {-# OPTIONS_GHC -ddump-rule-rewrites #-}
{-# OPTIONS_GHC -fsimpl-tick-factor=25 #-}  -- default 100
-- {-# OPTIONS_GHC -fsimpl-tick-factor=250 #-}  -- default 100

-- {-# OPTIONS -fplugin-opt=ConCat.Plugin:trace #-}

{-# OPTIONS_GHC -fno-do-lambda-eta-expansion #-}

module Main where

import Control.Applicative (liftA2,liftA3)
import GHC.Float (int2Double)   -- TEMP

import ConCat.Misc ((:*),R,sqr,magSqr,Unop,Binop,inNew,inNew2)
import ConCat.Circuit (GenBuses,(:>))
import ConCat.Graphics.GLSL
import ConCat.Graphics.Color (ToColor(..))
import ConCat.Graphics.Image
import qualified ConCat.RunCircuit as RC
import ConCat.Syntactic (Syn,render)
import ConCat.AltCat (Ok2,toCcc,(:**:)(..))
import qualified ConCat.AltCat as A

import ConCat.Rebox () -- necessary for reboxing rules to fire

main :: IO ()
main = sequence_
  [ putChar '\n' -- return ()

  -- , runHtml' "disk-sizing-a" (sliderW "Radius" (0,2) 1) $ disk
  -- , runHtml' "disk-sizing-b" timeW $ disk . cos
  -- , runHtml' "annulus1"
  --     (pairW (sliderW "Outer radius" (0,2) 1) (sliderW "Inner radius" (0,2) 0.1)) $
  --     uncurry annulus
  , runHtml' "annulus2" (pairW (sliderW "Outer" (0,2) 1) timeW) $
      \ (o,i) -> annulus o ((sin i + 1) / 2)

  -- , runSynCirc "wobbly-disk" $ toCcc $ \ t ->
  --     disk' (3/4 + 1/4 * cos t)
  -- , runSynCirc "wobbly-disk-color" $ toCcc $ toPImageC $ \ t ->
  --     disk' (3/4 + 1/4 * cos t)

  -- , runHtml' "wobbly-disk" timeW $ \ t ->
  --     disk' (3/4 + 1/4 * cos t)

  -- , runHtml' "diag-plus-im" timeW $ \ t ->
  --     \ ((x,y) :: R2) -> x + sin t > y
  -- , runHtml' "diag-disk-turning" timeW $ \ t ->
  --     udisk `intersectR` rotate t xPos
  -- , runHtml' "checker-rotate" timeW $ \ t ->
  --     rotate t checker15

  -- , runHtml' "diag-disk-turning-sizing" timeW $ \ t ->
  --     disk' (cos t) `xorR` rotate t xyPos

  -- , runHtml' "orbits1" timeW $ orbits1
  -- , runHtml' "checker-orbits1" timeW $
  --     liftA2 xorR (const checker15) orbits1
  -- , runHtml' "checker-orbits2" timeW $ \ t ->
  --     uscale (sin t + 1.05) checker `xorR` orbits1 t
  -- , runHtml' "checker-orbits3" timeW $ \ t -> 
  --     orbits1 t `intersectR` checker15
  -- , runHtml' "checker-orbits4" timeW $ \ t -> 
  --     orbits1 t `intersectR` translate (t/10,0) checker15
  -- , runHtml' "checker-orbits5" timeW $ \ t -> 
  --     orbits1 t `intersectR` rotate (t/10) checker15
  -- , runHtml' "orbits2" timeW $ orbits2
  -- , runHtml' "checker-orbits6" timeW $ \ t ->
  --     orbits2 t `intersectR` rotate (t/10) checker15

  -- , runHtml' "soft-disk-a" unitW (const (softDisk 1))
  -- , runHtml' "soft-disk-b" (sliderW "k" (0,100) 50) softDisk
  -- , runHtml' "disk-sdf-r" unitW (const (sdfR diskSdf))

  ]

{--------------------------------------------------------------------
    Testing utilities
--------------------------------------------------------------------}

type GO a b = (GenBuses a, Ok2 (:>) a b)

type EC = Syn :**: (:>)

runSyn :: Syn a b -> IO ()
runSyn syn = putStrLn ('\n' : render syn)

runCirc :: GO a b => String -> (a :> b) -> IO ()
runCirc nm circ = RC.run nm [] circ

runSynCirc :: GO a b => String -> EC a b -> IO ()
runSynCirc nm (syn :**: circ) = runSyn syn >> runCirc nm circ

runH :: (GenBuses a)
     => String -> Widgets a -> (a :> ImageC) -> IO ()
-- runH n w f = runHtml n w f
runH n w f = runHtml n w f >> runCirc n f

runHtml' :: (GenBuses a, ToColor c)
         => String -> Widgets a -> (a -> Image c) -> IO ()
runHtml' _ _ _ = error "runHtml' called directly"
{-# NOINLINE runHtml' #-}
{-# RULES "runHtml'"
  forall n w f. runHtml' n w f = runH n w $ toCcc $ toPImageC f #-}

-- runHtml' name widgets f =
--   runH name widgets $ toCcc $ toPImageC f
-- {-# INLINE runHtml' #-}


{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

later :: Num t => t -> Unop (t -> a)
later dt f = f . subtract dt

orbits1 :: R -> Region
orbits1 z = translate (cos theta,0) d `xorR` translate (0,sin theta) d
 where
   d = disk (1/2)
   theta = z * 2

orbits2 :: R -> Region
orbits2 z =
  translate (cos theta,0) (disk r1) `xorR` translate (0,sin theta) (disk r2)
 where
   r1 = (sin (z * 3) + 1) / 2
   r2 = 1 - r1
   theta = z * 2

checker15 :: Region
checker15 = uscale (1/5) checker

exampleB :: R -> Region
exampleB = \ t -> let s = sin t in \ (x,y) -> x > y + s

exampleC :: R -> R -> R
exampleC = \ t -> let s = sin t in \ x -> x + s

exampleC2 :: EC R (R -> R)
exampleC2 = A.curry (A.addC A.. (A.exr A.&&& A.sinC A.. A.exl))

exampleC3 :: EC R (R -> R)
exampleC3 = A.curry (A.addC A.. (A.exr A.&&& A.exl)) A.. A.sinC

exampleC3' :: ( A.ClosedCat k, A.MonoidalPCat k, A.FloatingCat k R, A.NumCat k R
              , A.Ok k (R :* R), A.Ok k (R -> R) )
           => R `k` (R -> R)
exampleC3' = A.curry (A.addC A.. (A.exr A.&&& A.exl)) A.. A.sinC

-- Swap addends
exampleD :: R -> R -> R
exampleD = \ t -> let s = sin t in \ x -> s + x

-- Soft-edged unit disk
softDisk :: R -> Image R
softDisk k p = 1 / (1 + magSqr p ** k)

-- Disk SDF (signed distance field)
diskSdf :: Image R
diskSdf p = 1 - magSqr p

-- SDF to region
sdfR :: Image R -> Region
-- sdfR im p = im p > 0
-- sdfR im = (> 0) . im
sdfR = ((> 0) .)
