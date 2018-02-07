-- Test case for new HasFin instances in TArr.hs.
--
-- Original author: David Banas <capn.freako@gmail.com>
-- Original date: February 1, 2018
--
-- Copyright (c) 2018 David Banas; all rights reserved World wide.

-- newtype Arr a b = Arr (Vector (Card a) b)

-- (!) :: HasFin a => Arr a b -> (a -> b)
-- Arr v ! a = v `index` toFin a

{-# LANGUAGE TypeOperators #-}

module Main where

import Data.Vector.Sized

import ConCat.Misc
import ConCat.TArr

v1 = singleton 2
v2 = 3 `cons` v1
v3 = 4 `cons` v2
v4 = 5 `cons` v3

main :: IO ()
main = do
  putStr "\nTesting (): "
  if fetched == 2
     then putStrLn "PASS"
     else putStrLn "FAIL"
  putStr "Testing Bool: "
  if fetched2 False == 3 && fetched2 True == 2
     then putStrLn "PASS"
     else putStrLn "FAIL"
  putStr "Testing (Bool :+ ()): "
  if fetched3 (Right ()) == 2
     && fetched3 (Left False) == 4
     && fetched3 (Left True) == 3
     then putStrLn "PASS"
     else putStrLn "FAIL"
  putStr "Testing (Bool :* Bool): "
  if fetched4 (True,True) == 2
     && fetched4 (True,False) == 3
     && fetched4 (False,True) == 4
     && fetched4 (False,False) == 5
     then putStrLn "PASS"
     else putStrLn "FAIL"


stored :: Arr () Int
stored = Arr v1

fetched :: Int
fetched = stored ! ()

stored2 :: Arr Bool Int
stored2 = Arr v2

fetched2 :: Bool -> Int
fetched2 p = stored2 ! p

stored3 :: Arr (Bool :+ ()) Int
stored3 = Arr v3

fetched3 :: (Bool :+ ()) -> Int
fetched3 e = stored3 ! e

stored4 :: Arr (Bool :* Bool) Int
stored4 = Arr v4

fetched4 :: (Bool :* Bool) -> Int
fetched4 p = stored4 ! p

