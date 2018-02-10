-- Exercise the ghc-typelits-natnormalize package.

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

import Data.Proxy
import GHC.TypeLits

proxyFun6 :: Proxy (2^k) -> Proxy (2^k)
proxyFun6 = const Proxy

test1 :: Proxy 7
test1 = proxyFun6 (Proxy :: Proxy 7)

test2 :: Proxy 8
test2 = proxyFun6 (Proxy :: Proxy 8)

main :: IO ()
main = do
  putStrLn ""
  putStrLn $ show test1
  putStrLn $ show test2

