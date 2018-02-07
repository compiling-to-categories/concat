-- Try to "see" partial function implementation in Core.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -ddump-simpl #-}

import GHC.TypeLits
import Data.Proxy
import Data.Finite

main :: IO ()
main = do
  -- putStrLn $ "\ntoFin False = " ++ show (toFin False)
  putStrLn $ "\ntoFin' (Left ()) = "    ++ show (toFin' (Left  ()))
  putStrLn $ "\ntoFin' (Right True) = " ++ show (toFin' (Right True))

toFin :: Bool -> Finite 2
toFin False = finite 0
toFin True  = finite 1

toFin' :: Either () Bool -> Finite 3
toFin' (Left  _) = (finite . getFinite . toFin'') ()
toFin' (Right p) = finite $ natVal (Proxy @1) + (getFinite . toFin) p

toFin'' :: () -> Finite 1
toFin'' _ = finite 0

