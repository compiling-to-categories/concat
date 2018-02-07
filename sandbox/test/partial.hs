-- Try to "see" partial function implementation in Core.

{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -ddump-simpl #-}

-- import GHC.TypeLits
import Data.Finite

main :: IO ()
main = do
  putStrLn $ "\ntoFin False = " ++ show (toFin False)

toFin :: Bool -> Finite 2
toFin False = finite 0
toFin True  = finite 1

