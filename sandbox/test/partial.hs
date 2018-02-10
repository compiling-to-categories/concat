-- Try to "see" partial function implementation in Core.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -ddump-simpl #-}

import GHC.TypeLits
import Data.Proxy
import Data.Finite hiding (finite)
import Data.Finite.Internal (Finite(..))
import Data.Reflection

-- A safer form of `finite`.
finite :: (KnownNat n, KnownNat m, (n <=? m) ~ 'False) => Proxy m -> Finite n
finite p = Finite $ natVal p
-- finite = Finite . natVal  -- I think I can't do this reduction, if I want the inlining to work; is that right?
{-# INLINE finite #-}


-- A safer form of `getFinite`.
-- reifyNat :: forall r. Integer -> (forall n. KnownNat n => Proxy n -> r) -> r
getFinite' :: KnownNat n => Finite n -> (forall m. (KnownNat m, (n <=? m) ~ 'False) => Proxy m -> r) -> r
getFinite' x f = reifyNat (getFinite x) f
-- getFinite' = reifyNat . getFinite  -- I think I can't do this reduction, if I want the inlining to work; is that right?
{-# INLINE getFinite' #-}


main :: IO ()
main = do
  -- putStrLn $ "\ntoFin False = " ++ show (toFin False)
  putStrLn $ "\ntoFin' (Left ()) = "    ++ show (toFin' (Left  ()))
  putStrLn $ "\ntoFin' (Right True) = " ++ show (toFin' (Right True))


toFin :: Bool -> Finite 2
toFin False = finite (Proxy @0)
toFin True  = finite (Proxy @1)


toFin' :: Either () Bool -> Finite 3
toFin' (Left  _) = getFinite' (toFin'' ()) finite
toFin' (Right p) = getFinite' (toFin    p) finite


toFin'' :: () -> Finite 1
toFin'' _ = finite (Proxy @0)

