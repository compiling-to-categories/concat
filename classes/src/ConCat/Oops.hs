{-# OPTIONS_GHC -O0 -fno-strictness #-}
module ConCat.Oops(oops) where

-- Both -O0 -fno-strictness are necessary to keep ghc 9 from
-- discovering that this bombs.

-- | Pseudo function to fool GHC's divergence checker.
oops :: String -> b
oops str = error ("Oops: "++str)
{-# NOINLINE oops #-}

