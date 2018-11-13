{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

#define TESTING

#ifdef TESTING
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
#endif

-- | Determine whether the plugin can handle a type. Used in ConCat.Plugin.

module ConCat.OkType (OkType) where

#ifdef TESTING
import ConCat.Misc (Unop)
#endif
import ConCat.Rep

class OkType t

instance OkType ()
instance OkType Bool
instance OkType Int
instance OkType Integer
instance OkType Float
instance OkType Double

instance (OkType a, OkType b) => OkType (a ,  b)
instance (OkType a, OkType b) => OkType (a -> b)

instance {-# overlappable #-} (HasRep t, OkType (Rep t)) => OkType t

#ifdef TESTING

ok :: OkType t => Unop t
ok = id

ok1 = ok :: Unop Int
ok2 = ok :: Unop (Bool,Int)
ok3 = ok :: Unop (Bool,Int,Bool)

#endif

