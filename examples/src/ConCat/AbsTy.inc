-- Macro to declare various class instances for types with HasRep instances. To
-- use this macro with your own types, use the AbsTyPragmas macro in your
-- language pragmas section and AbsTyImports in your imports section.

#define AbsTy(abs) \
instance (OkCAR (abs)) => GenBuses (abs) where \
  { genBuses' = genBusesRep' {- ; delay = delayCRep -} ; ty = tyRep @(abs) ; unflattenB' = genUnflattenB' }; \
instance ({-OkCAR (abs), -} GenBuses z, GenBuses (Rep (abs)), ConCat.Category.BottomCat (:>) z (Rep (abs))) => ConCat.Category.BottomCat (:>) z (abs) where \
  { bottomC = bottomRep }; \
instance (OkCAR (abs), ConCat.Category.IfCat (:>) (Rep (abs))) => ConCat.Category.IfCat (:>) (abs) where { ifC = ConCat.Category.repIf };

--  \
-- instance Uncurriable k _a_ (abs) where uncurries f = f ; {-# INLINE uncurries #-}

-- See 2016-01-13 notes on "bottom evaluated"
-- instance (OkCAR (abs), ConstCat (:>) (Rep (abs))) => ConstCat (:>) (abs) where \
--   { const = repConst } ; \

#define AbsTyPragmas \
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, FlexibleInstances, TypeApplications #-}

#define AbsTyImports \
import qualified ConCat.Category ;\
import ConCat.Circuit (GenBuses(..){-,delayCRep-},tyRep,bottomRep,genBusesRep',genUnflattenB',(:>),OkCAR);

-- import ConCat.AltCat (BottomCat(..),IfCat(..),repIf,Uncurriable(..)) ;\
