-- Macro to declare various class instances for types with HasRep instances. To
-- use this macro with your own types, use the AbsTyPragmas macro in your
-- language pragmas section and AbsTyImports in your imports section.

#define AbsTy(abs) \
instance GenBuses (Rep (abs)) => GenBuses (abs) where \
  { genBuses' = genBusesRep' ; delay = delayCRep ; ty = tyRep }; \
instance ConstCat (:>) (Rep (abs)) => ConstCat (:>) (abs) where \
  { const = repConst } ; \
instance BottomCat (:>) (Rep (abs)) => BottomCat (:>) (abs) where \
  { bottomC = bottomRep };\
instance IfCat (:>) (Rep (abs)) => IfCat (:>) (abs) where { ifC = repIf };\
instance Uncurriable k _a_ (abs) where uncurries f = f ; {-# INLINE uncurries #-}

#define AbsTyPragmas \
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, FlexibleInstances #-}

#define AbsTyImports \
import ConCat.AltCat (BottomCat(..),IfCat(..),repIf,Uncurriable(..),constRepr) ;\
import ConCat.Circuit (GenBuses(..),delayCRep,tyRep,bottomRep,genBusesRep',(:>));
