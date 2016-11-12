-- Macro to declare various class instances for types with HasRep instances. To
-- use this macro with your own types, use the AbsTyPragmas macro in your
-- language pragmas section and AbsTyImports in your imports section.

#define AbsTy(abs) \
instance GenBuses (Rep (abs)) => GenBuses (abs) where \
  { genBuses' = genBusesRep' ; delay = delayCRep ; ty = tyRep }; \
instance BottomCat (:>) (Rep (abs)) => BottomCat (:>) (abs) where \
  { bottomC = bottomRep };\
instance IfCat (:>) (Rep (abs)) => IfCat (:>) (abs) where { ifC = repIf };\
-- instance OkayArr k q_q (abs) => Uncurriable k q_q (abs) where uncurries = id

#define AbsTyPragmas \
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, FlexibleInstances #-}

#define AbsTyImports \
import Circat.Category (Uncurriable(..){-,OkayArr-}) ;\
import Circat.Classes (BottomCat(..),IfCat(..),repIf) ;\
import Circat.Circuit (GenBuses(..),delayCRep,tyRep,bottomRep,genBusesRep',(:>));
