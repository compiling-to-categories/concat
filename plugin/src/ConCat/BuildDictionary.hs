{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.BuildDictionary
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Adaptation of HERMIT's buildDictionaryT
----------------------------------------------------------------------

module ConCat.BuildDictionary (buildDictionary) where

import Data.Monoid (Any(..))
import Data.Char (isSpace)
import Data.Data (Data)
import Data.Generics (mkQ,everything)
import Control.Monad (filterM)
import System.IO.Unsafe (unsafePerformIO)

import GhcPlugins

import Control.Arrow (second)

import TyCoRep (CoercionHole(..))
import TcHsSyn (emptyZonkEnv,zonkEvBinds)
import           TcRnMonad (getCtLocM)
import           TcRnTypes (cc_ev)
import TcSMonad (runTcS)
import TcEvidence (evBindMapBinds)
import TcErrors(warnAllUnsolved)

import DsMonad
import DsBinds
import           TcSimplify
import           TcRnTypes
import ErrUtils (pprErrMsgBagWithLoc)
import Encoding (zEncodeString)
import Unique (mkUniqueGrimily)
import Finder (findExposedPackageModule)

import TcRnDriver
-- Temp
-- import HERMIT.GHC.Typechecker (initTcFromModGuts)
-- import ConCat.GHC

isFound :: FindResult -> Bool
isFound (Found _ _) = True
isFound _           = False

moduleIsOkay :: HscEnv -> ModuleName -> IO Bool
moduleIsOkay env mname = isFound <$> findExposedPackageModule env mname Nothing
       
runTcMUnsafe :: HscEnv -> DynFlags -> ModGuts -> TcM a -> a
runTcMUnsafe env0 dflags guts m = unsafePerformIO $ do
    -- Remove hidden modules from dep_orphans
    orphans <- filterM (moduleIsOkay env0) (moduleName <$> dep_orphs (mg_deps guts))
    (msgs, mr) <- runTcInteractive (env orphans) m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat $
              text "Errors:"   : pprErrMsgBagWithLoc errs
           ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (fail $ showMsgs msgs) return mr
 where
   imports0 = ic_imports (hsc_IC env0)
   -- imports0 shows up empty for my uses. Add GHC.Float and ConCat.Orphans for
   -- orphans, plus GHC.Generics for its newtypes (Coercible).
   -- TODO: find a better way.
   -- Hack: these ones lead to "Failed to load interface for ..."
                      -- mkModuleName <$> ["GHC.Float"","GHC.Exts","ConCat.Orphans","ConCat.AD"]
                      -- map moduleName (dep_orphs (mg_deps guts))
   env :: [ModuleName] -> HscEnv
   env extraModuleNames = 

         -- pprTrace "runTcMUnsafe extraModuleNames" (ppr extraModuleNames) $
         -- pprTrace "runTcMUnsafe dep_mods" (ppr (dep_mods (mg_deps guts))) $
         -- pprTrace "runTcMUnsafe orphans" (ppr orphans) $
         -- pprTrace "runTcMUnsafe dep_orphs" (ppr (dep_orphs (mg_deps guts))) $
         -- pprTrace "runTcMUnsafe dep_finsts" (ppr (dep_finsts (mg_deps guts))) $
         -- pprTrace "runTcMUnsafe mg_insts" (ppr (mg_insts guts)) $
         -- pprTrace "runTcMUnsafe fam_mg_insts" (ppr (mg_fam_insts guts)) $
         -- pprTrace "runTcMUnsafe imports0" (ppr imports0) $
         -- pprTrace "runTcMUnsafe mg_rdr_env guts" (ppr (mg_rdr_env guts)) $
         -- pprTrace "runTcMUnsafe ic_rn_gbl_env" (ppr (ic_rn_gbl_env (hsc_IC env0))) $         
         env0 { hsc_IC = (hsc_IC env0)
                 { ic_imports = map IIModule extraModuleNames ++ imports0
                 , ic_rn_gbl_env = mg_rdr_env guts
                 , ic_instances = (mg_insts guts, mg_fam_insts guts)
                 } }
         -- env0

-- TODO: Try initTcForLookup or initTcInteractive in place of initTcFromModGuts.
-- If successful, drop dflags and guts arguments.

runDsMUnsafe :: HscEnv -> DynFlags -> ModGuts -> DsM a -> a
runDsMUnsafe env dflags guts = runTcMUnsafe env dflags guts . initDsTc

-- | Build a dictionary for the given id
buildDictionary' :: HscEnv -> DynFlags -> ModGuts -> Id -> (Id, [CoreBind])
buildDictionary' env dflags guts evar =
    let (i, bs) =
         runTcMUnsafe env dflags guts $
          do loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
             let predTy = varType evar
                 nonC = mkNonCanonical $
                          CtWanted { ctev_pred = predTy, ctev_dest = EvVarDest evar
                                   , ctev_loc = loc }
                 wCs = mkSimpleWC [cc_ev nonC]
             -- TODO: Make sure solveWanteds is the right function to call.
             (_wCs', bnds0) <- second evBindMapBinds <$> runTcS (solveWanteds wCs)
             -- Use the newly exported zonkEvBinds. <https://phabricator.haskell.org/D2088>
             (_env',bnds) <- zonkEvBinds emptyZonkEnv bnds0
             -- pprTrace "buildDictionary' _wCs'" (ppr _wCs') (return ())
             -- changed next line from reportAllUnsolved, which panics. revisit and fix!
             -- warnAllUnsolved _wCs'
             warnAllUnsolved _wCs'
             return (evar, bnds)
    in
      (i, runDsMUnsafe env dflags guts (dsEvBinds bs))

-- TODO: Richard Eisenberg: "use TcMType.newWanted to make your CtWanted. As it
-- stands, if predTy is an equality constraint, your CtWanted will be
-- ill-formed, as all equality constraints should have HoleDests, not
-- EvVarDests. Using TcMType.newWanted will simplify and improve your code."

-- TODO: Why return the given evar?

-- TODO: Try to combine the two runTcMUnsafe calls.

buildDictionary :: HscEnv -> DynFlags -> ModGuts -> InScopeEnv -> Type -> Either SDoc CoreExpr
buildDictionary env dflags guts inScope ty =
  -- pprTrace "buildDictionary" (ppr ty) $
  -- pprTrace "buildDictionary" (ppr ty $$ text "-->" $$ ppr dict) $
  -- pprTrace "buildDictionary free vars" (ppr (exprFreeVars dict)) $
  -- pprTrace "buildDictionary (bnds,freeIds)" (ppr (bnds,freeIds)) $
  -- pprTrace "buildDictionary (collectArgs dict)" (ppr (collectArgs dict)) $
  -- either (\ e -> pprTrace "buildDictionary fail" (ppr ty $$ text "-->" $$ e) res) (const res) $
  res
 where
   res | null bnds          = Left (text "no bindings")
       | notNull holeyBinds = Left (text "coercion holes: " <+> ppr holeyBinds)
       | notNull freeIdTys  = Left (text "free id types:" <+> ppr freeIdTys)
       | otherwise          = return dict
   name     = "$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags ty))
   binder   = localId inScope name ty
   (i,bnds) = buildDictionary' env dflags guts binder
   dict =
     case bnds of
       -- The common case that we would have gotten a single non-recursive let
       [NonRec v e] | i == v -> e
       _                     -> mkCoreLets bnds (varToCoreExpr i)
   -- Sometimes buildDictionary' constructs bogus dictionaries with free
   -- identifiers. Hence check that freeIds is empty. Allow for free *type*
   -- variables, however, since there may be some in the given type as
   -- parameters. Alternatively, check that there are no free variables (val or
   -- type) in the resulting dictionary that were not in the original type.
   freeIds = filter isId (uniqSetToList (exprFreeVars dict))
   freeIdTys = varType <$> freeIds
   holeyBinds = filter hasCoercionHole bnds
   -- err doc = Left (doc $$ ppr ty $$ text "-->" $$ ppr dict)

hasCoercionHole :: Data t => t -> Bool
hasCoercionHole = getAny . everything mappend (mkQ mempty (Any . isHole))
 where
   isHole :: CoercionHole -> Bool
   isHole = const True

-- | Make a unique identifier for a specified type, using a provided name.
localId :: InScopeEnv -> String -> Type -> Id
localId (inScopeSet,_) str ty =
  uniqAway inScopeSet (mkLocalId (stringToName str) ty)

stringToName :: String -> Name
stringToName str =
  mkSystemVarName (mkUniqueGrimily (abs (fromIntegral (hashString str))))
                  (mkFastString str)

-- When mkUniqueGrimily's argument is negative, we see something like
-- "Exception: Prelude.chr: bad argument: (-52)". Hence the abs.
