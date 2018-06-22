{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_GHC -Wall #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
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

module ConCat.BuildDictionary
  (buildDictionary
  ,WithType(..)
  , withType
  ,varWithType
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
  ,uniqSetToList
#endif
  ) where

import Data.Monoid (Any(..))
import Data.Char (isSpace)
import Data.Data (Data)
import Data.Generics (mkQ,everything)
import Control.Monad (filterM,when)

import GhcPlugins

import Control.Arrow (second)

import TyCoRep (CoercionHole(..))
import TcHsSyn (emptyZonkEnv,zonkEvBinds)
import           TcRnMonad (getCtLocM,traceTc)
import           TcRnTypes (cc_ev)
import TcInteract (solveSimpleGivens)
import TcSMonad -- (TcS,runTcS)
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
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
import qualified UniqSet as NonDetSet
#endif
-- Temp
-- import HERMIT.GHC.Typechecker (initTcFromModGuts)
-- import ConCat.GHC

import ConCat.Simplify

isFound :: FindResult -> Bool
isFound (Found _ _) = True
isFound _           = False

moduleIsOkay :: HscEnv -> ModuleName -> IO Bool
moduleIsOkay env mname = isFound <$> findExposedPackageModule env mname Nothing

#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
uniqSetToList ::  UniqSet a -> [a]
uniqSetToList = NonDetSet.nonDetEltsUniqSet
#endif
-- #define TRACING

pprTrace' :: String -> SDoc -> a -> a
#ifdef TRACING
pprTrace' = pprTrace
#else
pprTrace' _ _ = id
#endif

traceTcS' :: String -> SDoc -> TcS ()
traceTcS' str doc = pprTrace' str doc (return ())

traceTc' :: String -> SDoc -> TcRn ()
traceTc' str doc = pprTrace' str doc (return ())

runTcM :: HscEnv -> DynFlags -> ModGuts -> TcM a -> IO a
runTcM env0 dflags guts m = do
    -- Remove hidden modules from dep_orphans
    orphans <- filterM (moduleIsOkay env0) (moduleName <$> dep_orphs (mg_deps guts))
    -- pprTrace' "runTcM orphans" (ppr orphans) (return ())
    (msgs, mr) <- runTcInteractive (env orphans) m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat $
              text "Errors:"   : pprErrMsgBagWithLoc errs
           ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (fail $ showMsgs msgs) return mr
 where
   imports0 = ic_imports (hsc_IC env0)
   env :: [ModuleName] -> HscEnv
   env extraModuleNames =
     -- pprTrace' "runTcM extraModuleNames" (ppr extraModuleNames) $
     -- pprTrace' "runTcM dep_mods" (ppr (dep_mods (mg_deps guts))) $
     -- pprTrace' "runTcM dep_orphs" (ppr (dep_orphs (mg_deps guts))) $
     -- pprTrace' "runTcM dep_finsts" (ppr (dep_finsts (mg_deps guts))) $
     -- pprTrace' "runTcM mg_insts" (ppr (mg_insts guts)) $
     -- pprTrace' "runTcM fam_mg_insts" (ppr (mg_fam_insts guts)) $
     -- pprTrace' "runTcM imports0" (ppr imports0) $
     -- pprTrace' "runTcM mg_rdr_env guts" (ppr (mg_rdr_env guts)) $
     -- pprTrace' "runTcM ic_rn_gbl_env" (ppr (ic_rn_gbl_env (hsc_IC env0))) $
     env0 { hsc_IC = (hsc_IC env0)
             { ic_imports = map IIModule extraModuleNames ++ imports0
             , ic_rn_gbl_env = mg_rdr_env guts
             , ic_instances = (mg_insts guts, mg_fam_insts guts)
             } }
     -- env0

-- TODO: Try initTcForLookup or initTcInteractive in place of initTcFromModGuts.
-- If successful, drop dflags and guts arguments.

runDsM :: HscEnv -> DynFlags -> ModGuts -> DsM a -> IO a
runDsM env dflags guts = runTcM env dflags guts . initDsTc

-- | Build a dictionary for the given id
buildDictionary' :: HscEnv -> DynFlags -> ModGuts -> VarSet -> Id
                 -> IO (Id, [CoreBind])
buildDictionary' env dflags guts evIds evar =
  do (i, bs) <-
       runTcM env dflags guts $
       do loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
          let givens = mkGivens loc (uniqSetToList evIds)
              predTy = varType evar
              nonC = mkNonCanonical $
                       CtWanted { ctev_pred = predTy
                                , ctev_dest = EvVarDest evar
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
                                , ctev_nosh = WOnly
#endif
                                , ctev_loc = loc }
              wCs = mkSimpleWC [cc_ev nonC]
          -- TODO: Make sure solveWanteds is the right function to call.
          traceTc' "buildDictionary': givens" (ppr givens)
          (_wCs', bnds0) <-
            second evBindMapBinds <$>
            runTcS (do _ <- solveSimpleGivens givens
                       traceTcS' "buildDictionary' back from solveSimpleGivens" empty
                       z <- solveWanteds wCs
                       traceTcS' "buildDictionary' back from solveWanteds" (ppr z)
                       return z
                   )
          traceTc' "buildDictionary' back from runTcS" (ppr bnds0)
          -- Use the newly exported zonkEvBinds. <https://phabricator.haskell.org/D2088>
          (_env',bnds) <- zonkEvBinds emptyZonkEnv bnds0
          -- traceTc "buildDictionary' _wCs'" (ppr _wCs')
          -- changed next line from reportAllUnsolved, which panics. revisit and fix!
          -- warnAllUnsolved _wCs'
          traceTc' "buildDictionary' zonked" (ppr bnds)
          warnAllUnsolved _wCs'
          return (evar, bnds)
     bs' <- runDsM env dflags guts (dsEvBinds bs)
     return (i, bs')

-- TODO: Richard Eisenberg: "use TcMType.newWanted to make your CtWanted. As it
-- stands, if predTy is an equality constraint, your CtWanted will be
-- ill-formed, as all equality constraints should have HoleDests, not
-- EvVarDests. Using TcMType.newWanted will simplify and improve your code."

-- TODO: Why return the given evar?

-- TODO: Try to combine the two runTcM calls.

buildDictionary :: HscEnv -> DynFlags -> ModGuts -> InScopeEnv -> Type -> IO (Either SDoc CoreExpr)
buildDictionary env dflags guts inScope goalTy =
  pprTrace' "\nbuildDictionary" (ppr goalTy) $
  pprTrace' "buildDictionary in-scope evidence" (ppr (WithType . Var <$> uniqSetToList scopedDicts)) $
  reassemble <$> buildDictionary' env dflags guts scopedDicts binder
 where
   binder = localId inScope name goalTy
   name = "$d" ++ zEncodeString (filter (not . isSpace) (showPpr dflags goalTy))
   scopedDicts = filterVarSet keepVar (getInScopeVars (fst inScope))
   keepVar v =
     -- Occasionally I get "StgCmmEnv: variable not found", so don't keep any.
     -- See 2018-01-23 journal notes. For now, False
     -- TODO: Investigate!
     False &&
     isEvVar v -- && not (isDeadBinder v)
     -- Keep evidence that relates to free type variables in the goal.
     -- && not (isEmptyVarSet (goalTyVars `intersectVarSet` tyCoVarsOfType (varType v))) -- see issue #20
   -- freeIds = filter isId (uniqSetToList (exprFreeVars dict))
   -- freeIdTys = varType <$> freeIds
   -- goalTyVars = tyCoVarsOfType goalTy
   reassemble (i,bnds) =
     -- pprTrace' "buildDictionary" (ppr goalTy $$ text "-->" $$ ppr dict) $
     -- pprTrace' "buildDictionary inScope" (ppr (fst inScope)) $
     -- pprTrace' "buildDictionary freeIds" (ppr freeIds) $
     -- pprTrace' "buildDictionary (bnds,freeIds)" (ppr (bnds,freeIds)) $
     -- pprTrace' "buildDictionary dict" (ppr dict) $
     -- either (\ e -> pprTrace' "buildDictionary fail" (ppr goalTy $$ text "-->" $$ e) res) (const res) $
     res
    where
      res | null bnds          = Left (text "no bindings")
          | notNull holeyBinds = Left (text "coercion holes: " <+> ppr holeyBinds)
          | notNull freeIdTys  = Left (text "free id types:" <+> ppr freeIdTys)
          | otherwise          = return $ simplifyE dflags False
                                          dict
      dict =
        case bnds of
          -- Common case with single non-recursive let
          [NonRec v e] | i == v -> e
          _                     -> mkCoreLets bnds (varToCoreExpr i)
      -- Sometimes buildDictionary' constructs bogus dictionaries with free
      -- identifiers. Hence check that freeIds is empty. Allow for free *type*
      -- variables, however, since there may be some in the given type as
      -- parameters. Alternatively, check that there are no free variables (val or
      -- type) in the resulting dictionary that were not in the original type.
      freeIds = filterVarSet isId (exprFreeVars dict) `minusVarSet` scopedDicts
      freeIdTys = varType <$> uniqSetToList freeIds
      holeyBinds = filter hasCoercionHole bnds
      -- err doc = Left (doc $$ ppr goalTy $$ text "-->" $$ ppr dict)

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


-- Maybe place in a GHC utils module.

withType :: CoreExpr -> WithType
withType = WithType

varWithType :: Var -> WithType
varWithType = withType . Var

newtype WithType = WithType CoreExpr

instance Outputable WithType where
  ppr (WithType e) = ppr e <+> dcolon <+> ppr (exprType e)

newtype WithIdInfo = WithIdInfo Id

instance Outputable WithIdInfo where
  -- I wanted the full IdInfo, but it's not Outputtable
  -- ppr (WithIdInfo v) = ppr v <+> colon <+> ppr (occInfo (idInfo v))
  ppr (WithIdInfo v) = ppr v <+> colon <+> ppr (splitTyConApp_maybe (varType v))
