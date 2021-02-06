{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}
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
  ,annotateEvidence
  ) where

import Data.Monoid (Any(..))
import Data.Char (isSpace)
import Data.Data (Data)
import Data.Generics (mkQ,everything)
import Control.Monad (filterM,when)

import GhcPlugins

import Control.Arrow (second)

import TyCoRep (CoercionHole(..), Type(..))
import TyCon (isTupleTyCon)
import TcHsSyn (emptyZonkEnv,zonkEvBinds)
import           TcRnMonad (getCtLocM,traceTc)
import           TcRnTypes (cc_ev)
import TcInteract (solveSimpleGivens)
import TcSMonad -- (TcS,runTcS)
import TcEvidence (evBindMapBinds)
import TcErrors(warnAllUnsolved)
import qualified TcMType as TcMType

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
buildDictionary' :: HscEnv -> DynFlags -> ModGuts -> VarSet -> Type
                 -> IO (Maybe (Id, [CoreBind]))
buildDictionary' env dflags guts evIds predTy =
  do res <-
       runTcM env dflags guts $
       do loc <- getCtLocM (GivenOrigin UnkSkol) Nothing
          evidence <- TcMType.newWanted (GivenOrigin UnkSkol) Nothing predTy
          let EvVarDest evarDest = ctev_dest evidence
              givens = mkGivens loc (uniqSetToList evIds)
              wCs = mkSimpleWC [evidence]
          -- TODO: Make sure solveWanteds is the right function to call.
          traceTc' "buildDictionary': givens" (ppr givens)
          (wantedConstraints, bnds0) <-
            second evBindMapBinds <$>
            runTcS (do _ <- solveSimpleGivens givens
                       traceTcS' "buildDictionary' back from solveSimpleGivens" empty
                       z <- solveWanteds wCs
                       traceTcS' "buildDictionary' back from solveWanteds" (ppr z)
                       return z
                   )
          traceTc' "buildDictionary' back from runTcS" (ppr bnds0)
#if MIN_VERSION_GLASGOW_HASKELL(8,8,0,0)
          ez <- emptyZonkEnv
#else
          let ez = emptyZonkEnv
#endif
          -- Use the newly exported zonkEvBinds. <https://phabricator.haskell.org/D2088>
          (_env',bnds) <- zonkEvBinds ez bnds0
          -- traceTc "buildDictionary' _wCs'" (ppr _wCs')
          -- changed next line from reportAllUnsolved, which panics. revisit and fix!
          -- warnAllUnsolved _wCs'
          traceTc' "buildDictionary' zonked" (ppr bnds)
          if isEmptyWC wantedConstraints
          then return (Just (evarDest, bnds))
          else return Nothing
     case res of
       Just (i, bs) ->
         do bs' <- runDsM env dflags guts (dsEvBinds bs)
            return (Just (i, bs'))
       Nothing -> return Nothing

-- TODO: Try to combine the two runTcM calls.

buildDictionary :: HscEnv -> DynFlags -> ModGuts -> InScopeEnv -> Type -> CoreExpr -> Type -> IO (Either SDoc CoreExpr)
buildDictionary env dflags guts inScope evType@(TyConApp tyCon evTypes) ev goalTy | isTupleTyCon tyCon =
  reallyBuildDictionary env dflags guts inScope evType evTypes ev goalTy
-- only 1-tuples in Haskell  
buildDictionary env dflags guts inScope evType ev goalTy | isEvVarType evType =
  reallyBuildDictionary env dflags guts inScope evType [evType] ev goalTy
buildDictionary _env _dflags _guts _inScope evT _ev _goalTy = pprPanic "evidence type mismatch" (ppr evT)
                                                         
reallyBuildDictionary :: HscEnv -> DynFlags -> ModGuts -> InScopeEnv -> Type -> [Type] -> CoreExpr -> Type -> IO (Either SDoc CoreExpr)
reallyBuildDictionary env dflags guts inScope evType evTypes ev goalTy =
  pprTrace' "\nbuildDictionary" (ppr goalTy) $
  pprTrace' "buildDictionary in-scope evidence" (ppr ev) $
  reassemble <$> buildDictionary' env dflags guts evIdSet goalTy
 where
   evIds = [ local
           | (evTy, index) <- evTypes `zip` [(0 :: Int) ..]
           , let local = localId inScope ("evidence" ++ show index) evTy ]
   evIdSet = mkVarSet evIds
   reassemble Nothing =
     Left (text "unsolved constraints")
   reassemble (Just (i,bnds)) =
     pprTrace' "buildDictionary" (ppr goalTy $$ text "-->" $$ ppr expr) $
     pprTrace' "buildDictionary evIds" (ppr evIds) $
     pprTrace' "buildDictionary expr" (ppr expr) $
     either (\ e -> pprTrace' "buildDictionary fail" (ppr goalTy $$ text "-->" $$ e) res) (const res) $
     res
    where
      res | null bnds          = Left (text "no bindings")
          | notNull holeyBinds = Left (text "coercion holes: " <+> ppr holeyBinds)
          | otherwise          = return $ simplifyE dflags False
                                          expr
      dict =
        case bnds of
          -- Common case with single non-recursive let
          [NonRec v e] | i == v -> e
          _                     -> mkCoreLets bnds (varToCoreExpr i)
      -- could optimize if these things are already variables
      expr = if null evTypes
             then dict
             else mkWildCase ev evType goalTy [(DataAlt (tupleDataCon Boxed (length evIds)), evIds, dict)]
      holeyBinds = filter hasCoercionHole bnds

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

-- Transform calls to a function that requires a dictionary into one
-- another one that also takes a tuple of available locally-bound
-- dictionaries.  (Note that inScope contains a superset of these
-- variables, including some that will be unbound in the final output
-- code.)

extendEvVars :: DVarSet -> Var -> DVarSet
extendEvVars evVars var =
  if isEvVar var
  then extendDVarSet evVars var
  else evVars

extendEvVarsList :: DVarSet -> [Var] -> DVarSet
extendEvVarsList evVars vars =
  extendDVarSetList evVars (filter isEvVar vars)

annotateEvidence :: Id -> Id -> Int -> CoreBind -> CoreM CoreBind
annotateEvidence fnId fnId' typeArgsCount (NonRec var expr) =
  do let expr' = annotateExpr fnId fnId' typeArgsCount expr
     return (NonRec var expr')
annotateEvidence fnId fnId' typeArgsCount (Rec bindings) =
  do bindings' <- mapM (\ (var, expr) ->
                          do let expr' = annotateExpr fnId fnId' typeArgsCount expr
                             return (var, expr'))
                       bindings
     return (Rec bindings')

annotateExpr :: Id -> Id -> Int -> CoreExpr -> CoreExpr
-- annotateExpr _fnId _fnId' _typeArgsCount expr | pprTrace "annotateExpr" (ppr expr) False = undefined
annotateExpr fnId fnId' typeArgsCount expr0 =
  go emptyDVarSet expr0
  where
    go _evVars expr@(Var _) = expr
    go _evVars expr@(Lit _) = expr
    go evVars expr@(collectArgs -> (Var ((== fnId) -> True), args)) =
       let (tyArgs, valArgs) = splitAt typeArgsCount args
       in if length tyArgs < typeArgsCount
          then pprPanic "unsaturated call to target function" (ppr expr)
          else
            let evVarExp = mkCoreTup (map Var (dVarSetElems evVars))
                valArgs' = map (go evVars) valArgs
            in mkCoreApps (Var fnId') (tyArgs ++ [Type (exprType evVarExp), evVarExp] ++ valArgs')
    go evVars (App fn arg) =
      let fn' = go evVars fn
          arg' = go evVars arg
      in App fn' arg'
    go evVars (Lam var body) =
      let evVars' = extendEvVars evVars var
          body' = go evVars' body
      in Lam var body'
    go evVars (Let (NonRec var rhs) body) =
      let rhs' = go evVars rhs
          body' = go (extendEvVars evVars var) body
      in Let (NonRec var rhs') body'
    go evVars (Let (Rec bindings) body) =
      let evVars' = extendEvVarsList evVars (map fst bindings)
          bindings' = map (\ (var, expr) -> (var, go evVars' expr))
                           bindings
          body' = go  evVars' body
      in Let (Rec bindings') body'
    go evVars (Case scrutinee var ty alts) =
      let evVars' = extendEvVars evVars var
          scrutinee' = go evVars scrutinee
          alts' = map (annotateAlt evVars') alts
      in Case scrutinee' var ty alts'
    go evVars (Cast expr coercion) =
      let expr' = go evVars expr
      in Cast expr' coercion
    go evVars (Tick tickish expr) =
      let expr' = go evVars expr
      in Tick tickish expr'
    go _evVars expr@(Type _) = expr
    go _evVars expr@(Coercion _) = expr

    annotateAlt evVars (con, binders, rhs) =
      (con, binders, go (extendEvVarsList evVars binders) rhs)

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
