{-# LANGUAGE ViewPatterns, CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Plugin to install a GHC 'BuiltinRule' for 'CO.satisfyClassOp'.

module ConCat.Satisfy.Plugin where

import System.IO.Unsafe (unsafePerformIO)

-- GHC API
#if MIN_VERSION_GLASGOW_HASKELL(9,4,0,0)
import GHC.Utils.Trace
#endif
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
import GHC.Core.Unfold (defaultUnfoldingOpts)
import qualified GHC.Driver.Backend as Backend
import GHC.Utils.Logger (getLogger)
#endif
#if MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
import GHC.Core.Class (classAllSelIds)
import GHC.Core.Make (mkCoreTup)
import GHC.Plugins as GHC
import GHC.Runtime.Loader
import GHC.Types.Id.Make (mkDictSelRhs)
#else
import GhcPlugins as GHC
import Class (classAllSelIds)
import MkId (mkDictSelRhs)
import MkCore (mkCoreTup)
import DynamicLoading
#endif

import ConCat.BuildDictionary (buildDictionary, annotateEvidence)
import ConCat.Inline.Plugin (findId)

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install
                       , pluginRecompile = purePlugin
                       }

on_mg_rules :: ([CoreRule] -> [CoreRule]) -> (ModGuts -> ModGuts)
on_mg_rules f mg = mg { mg_rules = f (mg_rules mg) }


install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _opts todos =
  do dflags <- getDynFlags
     -- Unfortunately, the plugin doesn't work in GHCi. Until fixed,
     -- disable under GHCi, so we can at least type-check conveniently.
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
     logger <- getLogger
     if backend dflags == Backend.Interpreter then
        return todos
#else
     if hscTarget dflags == HscInterpreted then
        return todos
#endif
      else do
          hscEnv <- getHscEnv
          pprTrace "Install satisfyRule" empty (return ())
          uniqSupply <- getUniqueSupplyM
          let addRule, delRule :: ModGuts -> CoreM ModGuts
              addRule guts =
                do satisfyPV <- findId "ConCat.Satisfy" "satisfy'"
                   pprTrace "adding satisfyRule" empty (return ())
                   return (on_mg_rules (++ [satisfyRule hscEnv guts uniqSupply satisfyPV dflags]) guts)
              isOurRule r = (isBuiltinRule r) && (ru_name r == satisfyRuleName)
              delRule guts =
                do pprTrace "removing satisfyRule" empty (return ())
                   return (on_mg_rules (filter (not . isOurRule)) guts)

              mode dflags
                = SimplMode { sm_names      = ["Satisfy simplifier pass"]
                            , sm_phase      = Phase 3 -- ??
                            , sm_rules      = True  -- important
                            , sm_inline     = False -- important
                            , sm_eta_expand = False -- ??
                            , sm_case_case  = True
#if MIN_VERSION_GLASGOW_HASKELL(9,2,2,0)
                            , sm_cast_swizzle  = True
                            , sm_uf_opts = defaultUnfoldingOpts
                            , sm_pre_inline = False
                            , sm_logger = logger
#endif
                            , sm_dflags     = dflags
                    }
          -- It really needs to be this early, otherwise ghc will
          -- break up the calls and the rule will not fire.
          return $
             [CoreDoPluginPass "annotate satisfy instantiations" (annotateEvidencePass "ConCat.Satisfy" "satisfy" "satisfy'" 2),
               CoreDoPluginPass "Insert satisfy rule" addRule,
               CoreDoSimplify 7 (mode dflags),
               CoreDoPluginPass "Satisfy remove rule" delRule]
              ++ todos

annotateEvidencePass :: String -> String -> String -> Int -> ModGuts -> CoreM ModGuts
annotateEvidencePass modName name name' typeArgsCount guts =
  do fnId <- findId modName name
     fnId' <- findId modName name'
     bindsOnlyPass (mapM (annotateEvidence fnId fnId' typeArgsCount)) guts

satisfyRuleName :: FastString
satisfyRuleName = fsLit "satisfy'Rule"
-- satisfy :: forall c z. (c => z) -> z

satisfyRule :: HscEnv -> ModGuts -> UniqSupply -> Id -> DynFlags -> CoreRule
satisfyRule env guts uniqSupply satisfyPV dflags = BuiltinRule
  { ru_name  = satisfyRuleName
  , ru_fn    = varName satisfyPV
  , ru_nargs = 5  -- including type args
  , ru_try   = const $ satisfy env guts uniqSupply dflags
  }

satisfy :: HscEnv -> ModGuts -> UniqSupply -> DynFlags -> InScopeEnv -> Id -> [CoreExpr] -> Maybe CoreExpr
satisfy _ _ _ _ _ _ args | pprTrace "satisfyRule" (ppr args) False = undefined
satisfy hscEnv guts uniqSupply dflags inScope _sat [Type evT, Type c, Type _z, ev, f] =
  case unsafePerformIO $ buildDictionary hscEnv dflags guts uniqSupply inScope evT ev c of
    Left  msg  -> pprPanic "satisfy: couldn't build dictionary for"
                    (ppr (exprType f) GHC.<> colon $$ msg)
    Right dict -> Just (f `App` dict)
satisfy _ _ _ _ _ _ args = pprPanic "satisfy mismatch" (ppr args)
