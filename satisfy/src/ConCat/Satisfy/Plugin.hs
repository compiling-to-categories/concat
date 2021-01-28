{-# LANGUAGE ViewPatterns, CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Plugin to install a GHC 'BuiltinRule' for 'CO.satisfyClassOp'.

module ConCat.Satisfy.Plugin where

import System.IO.Unsafe (unsafePerformIO)

-- GHC API
import GhcPlugins as GHC
import Class (classAllSelIds)
import MkId (mkDictSelRhs)
import MkCore (mkCoreTup)
import DynamicLoading

import ConCat.BuildDictionary (buildDictionary, annotateEvidence)
import ConCat.Inline.Plugin (findId)

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install
#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
                       , pluginRecompile = purePlugin
#endif
                       }

on_mg_rules :: ([CoreRule] -> [CoreRule]) -> (ModGuts -> ModGuts)
on_mg_rules f mg = mg { mg_rules = f (mg_rules mg) }


install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _opts todos =
  do dflags <- getDynFlags
     -- Unfortunately, the plugin doesn't work in GHCi. Until fixed,
     -- disable under GHCi, so we can at least type-check conveniently.
     if hscTarget dflags == HscInterpreted then
        return todos
      else do
#if !MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
          reinitializeGlobals
#endif
          hscEnv <- getHscEnv
          pprTrace "Install satisfyRule" empty (return ())
          let addRule, delRule :: ModGuts -> CoreM ModGuts
              addRule guts =
                do satisfyPV <- findId "ConCat.Satisfy" "satisfy'"
                   pprTrace "adding satisfyRule" empty (return ())
                   return (on_mg_rules (++ [satisfyRule hscEnv guts satisfyPV]) guts)
              isOurRule r = (isBuiltinRule r) && (ru_name r == satisfyRuleName)
              delRule guts =
                do pprTrace "removing satisfyRule" empty (return ())
                   return (on_mg_rules (filter (not . isOurRule)) guts)

              mode
#if MIN_VERSION_GLASGOW_HASKELL(8,4,0,0)
               dflags
#else
               _dflags
#endif
                = SimplMode { sm_names      = ["Satisfy simplifier pass"]
                            , sm_phase      = Phase 3 -- ??
                            , sm_rules      = True  -- important
                            , sm_inline     = False -- important
                            , sm_eta_expand = False -- ??
                            , sm_case_case  = True
#if MIN_VERSION_GLASGOW_HASKELL(8,4,0,0)
                            , sm_dflags     = dflags
#endif
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

satisfyRule :: HscEnv -> ModGuts -> Id -> CoreRule
satisfyRule env guts satisfyPV = BuiltinRule
  { ru_name  = satisfyRuleName
  , ru_fn    = varName satisfyPV
  , ru_nargs = 5  -- including type args
  , ru_try   = satisfy env guts
  }

satisfy :: HscEnv -> ModGuts -> DynFlags -> InScopeEnv -> Id -> [CoreExpr] -> Maybe CoreExpr
satisfy _ _ _ _ _ args | pprTrace "satisfyRule" (ppr args) False = undefined
satisfy hscEnv guts dflags inScope _sat [Type evT, Type c, Type _z, ev, f] =
  case unsafePerformIO $ buildDictionary hscEnv dflags guts inScope evT ev c of
    Left  msg  -> pprPanic "satisfy: couldn't build dictionary for"
                    (ppr (exprType f) GHC.<> colon $$ msg)
    Right dict -> Just (f `App` dict)
satisfy _ _ _ _ _ args = pprPanic "satisfy mismatch" (ppr args)
