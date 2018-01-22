{-# LANGUAGE ViewPatterns #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Plugin to install a GHC 'BuiltinRule' for 'CO.satisfyClassOp'.

module ConCat.Satisfy.Plugin where

import System.IO.Unsafe (unsafePerformIO)

-- GHC API
import GhcPlugins
import Class (classAllSelIds)
import MkId (mkDictSelRhs)
import DynamicLoading

import ConCat.BuildDictionary (buildDictionary)
import ConCat.Inline.Plugin (findId)

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _opts todos =
  do dflags <- getDynFlags
     -- Unfortunately, the plugin doesn't work in GHCi. Until fixed,
     -- disable under GHCi, so we can at least type-check conveniently.
     if hscTarget dflags == HscInterpreted then
        return todos
      else
       do reinitializeGlobals
          hscEnv <- getHscEnv
          -- pprTrace "Install satisfyRule" empty (return ())
          let addRule :: ModGuts -> CoreM ModGuts
              addRule guts =
                do satisfyV <- findId "ConCat.Satisfy" "satisfy"
                   return (guts { mg_rules = satisfyRule hscEnv guts satisfyV : mg_rules guts })
          return $
             CoreDoPluginPass "Insert satisfy rule" addRule : todos

-- satisfy :: forall c z. (c => z) -> z

satisfyRule :: HscEnv -> ModGuts -> Id -> CoreRule
satisfyRule env guts satisfyV = BuiltinRule
  { ru_name  = fsLit "satisfy"
  , ru_fn    = varName satisfyV
  , ru_nargs = 3  -- including type args
  , ru_try   = satisfy env guts
  }

satisfy :: HscEnv -> ModGuts -> DynFlags -> InScopeEnv -> Id -> [CoreExpr] -> Maybe CoreExpr
satisfy _ _ _ _ _ args | pprTrace "satisfyRule" (ppr args) False = undefined
satisfy hscEnv guts dflags inScope _sat (Type _c : Type _z : f : _) =
  case unsafePerformIO $ buildDictionary hscEnv dflags guts inScope (exprType f) of
    Left  msg  -> pprPanic "satisfy: couldn't build dictionary for" 
                    (ppr (exprType f) <> colon $$ msg)
    Right dict -> Just (f `App` dict)
satisfy _ _ _ _ _ args = pprPanic "satisfy mismatch" (ppr args)
