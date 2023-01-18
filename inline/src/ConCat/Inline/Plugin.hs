{-# LANGUAGE ViewPatterns, CPP  #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-unused-imports #-} -- TEMP

-- | Plugin to install a GHC 'BuiltinRule' for 'CO.inlineClassOp'.

module ConCat.Inline.Plugin where

import qualified ConCat.Inline.ClassOp as CO

import Data.List (elemIndex)

-- GHC API
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
import qualified GHC.Driver.Backend as Backend
import GHC.Types.TyThing (lookupId, lookupTyCon)
#endif
#if MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
import GHC.Core.Class (classAllSelIds)
import GHC.Plugins
import GHC.Types.Id.Make (mkDictSelRhs)
import GHC.Runtime.Loader
#else
import GhcPlugins
import Class (classAllSelIds)
import MkId (mkDictSelRhs)
import DynamicLoading
#endif

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install
#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
                       , pluginRecompile = purePlugin
#endif
                       }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _opts todos =
  do dflags <- getDynFlags
     -- Unfortunately, the plugin doesn't work in GHCi. Until fixed,
     -- disable under GHCi, so we can at least type-check conveniently.
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
     if backend dflags == Backend.Interpreter then
        return todos
#else
     if hscTarget dflags == HscInterpreted then
        return todos
#endif
     else
       do
#if !MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
          reinitializeGlobals
#endif
          -- pprTrace "Install inlineClassOpRule" empty (return ())
          let addRule :: ModGuts -> CoreM ModGuts
              addRule guts =
                do inlineV <- findId "ConCat.Inline.ClassOp" "inline"
                   return (guts { mg_rules = inlineClassOpRule inlineV : mg_rules guts })
          return $
             CoreDoPluginPass "Insert inlineClassOp rule" addRule : todos

inlineClassOpRule :: Id -> CoreRule
inlineClassOpRule inlineV = BuiltinRule
  { ru_name  = fsLit "inlineClassOp"
  , ru_fn    = varName inlineV
  , ru_nargs = 2  -- including type args
  , ru_try   = \ _dflags _inScope _fn -> expand
  }
 where
   -- expand _args | pprTrace "inlineClassOpRule" (ppr _args) False = undefined
   expand _es@(Type _a : arg : _) = inlineClassOp arg
   -- expand _args = -- pprTrace "inlineClassOp mismatch args" (ppr _args) $
   expand _args = -- pprTrace "inlineClassOp mismatch args" (ppr _args) $
                  Nothing

-- | The CoreExpr transformation. Inlines a class op to a field accessor in a
-- dictionary.
inlineClassOp :: CoreExpr -> Maybe CoreExpr
-- inlineClassOp e | pprTrace "inlineClassOp" (ppr (e,collectArgs e)) False = undefined
inlineClassOp (collectArgs -> (Var v,rest))
  | ClassOpId cls <- idDetails v
  = -- pprTrace "inlineClassOp class" (ppr cls) $
    ((`mkCoreApps` rest) . mkDictSelRhs cls) <$> elemIndex v (classAllSelIds cls)
  -- Experiment
  -- | Just e' <- maybeUnfoldingTemplate (realIdUnfolding v)
  -- = pprTrace "inlining non-class-op to" (ppr e') $
  --   Just e'
inlineClassOp e = pprTrace "inlineClassOp failed/unnecessary" (ppr e) $
                  Just e

-- inlineClassOp e = pprPanic "inlineClassOp failed" (ppr e)

-- inlineClassOp _e = pprTrace "inlineClassOp failed" (ppr _e) $
--                    Nothing

{--------------------------------------------------------------------
    Utilities
--------------------------------------------------------------------}

lookupRdr :: ModuleName -> (String -> OccName) -> (Name -> CoreM a) -> String -> CoreM a
lookupRdr modu mkOcc mkThing str =
  maybe (panic err) mkThing' =<<
    do hsc_env <- getHscEnv
       liftIO (lookupRdrNameInModuleForPlugins hsc_env modu (Unqual (mkOcc str)))
 where
   err = "lookupRdr: couldn't find " ++ str ++ " in " ++ moduleNameString modu

#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
   -- In GHC 8.6, lookupRdrNameInModuleForPlugins returns a (Name, Module)
   -- where earlier it was just a Name
   mkThing' = mkThing . fst
#else
   mkThing' = mkThing
#endif

lookupTh :: (String -> OccName) -> (Name -> CoreM a) -> String
         -> String -> CoreM a
lookupTh mkOcc mk modu = lookupRdr (mkModuleName modu) mkOcc mk

-- | Find an identifier from module and id names
findId :: String -> String -> CoreM Id
findId = lookupTh mkVarOcc lookupId

-- | Find a TyCon from module and id names
findTc :: String -> String -> CoreM TyCon
findTc = lookupTh mkTcOcc lookupTyCon
