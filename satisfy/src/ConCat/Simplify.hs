{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}

-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds   #-} -- TEMP

----------------------------------------------------------------------
-- |
-- Module      :  ConCat.Simplify
-- Copyright   :  (c) 2016 Conal Elliott
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- 
----------------------------------------------------------------------

module ConCat.Simplify (simplifyE) where

-- TODO: explicit exports

import System.IO.Unsafe (unsafePerformIO)

#if MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
#if !MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
import GHC.Core (emptyRuleEnv)
#endif
import GHC.Core.FamInstEnv (emptyFamInstEnvs)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.Opt.Simplify (simplExpr)
import GHC.Core.Opt.Simplify.Env
import GHC.Core.Opt.Simplify.Monad (SimplM,initSmpl)
import GHC.Core.Stats (exprSize)
import GHC.Plugins
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
import GHC.Core.Unfold (defaultUnfoldingOpts)
import qualified GHC.Utils.Logger as Err
#else
import qualified GHC.Utils.Error as Err
#endif
#else
import GhcPlugins
import Simplify (simplExpr)
import SimplMonad (SimplM,initSmpl)
import CoreSyn (emptyRuleEnv)
import qualified ErrUtils as Err
import SimplEnv
import CoreStats (exprSize)
import OccurAnal (occurAnalyseExpr)
import FamInstEnv (emptyFamInstEnvs)
#endif

#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
dumpIfSet_dyn' :: Err.Logger -> DynFlags -> DumpFlag -> String -> SDoc -> IO ()
dumpIfSet_dyn' logger dflags dumpFlag str =
  Err.dumpIfSet_dyn logger dflags dumpFlag str Err.FormatCore
#elif MIN_VERSION_GLASGOW_HASKELL(9,0,0,0)
dumpIfSet_dyn' :: DynFlags -> DumpFlag -> String -> SDoc -> IO ()
dumpIfSet_dyn' dflags dumpFlag str = Err.dumpIfSet_dyn dflags dumpFlag str Err.FormatCore
#else
dumpIfSet_dyn' :: DynFlags -> DumpFlag -> String -> SDoc -> IO ()
dumpIfSet_dyn' = Err.dumpIfSet_dyn
#endif

{--------------------------------------------------------------------
    Simplification
--------------------------------------------------------------------}

-- We can't use simplifyExpr from SimplCore, because it doesn't inline.

-- TODO: I don't think I'm using inline with simplifyE, so switch to simplifyExpr.

simplifyE :: DynFlags -> Bool -> CoreExpr -> CoreExpr
simplifyE dflags inline = unsafePerformIO . simplifyExpr dflags inline

simplifyExpr :: DynFlags -- includes spec of what core-to-core passes to do
             -> Bool
             -> CoreExpr
             -> IO CoreExpr
-- simplifyExpr is called by the driver to simplify an
-- expression typed in at the interactive prompt
--
-- Also used by Template Haskell
simplifyExpr dflags inline expr
  = do let sz = exprSize expr
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
       logger <- Err.initLogger
       (expr', counts) <- initSmpl logger dflags emptyRuleEnv
                            emptyFamInstEnvs sz
                            (simplExprGently (simplEnvForCcc dflags inline logger) expr)
       Err.dumpIfSet logger dflags (dopt Opt_D_dump_simpl_stats dflags)
               "Simplifier statistics" (pprSimplCount counts)
       dumpIfSet_dyn' logger dflags Opt_D_dump_simpl "Simplified expression"
                      (ppr expr')
#else
       us <- mkSplitUniqSupply 'r'
       (expr', counts) <- initSmpl dflags emptyRuleEnv
                            emptyFamInstEnvs us sz
                            (simplExprGently (simplEnvForCcc dflags inline) expr)
       Err.dumpIfSet dflags (dopt Opt_D_dump_simpl_stats dflags)
               "Simplifier statistics" (pprSimplCount counts)
       dumpIfSet_dyn' dflags Opt_D_dump_simpl "Simplified expression"
                      (ppr expr')
#endif
       return expr'

-- Copied from SimplCore (not exported)
simplExprGently :: SimplEnv -> CoreExpr -> SimplM CoreExpr
simplExprGently env expr = do
    expr1 <- simplExpr env (occurAnalyseExpr expr)
    simplExpr env (occurAnalyseExpr expr1)

-- Like simplEnvForGHCi but with inlining.
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
simplEnvForCcc :: DynFlags -> Bool -> Err.Logger -> SimplEnv
simplEnvForCcc dflags inline logger
  = mkSimplEnv $ SimplMode { sm_names = ["Simplify for ccc"]
                           , sm_phase = Phase 0 -- Was InitialPhase
                           , sm_rules = rules_on
                           , sm_inline = inline -- was False
                           , sm_eta_expand = eta_expand_on
                           , sm_case_case = True
                           , sm_uf_opts = defaultUnfoldingOpts
                           , sm_pre_inline = inline
                           , sm_logger = logger
                           , sm_dflags = dflags
#if MIN_VERSION_GLASGOW_HASKELL(9,2,2,0)
                           , sm_cast_swizzle = True
#endif
                           }
  where
    rules_on      = gopt Opt_EnableRewriteRules   dflags
    eta_expand_on = gopt Opt_DoLambdaEtaExpansion dflags
#else
simplEnvForCcc :: DynFlags -> Bool -> SimplEnv
simplEnvForCcc dflags inline
  = mkSimplEnv $ SimplMode { sm_names = ["Simplify for ccc"]
                           , sm_phase = Phase 0 -- Was InitialPhase
                           , sm_rules = rules_on
                           , sm_inline = inline -- was False
                           , sm_eta_expand = eta_expand_on
                           , sm_case_case = True
                           , sm_dflags = dflags
                           }
  where
    rules_on      = gopt Opt_EnableRewriteRules   dflags
    eta_expand_on = gopt Opt_DoLambdaEtaExpansion dflags
#endif
