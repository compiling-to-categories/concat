-- {-# LANGUAGE #-}
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

import GhcPlugins
import Simplify (simplExpr)
import SimplMonad (SimplM,initSmpl)
import CoreSyn (emptyRuleEnv)
import qualified ErrUtils as Err
import SimplEnv
import CoreStats (exprSize)
import OccurAnal (occurAnalyseExpr)
import FamInstEnv (emptyFamInstEnvs)

import ConCat.Misc (Unop)


{--------------------------------------------------------------------
    Simplification
--------------------------------------------------------------------}

-- We can't use simplifyExpr from SimplifyCore, because it doesn't inline.

simplifyE :: DynFlags -> Bool -> Unop CoreExpr
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
  = do us <- mkSplitUniqSupply 'r'
       let sz = exprSize expr
       (expr', counts) <- initSmpl dflags emptyRuleEnv
                            emptyFamInstEnvs us sz
                            (simplExprGently (simplEnvForReify dflags inline) expr)
       Err.dumpIfSet dflags (dopt Opt_D_dump_simpl_stats dflags)
               "Simplifier statistics" (pprSimplCount counts)
       Err.dumpIfSet_dyn dflags Opt_D_dump_simpl "Simplified expression"
                     (ppr expr')
       return expr'

-- Copied from SimplCore (not exported)
simplExprGently :: SimplEnv -> CoreExpr -> SimplM CoreExpr
simplExprGently env expr = do
    expr1 <- simplExpr env (occurAnalyseExpr expr)
    simplExpr env (occurAnalyseExpr expr1)

-- Like simplEnvForGHCi but with inlining.
simplEnvForReify :: DynFlags -> Bool -> SimplEnv
simplEnvForReify dflags inline
  = mkSimplEnv $ SimplMode { sm_names = ["Simplify for reify"]
                           , sm_phase = Phase 0 -- Was InitialPhase
                           , sm_rules = rules_on
                           , sm_inline = inline -- was False
                           , sm_eta_expand = eta_expand_on
                           , sm_case_case = True }
  where
    rules_on      = gopt Opt_EnableRewriteRules   dflags
    eta_expand_on = gopt Opt_DoLambdaEtaExpansion dflags
