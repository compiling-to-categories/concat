{-# LANGUAGE CPP #-}

-- | Utility functions for normalising, comparing types modulo type families.
module ConCat.NormaliseType (eqTypeM) where

import GHC.Plugins
#if MIN_VERSION_GLASGOW_HASKELL(9,4,0,0)
import GHC.HsToCore.Monad
import Data.Maybe (maybe)
import GHC.HsToCore.Monad
import GHC.Tc.Module (withTcPlugins, withHoleFitPlugins)
import GHC.Tc.Instance.Family (tcGetFamInstEnvs)
import GHC.Core.FamInstEnv (normaliseType)
import GHC.Core.Reduction (reductionReducedType)
import GHC.Tc.Types (TcM)
#endif

-- | compare two types after first normalising out type families
eqTypeM :: HscEnv -> DynFlags -> ModGuts -> Type -> Type -> IO Bool
#if MIN_VERSION_GLASGOW_HASKELL(9,4,0,0)
eqTypeM env dflags guts ty1 ty2 =
  if ty1 `eqType` ty2
  then return True
  else
  runTcForSolver env dflags guts $ do
    famInstEnvs <- tcGetFamInstEnvs
    let reduction1 = normaliseType famInstEnvs Nominal ty1
    let reduction2 = normaliseType famInstEnvs Nominal ty2
    return (reductionReducedType reduction1 `eqType` reductionReducedType reduction2)

-- | run a DsM program inside IO
runDsM :: HscEnv -> DynFlags -> ModGuts -> DsM a -> IO a
runDsM env dflags guts m = do
  (messages, result) <- initDsWithModGuts env guts m
  maybe (fail (showSDoc dflags (ppr messages)))
        return result

-- | run a TcM program inside IO, with plugins initialised
runTcForSolver :: HscEnv -> DynFlags -> ModGuts -> TcM a -> IO a
runTcForSolver env dflags guts m =
  runDsM env dflags guts $ do
    initTcDsForSolver . withTcPlugins env . withHoleFitPlugins env $ m

-- | normalise a type wrt. type families
normaliseTypeM :: HscEnv -> DynFlags -> ModGuts -> Type -> IO Type
normaliseTypeM env dflags guts ty =
  runTcForSolver env dflags guts $ do
    famInstEnvs <- tcGetFamInstEnvs
    let reduction = normaliseType famInstEnvs Nominal ty
    return (reductionReducedType reduction)
#else
eqTypeM _ _ _ ty1 ty2 = pure $ ty1 `eqType` ty2
#endif
