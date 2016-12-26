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

import Control.Monad (guard,unless)
import Data.Monoid (Any(..))
import Data.Char (isSpace)
import Data.Data (Data)
import Data.Generics (mkQ,everything)
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

import TcRnDriver
-- Temp
-- import HERMIT.GHC.Typechecker (initTcFromModGuts)
-- import ConCat.GHC

runTcMUnsafe :: HscEnv -> DynFlags -> ModGuts -> TcM a -> a
runTcMUnsafe env0 dflags _guts m = unsafePerformIO $ do
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- runTcInteractive env m
                  -- initTcFromModGuts env guts HsSrcFile False m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                                 $    text "Errors:" : pprErrMsgBagWithLoc errs
                                                   ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (fail $ showMsgs msgs) return mr
 where
   imports0 = ic_imports (hsc_IC env0)
   orphNames = mkModuleName <$> ["GHC.Float"]
               -- map moduleName (dep_orphs (mg_deps guts))
   env = -- pprTrace "runTcMUnsafe dep_mods" (ppr (dep_mods (mg_deps guts))) $
         -- pprTrace "runTcMUnsafe dep_orphs" (ppr (dep_orphs (mg_deps guts))) $
         env0 { hsc_IC = (hsc_IC env0) { ic_imports = map IIModule orphNames ++ imports0 } }
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

buildDictionary :: HscEnv -> DynFlags -> ModGuts -> InScopeEnv -> Type -> Maybe CoreExpr
buildDictionary env dflags guts inScope ty =
  do 
     -- pprTrace "buildDictionary" (ppr ty $$ text "-->" $$ ppr dict) (return ())
     -- pprTrace "buildDictionary" (ppr (exprFreeVars dict)) (return ())
     -- pprTrace "buildDictionary" (ppr (bnds,freeIds)) (return ())
     let ok = notNull bnds && null freeIds && not (hasCoercionHole dict)
#if 1
     unless ok $
       pprTrace "buildDictionary fail for"
         (ppr ty <> colon <+>
          if | null bnds       -> text "no bindings"
             | notNull freeIds -> text "free ids:" <+> ppr freeIds
             | otherwise       -> text "coercion hole")
         (return ())
#endif
     guard ok
     return dict
 where
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
