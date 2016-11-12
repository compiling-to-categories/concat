{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | GHC plugin converting to CCC form.

module ConCat.Plugin where

import Control.Arrow (first)
import Control.Applicative (liftA2,(<|>))
import Control.Monad (unless,guard)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe,isJust,catMaybes)
import Data.List (isPrefixOf,isSuffixOf,elemIndex,sort)
import Data.Char (toLower)
import Data.Data (Data)
import Data.Generics (GenericQ,mkQ,everything)
import Data.Sequence (Seq)
import qualified Data.Sequence as S
import qualified Data.Map as M
import Text.Printf (printf)

import GhcPlugins hiding (substTy)
import Class (classAllSelIds)
import CoreArity (etaExpand)
import CoreLint (lintExpr)
import DynamicLoading
import MkId (mkDictSelRhs)
import Pair (Pair(..))
import PrelNames (leftDataConName,rightDataConName)
import Type (coreView)
import TcType (isIntTy, isFloatTy, isDoubleTy)
import FamInstEnv (normaliseType)
import TyCoRep                          -- TODO: explicit imports
import Unique (mkBuiltinUnique)

import ConCat.Misc (Unop,Binop)

-- Information needed for reification. We construct this info in
-- CoreM and use it in the reify rule, which must be pure.
data CccEnv = CccEnv { dtrace :: forall a. String -> SDoc -> a -> a
                     , cccV   :: Id
                     , idV    :: Id
                     }

-- Whether to run Core Lint after every step
lintSteps :: Bool
lintSteps = True -- False

type Rewrite a = a -> Maybe a
type ReExpr = Rewrite CoreExpr

#define Trying(str) e | dtrace ("Trying " ++ (str)) (e `seq` empty) False -> undefined

-- #define Trying(str)

ccc :: CccEnv -> ModGuts -> DynFlags -> InScopeEnv -> Var -> ReExpr
ccc (CccEnv {..}) guts dflags inScope x =
  traceRewrite "ccc" $
  (if lintSteps then lintReExpr else id) $
  go
 where
   go :: ReExpr
   go = \ case 
     e | dtrace "ccc go:" (ppr e) False -> undefined
     Trying("lambda")
     Var y | x == y ->
       return $ varApps idV [varType x] []
     Trying("bailing")
     _e -> dtrace "ccc" ("Unhandled:" <+> ppr _e) $
           Nothing
   traceRewrite :: (Outputable a, Outputable (f b)) =>
                   String -> Unop (a -> f b)
   traceRewrite str f a = pprTrans str a (f a)
   pprTrans :: (Outputable a, Outputable b) => String -> a -> b -> b
   pprTrans str a b = dtrace str (ppr a $$ "-->" $$ ppr b) b
   mkCcc :: Unop CoreExpr
   mkCcc e = varApps cccV [exprType e] [e]
   lintReExpr :: Unop ReExpr
   lintReExpr rew before =
     do after <- rew before
        let before' = mkCcc before
            oops str doc = pprPanic ("ccc post-transfo check. " ++ str)
                             (doc $$ ppr before' $$ "-->" $$ ppr after)
            beforeTy = exprType before'
            afterTy  = exprType after
        maybe (if beforeTy `eqType` afterTy then
                 return after
               else
                 oops "type change"
                  (ppr beforeTy <+> "vs" <+> ppr afterTy <+> "in"))
              (oops "Lint")
          (lintExpr dflags (varSetElems (exprFreeVars before)) before)

cccRule :: CccEnv -> ModGuts -> CoreRule
cccRule env guts =
  BuiltinRule { ru_name  = fsLit "ccc"
              , ru_fn    = varName (cccV env)
              , ru_nargs = 2  -- including type arg
              , ru_try   = \ dflags inScope _fn [_ty,arg] ->
                              case arg of 
                                Lam x body -> ccc env guts dflags inScope x body
                                _          -> Nothing
              }

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos =
  do -- pprTrace ("CCC install " ++ show opts) empty (return ())
     dflags <- getDynFlags
     -- Unfortunately, the plugin doesn't work in GHCi. Until I can fix it,
     -- disable under GHCi, so we can at least type-check conveniently.
     if hscTarget dflags == HscInterpreted then
        return todos
      else
       do reinitializeGlobals
          env <- mkCccEnv opts
          -- Add the rule after existing ones, so that automatically generated
          -- specialized ccc rules are tried first.
          let addRule guts = pure (on_mg_rules (++ [cccRule env guts]) guts)
          return $   CoreDoPluginPass "Ccc insert rule" addRule
                   : CoreDoSimplify 2 mode
                   : todos
 where
   -- flagCcc guts = 
   -- Extra simplifier pass for reification.
   -- Rules on, no inlining, and case-of-case.
   mode = SimplMode { sm_names      = ["Ccc simplifier pass"]
                    , sm_phase      = InitialPhase
                    , sm_rules      = True  -- important
                    , sm_inline     = False -- important
                    , sm_eta_expand = False -- ??
                    , sm_case_case  = True  -- important
                    }

mkCccEnv :: [CommandLineOption] -> CoreM CccEnv
mkCccEnv opts = do
  -- liftIO $ putStrLn ("Options: " ++ show opts)
  hsc_env <- getHscEnv
  let tracing = "trace" `elem` opts
      dtrace :: String -> SDoc -> a -> a
      dtrace str doc | tracing   = pprTrace str doc
                     | otherwise = id
      lookupRdr :: ModuleName -> (String -> OccName) -> (Name -> CoreM a) -> String -> CoreM a
      lookupRdr modu mkOcc mkThing str =
        maybe (panic err) mkThing =<<
          liftIO (lookupRdrNameInModuleForPlugins hsc_env modu (Unqual (mkOcc str)))
       where
         err = "reify installation: couldn't find "
               ++ str ++ " in " ++ moduleNameString modu
      lookupTh mkOcc mk modu = lookupRdr (mkModuleName modu) mkOcc mk
      findId = lookupTh mkVarOcc  lookupId
      findTc = lookupTh mkTcOcc   lookupTyCon
      findRepTc   = findTc "ConCat.Rep"
      findBaseId  = findId "GHC.Base"
      findMiscId  = findId "ConCat.Misc"
  ruleBase <- getRuleBase
  dtrace "mkReifyEnv: getRuleBase ==" (ppr ruleBase) (return ())
  idV        <- findBaseId "id"
  ccV        <- findMiscId "ccc"
  return (CccEnv { .. })


{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

on_mg_rules :: Unop [CoreRule] -> Unop ModGuts
on_mg_rules f mg = mg { mg_rules = f (mg_rules mg) }

-- fqVarName :: Var -> String
-- fqVarName = qualifiedName . varName

uqVarName :: Var -> String
uqVarName = getOccString . varName

-- Keep consistent with stripName in Exp.
uniqVarName :: Var -> String
uniqVarName v = uqVarName v ++ "_" ++ show (varUnique v)

-- Swiped from HERMIT.GHC
-- | Get the fully qualified name from a 'Name'.
qualifiedName :: Name -> String
qualifiedName nm = modStr ++ getOccString nm
    where modStr = maybe "" (\m -> moduleNameString (moduleName m) ++ ".") (nameModule_maybe nm)

-- | Substitute new subexpressions for variables in an expression
subst :: [(Id,CoreExpr)] -> Unop CoreExpr
subst ps = substExpr "subst" (foldr add emptySubst ps)
 where
   add (v,new) sub = extendIdSubst sub v new

subst1 :: Id -> CoreExpr -> Unop CoreExpr
subst1 v e = subst [(v,e)]

onHead :: Unop a -> Unop [a]
onHead f (c:cs) = f c : cs
onHead _ []     = []

collectTyArgs :: CoreExpr -> (CoreExpr,[Type])
collectTyArgs = go []
 where
   go tys (App e (Type ty)) = go (ty:tys) e
   go tys e                 = (e,tys)

collectTysDictsArgs :: CoreExpr -> (CoreExpr,[Type],[CoreExpr])
collectTysDictsArgs e = (h,tys,dicts)
 where
   (e',dicts) = collectArgsPred isPred e
   (h,tys)    = collectTyArgs e'
   isPred ex  = not (isTyCoArg ex) && isPredTy (exprType ex)

collectArgsPred :: (CoreExpr -> Bool) -> CoreExpr -> (CoreExpr,[CoreExpr])
collectArgsPred p = go []
 where
   go args (App fun arg) | p arg = go (arg:args) fun
   go args e                     = (e,args)

collectTyCoDictArgs :: CoreExpr -> (CoreExpr,[CoreExpr])
collectTyCoDictArgs = collectArgsPred isTyCoDictArg

isTyCoDictArg :: CoreExpr -> Bool
isTyCoDictArg e = isTyCoArg e || isPredTy (exprType e)

-- isConApp :: CoreExpr -> Bool
-- isConApp (collectArgs -> (Var (isDataConId_maybe -> Just _), _)) = True
-- isConApp _ = False

-- TODO: More efficient isConApp, discarding args early.

stringExpr :: String -> CoreExpr
stringExpr = Lit . mkMachString

varNameExpr :: Id -> CoreExpr
varNameExpr = stringExpr . uniqVarName

pattern FunTy :: Type -> Type -> Type
pattern FunTy dom ran <- (splitFunTy_maybe -> Just (dom,ran))
 where FunTy = mkFunTy

-- TODO: Replace explicit uses of splitFunTy_maybe

-- TODO: Look for other useful pattern synonyms

pattern FunCo :: Role -> Coercion -> Coercion -> Coercion
pattern FunCo r dom ran <- TyConAppCo r (isFunTyCon -> True) [dom,ran]
 where FunCo = mkFunCo

onCaseRhs :: Type -> Unop (Unop CoreExpr)
onCaseRhs altsTy' f (Case scrut v _ alts) =
  Case scrut v altsTy' (onAltRhs f <$> alts)
onCaseRhs _ _ e = pprPanic "onCaseRhs. Not a case: " (ppr e)

onAltRhs :: Unop CoreExpr -> Unop CoreAlt
onAltRhs f (con,bs,rhs) = (con,bs,f rhs)

-- To help debug. Sometimes I'm unsure what constructor goes with what ppr.
coercionTag :: Coercion -> String
coercionTag Refl        {} = "Refl"
coercionTag TyConAppCo  {} = "TyConAppCo"
coercionTag AppCo       {} = "AppCo"
coercionTag ForAllCo    {} = "ForAllCo"
coercionTag CoVarCo     {} = "CoVarCo"
coercionTag AxiomInstCo {} = "AxiomInstCo"
coercionTag UnivCo      {} = "UnivCo"
coercionTag SymCo       {} = "SymCo"
coercionTag TransCo     {} = "TransCo"
coercionTag AxiomRuleCo {} = "AxiomRuleCo"
coercionTag NthCo       {} = "NthCo"
coercionTag LRCo        {} = "LRCo"
coercionTag InstCo      {} = "InstCo"
coercionTag CoherenceCo {} = "CoherenceCo"
coercionTag KindCo      {} = "KindCo"
coercionTag SubCo       {} = "SubCo"

-- TODO: Should I unfold (inline application head) earlier? Doing so might
-- result in much simpler generated code by avoiding many beta-redexes. If I
-- do, take care not to inline "primitives". I think it'd be fairly easy.

-- Try to inline an identifier.
-- TODO: Also class ops
inlineId :: Id -> Maybe CoreExpr
inlineId v = maybeUnfoldingTemplate (realIdUnfolding v)

-- Adapted from Andrew Farmer's getUnfoldingsT in HERMIT.Dictionary.Inline:
inlineClassOp :: Id -> Maybe CoreExpr
inlineClassOp v =
  case idDetails v of
    ClassOpId cls -> mkDictSelRhs cls <$> elemIndex v (classAllSelIds cls)
    _             -> Nothing

onExprHead :: (Id -> Maybe CoreExpr) -> ReExpr
onExprHead h = (fmap.fmap) simpleOptExpr $
               go id
 where
   go cont (Var v)       = cont <$> h v
   go cont (App fun arg) = go (cont . (`App` arg)) fun
   go cont (Cast e co)   = go (cont . (`Cast` co)) e
   go _ _                = Nothing

-- The simpleOptExpr here helps keep simplification going.

-- Identifier not occurring in a given variable set
freshId :: VarSet -> String -> Type -> Id
freshId used nm ty =
  uniqAway (mkInScopeSet used) $
  mkSysLocal (fsLit nm) (mkBuiltinUnique 17) ty

infixl 3 <+
(<+) :: Binop (a -> Maybe b)
(<+) = liftA2 (<|>)

apps :: CoreExpr -> [Type] -> [CoreExpr] -> CoreExpr
apps e tys es = mkApps e (map Type tys ++ es)

varApps :: Id -> [Type] -> [CoreExpr] -> CoreExpr
varApps = apps . Var

conApps :: DataCon -> [Type] -> [CoreExpr] -> CoreExpr
conApps = varApps . dataConWorkId

-- Split into Var head, type arguments, and other arguments (breaking at first
-- non-type).
unVarApps :: CoreExpr -> Maybe (Id,[Type],[CoreExpr])
unVarApps (collectArgs -> (Var v,allArgs)) = Just (v,tys,others)
 where
   (tys,others) = first (map unType) (span isTypeArg allArgs)
   unType (Type t) = t
   unType e        = pprPanic "unVarApps - unType" (ppr e)
unVarApps _ = Nothing
