{-# LANGUAGE TupleSections #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE MultiWayIf #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fno-warn-unused-binds #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-matches #-} -- TEMP

-- | GHC plugin converting to CCC form.

module ConCat.Plugin where

import Data.Monoid (Any(..))
import Control.Arrow (first,second,(***))
import Control.Applicative (liftA2,(<|>))
import Control.Monad (unless,when,guard,(<=<))
import Data.Foldable (toList)
import Data.Maybe (isNothing,isJust,fromMaybe,catMaybes)
import Data.List (isPrefixOf,isSuffixOf,elemIndex,sort,stripPrefix)
import Data.Char (toLower)
import Data.Data (Data)
import Data.Generics (GenericQ,GenericM,gmapM,mkQ,mkT,mkM,everything,everywhere',everywhereM)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Text.Printf (printf)

import GhcPlugins hiding (substTy,cat)
import Class (classAllSelIds)
import CoreArity (etaExpand)
import CoreLint (lintExpr)
import DynamicLoading
import MkId (mkDictSelRhs,coerceId)
import Pair (Pair(..))
import PrelNames (leftDataConName,rightDataConName)
import Type (coreView)
import TcType (isIntTy)
import FamInstEnv (normaliseType)
import TyCoRep                          -- TODO: explicit imports
import Unique (mkBuiltinUnique)
-- For normaliseType etc
import FamInstEnv

import ConCat.Misc (Unop,Binop,Ternop,PseudoFun(..),(~>))
import ConCat.Simplify
import ConCat.BuildDictionary

-- Information needed for reification. We construct this info in
-- CoreM and use it in the ccc rule, which must be pure.
data CccEnv = CccEnv { dtrace           :: forall a. String -> SDoc -> a -> a
                     , cccV             :: Id
                     , idV              :: Id
                     , constV           :: Id
                     , forkV            :: Id
                     , applyV           :: Id
                     , composeV         :: Id
                     , curryV           :: Id
                     , uncurryV         :: Id
                     , ifV              :: Id
                     , exlV             :: Id
                     , exrV             :: Id
                     , constFunV        :: Id
                     , reprCV           :: Id
                     , abstCV           :: Id
                     , coerceV          :: Id
                     , bottomCV         :: Id
                     , repTc            :: TyCon
                  -- , hasRepMeth       :: HasRepMeth
                     -- , hasRepFromAbstCo :: Coercion   -> CoreExpr
                     , prePostV         :: Id
                  -- , lazyV            :: Id
                     , boxers           :: Map TyCon Id  -- to remove
                     , tagToEnumV       :: Id
                     , bottomV          :: Id
                     , boxIBV           :: Id
                  -- , reboxV           :: Id
                     , inlineV          :: Id
                  -- , coercibleTc      :: TyCon
                  -- , coerceV          :: Id
                     , polyOps          :: PolyOpsMap
                     , monoOps          :: MonoOpsMap
                     , hsc_env          :: HscEnv
                     , ruleBase         :: RuleBase  -- to remove
                     }

-- Map from fully qualified name of standard operation.
type MonoOpsMap = Map String (Var,[Type])

-- Map from fully qualified name of standard operation.
type PolyOpsMap = Map String Var

-- Whether to run Core Lint after every step
lintSteps :: Bool
lintSteps = True -- False

type Rewrite a = a -> Maybe a
type ReExpr = Rewrite CoreExpr

-- #define Trying(str) e_ | dtrace ("Trying " ++ (str)) (e_ `seq` empty) False -> undefined
-- #define Trying(str) e_ | pprTrace ("Trying " ++ (str)) (e_ `seq` empty) False -> undefined
#define Trying(str)

#define Doing(str) dtrace "Doing" (text (str)) id $
-- #define Doing(str) pprTrace "Doing" (text (str)) id $
-- #define Doing(str)

-- Category
type Cat = Type

ccc :: CccEnv -> Ops -> Type -> ReExpr
ccc (CccEnv {..}) (Ops {..}) cat =
  traceRewrite "ccc" $
  (if lintSteps then lintReExpr else id) $
  go
 where
   go :: ReExpr
   go = \ case
     e | dtrace ("go ccc "++pp cat++":") (pprWithType e) False -> undefined
     -- Sanity check: ccc should only take functions.
     e@(exprType -> isFunTy -> False) ->
       pprPanic "ccc/go: not of function type" (pprWithType e)
     -- Temporarily make `ccc` bail on polymorphic terms. Doing so will speed up
     -- my experiments, since much time is spent optimizing rules, IIUC. It'll
     -- be important to restore polymorphic transformation later for useful
     -- separate compilation.
--      Trying("top poly bail")
--      (exprType -> isMonoTy -> False) ->
--        Doing("top poly bail")
--        Nothing
     Trying("top Lam")
     Lam x body -> goLam x body
     Trying("top reCat")
     (reCat -> Just e') ->
       Doing("top reCat")
       Just e'
     Trying("top Avoid pseudo-app")
     (isPseudoApp -> True) ->
       Doing("top Avoid pseudo-app")
       Nothing
#if 0
     Trying("top ruled var app")
     (collectArgs -> (Var (fqVarName -> nm),args))
       | Just arity <- Map.lookup nm cccRuledArities
       , length args >= arity
       -> dtrace "top ruled var app" (text nm) $
          Nothing
#endif
     Trying("top Let")
     Let bind@(NonRec v rhs) body ->
       -- Experiment: always float.
       if {- True || -} substFriendly (isClosed cat) rhs || idOccs v body <= 1 then
         Doing("top Let float")
         return (Let bind (mkCcc body))
         -- -- Experiment:
         -- Doing("top Let substitution")
         -- return (mkCcc (subst1 v rhs body))
       else
         Doing("top Let to beta-redex")
         go (App (Lam v body) rhs)
     -- ccc-of-case. Maybe restrict to isTyCoDictArg for all bound variables, but
     -- perhaps I don't need to.
     Trying("top Case unfold")
     Case scrut wild rhsTy alts
       | Just scrut' <- unfoldMaybe scrut
       -> Doing("top Case unfold")  --  of dictionary
          return $ mkCcc (Case scrut' wild rhsTy alts)
          -- TODO: also for lam?
#if 1
     Trying("top Case")
     Case scrut wild rhsTy alts ->
       Doing("top Case")
       return $ Case scrut wild (catTy rhsTy) (onAltRhs mkCcc <$> alts)
#endif
#if 1
     Trying("top nominal Cast")
     Cast e co@( -- dtrace "top nominal cast co" (pprCoWithType co {-<+> (ppr (setNominalRole_maybe co))-}) id
                setNominalRole_maybe -> Just (reCatCo -> Just co')) ->
       -- etaExpand turns cast lambdas into themselves
       Doing("top nominal cast")
       let co'' = downgradeRole (coercionRole co) (coercionRole co') co' in
         -- pprTrace "top nominal Cast" (ppr co $$ text "-->" $$ ppr co'') $
         return (Cast (mkCcc e) co'')
       -- I think GHC is undoing this transformation, so continue eagerly
       -- (`Cast` co') <$> go e
#endif
#if 1
     Trying("top representational cast")
#if 0
     -- See notes from 2016-01-08. I'd like to tak this route, using Coercible
     -- instead of CoerceCat. However, in some categories (including L s, D s,
     -- and (:>)), the type parameters have nominal roles, so representational
     -- coercions don't translate from (->). For L and D, the issue is the V
     -- type family, while for (:>), it's the Buses GADT (IIUC).
     Cast e' (coercionKind -> Pair (catTy -> dom) (catTy -> cod))
       -> Doing("top representational cast 1")
          -- Will I get unnecessary coerceCs due to nominal-able sub-coercions?
          dtrace "mkCoerce 1" (pprWithType (Var coerceId)) $
          dtrace "mkCoerce 2" (pprWithType (varApps coerceId [dom,cod] [])) $
          dtrace "mkCoerce 3" (pprWithType (onDict (varApps coerceId [dom,cod] []))) $
          return $ onDict (varApps coerceId [dom,cod] []) `App` mkCcc e'
#else
     e@(Cast e' (coercionRole -> Representational))
       | FunTy a  b  <- exprType e
       , FunTy a' b' <- exprType e'
       ->
          Doing("top representational cast")
          -- Will I get unnecessary coerceCs due to nominal-able sub-coercions?
          return $ mkCompose cat (mkCoerceC cat b' b) $
                   mkCompose cat (mkCcc e') $
                   mkCoerceC cat a a'
#endif
#else
     Trying("top cast unfold")
     Cast (unfoldMaybe -> Just body') co ->
       Doing("top cast unfoldMaybe")
       return $ mkCcc $ mkCast body' co
     -- Helpful??
     Trying("top cast eta-reduce")
     Cast (etaReduce_maybe -> Just body') co ->
       Doing("top cast eta-reduce")
       return $ mkCcc $ mkCast body' co
     Trying("top cast normalize")
     Cast e co@(coercionKind -> Pair dom cod)
       | let norm = normaliseType famEnvs (coercionRole co)
             (dco,dom') = norm dom
             (cco,cod') = norm cod
       , dom' `eqType` cod'
       -- , not (isReflCo dco && isReflCo cco) -- mkCast will take care of it
       -> Doing("top cast normalize")
          -- dtrace "top cast normalize" (ppr ((dom,cod), (dco,dom'), (cco,cod')) $$ pprCoWithType (dco `mkTransCo` mkSymCo cco))
          return $ mkCcc $
            mkCast e (dco `mkTransCo` mkSymCo cco)
     Trying("top abstC codomain")
     e | _dom `FunTy` cod <- exprType e
       , Just repr <- mkReprC'_maybe funCat cod
       , Just abst <- mkAbstC'_maybe    cat cod
       -> Doing("top abstC codomain")
          return $
           mkCompose cat
             abst
             (mkCcc (inlineE (mkCompose funCat (inlineE repr) e)))
     Trying("top abstC domain")
     e | dom `FunTy` _cod <- exprType e
       , Just repr <- mkReprC'_maybe    cat dom
       , Just abst <- mkAbstC'_maybe funCat dom
       -> Doing("top abstC domain")
          return $
           mkCompose cat
             (mkCcc (inlineE (mkCompose funCat e (inlineE abst))))
             repr
     Trying("top cast abstC codomain")
     Cast (etaExpand 1 -> Lam x body) co
       | Just meth <- hrMeth (exprType body)
       -> Doing("top cast abstC codomain")
          return $ mkCcc $
            let a = meth abstV
                r = meth reprV
                FunTy _ rty = exprType r
                idr = mkId funCat rty
            in
              mkCast (Lam x (a `App` (idr `App` (r `App` body)))) co
#endif
#if 0
     Trying("top recast")
     Cast e co ->
       Doing("top recast")
       -- return (mkCcc (recast co `App` e))
       let re = recast co in
         dtrace "top recaster" (ppr re) $
         return (mkCcc (re `App` e))
#endif
     Trying("top abstReprCon")
     -- Constructor application
     e@(collectArgs -> (Var (isDataConId_maybe -> Just dc),_))
       | let (binds,body) = collectBinders (etaExpand (dataConRepArity dc) e)
             bodyTy = exprType body
       -- , dtrace "top abstReprCon abst type" (ppr bodyTy) True
       , Just repr <- mkReprC'_maybe funCat bodyTy
       , Just abst <- mkAbstC'_maybe funCat bodyTy
       -> Doing("top abstReprCon")
          return $ mkCcc $
           mkLams binds $
            abst `App` (inlineE repr `App` body)
#if 0
     Trying("top lazy")
     (collectArgs -> (Var ((== lazyV) -> True),_ty:f:args)) ->
       Doing("top lazy")
       return (mkCcc (mkCoreApps f args))
#endif
     Trying("top unfold")
     e@(exprHead -> Just _v)
       | -- Temp hack: avoid unfold/case-of-product loop.
         {- isCast e || not (isSelectorId _v || isAbstReprId _v)
       , -} Just e' <- unfoldMaybe e
       -> Doing("top unfold")
          -- , dtrace "top unfold" (ppr e <+> text "-->" <+> ppr e') True
          return (mkCcc e')
     Trying("top App")
     e@(App u v)
       | liftedExpr v
       , Just v' <- mkConst' cat dom v
       , Just uncU' <- mkUncurryMaybe cat (mkCcc u)
       -> -- dtrace "go App v'" (pprWithType v') $
          Doing("top App")
          -- u v == uncurry u . (constFun v &&& id)
          return (mkCompose cat uncU' (mkFork cat v' (mkId cat dom)))
      where
        Just (dom,_) = splitFunTy_maybe (exprType e)
#if 0
     Trying("top Wait for unfolding")
     (collectArgs -> (Var v,_)) | waitForVar ->
       Doing("top Wait for unfolding of " ++ fqVarName v)
       Nothing
      where
        -- expand later
        waitForVar = not (isPairVar v)
     -- go e = dtrace "go etaExpand to" (ppr (etaExpand 1 e)) $
     --        go (etaExpand 1 e)
     --        -- return $ mkCcc (etaExpand 1 e)
     -- TODO: If I don't etaReduceN, merge goLam back into the go Lam case.
#endif
     _e -> Doing("top Unhandled")
           -- pprTrace "ccc go. Unhandled" (ppr _e) $ Nothing
           -- pprPanic "ccc go. Unhandled" (ppr _e)
           Nothing
   -- goLam x body | dtrace "goLam:" (ppr (Lam x body)) False = undefined
   -- go _ = Nothing
   goLam x body | Just e' <- etaReduce_maybe (Lam x body) =
    Doing("lam eta-reduce")
    return (mkCcc e')
   goLam x body = case body of
     Trying("lam Id")
     Var y | x == y -> Doing("lam Id")
                       return (mkId cat xty)
     Trying("lam Poly const")
     _ | isConst, not (isFunTy bty), not (isMonoTy bty)
       -> Doing("lam Poly const bail")
          -- dtrace("lam Poly const: bty & isMonoTy") (ppr (bty, isMonoTy bty)) $
          Nothing
     Trying("lam bottom") -- must come before "lam Const" and "lam App"
     (collectArgs -> (Var ((== bottomV) -> True),[Type ty]))
       | Just e' <- mkBottomC cat xty ty
       -> Doing("lam bottom")
          return e'
     Trying("lam Const")
     -- _ | isConst, dtrace "goLam mkConst'" (ppr (exprType body,mkConst' cat xty body)) False -> undefined
     _ | isConst, Just body' <- mkConst' cat xty body
       -> Doing("lam mkConst'")
       return body'
     Trying("lam Avoid pseudo-app")
     (isPseudoApp -> True) ->
       Doing("lam Avoid pseudo-app")
       Nothing
     Trying("lam Pair")
     (collectArgs -> (PairVar,(Type a : Type b : rest))) ->
       -- | dtrace "Pair" (ppr rest) False -> undefined
       case rest of
         []    -> -- (,) == curry id
                  -- Do we still need this case, or is it handled by catFun?
                  Doing("lam Plain (,)")
                  return (mkCurry cat (mkId cat (pairTy a b)))
         [_]   -> Doing("lam Pair eta-expand")
                  goLam x (etaExpand 1 body)
         [u,v] -> Doing("lam Pair")
                  -- dtrace "Pair test" (pprWithType u <> comma <+> pprWithType v) $
                  return (mkFork cat (mkCcc (Lam x u)) (mkCcc (Lam x v)))
         _     -> pprPanic "goLam Pair: too many arguments: " (ppr rest)
#if 1
     -- Revisit.
     Trying("lam abstReprCon")
     -- Constructor applied to ty/co/dict arguments
     e@(collectNonTyCoDictArgs ->
        (collectTyCoDictArgs -> (Var (isDataConId_maybe -> Just dc),_), args))
       | let (binds,body') = collectBinders (etaExpand (dataConRepArity dc - length args) e)
             bodyTy = exprType body'
       , Just repr <- mkReprC'_maybe funCat bodyTy
       , Just abst <- mkAbstC'_maybe funCat bodyTy
       -> Doing("lam abstReprCon")
          return $ mkCcc $ Lam x $
            mkLams binds $ abst `App` (inlineE repr `App` body')
#endif
     Trying("lam Let")
     -- TODO: refactor with top Let
     _e@(Let bind@(NonRec v rhs) body') ->
       -- dtrace "lam Let subst criteria" (ppr (substFriendly (isClosed cat) rhs, not xInRhs, idOccs v body')) $
       if substFriendly (isClosed cat) rhs || not xInRhs || idOccs v body' <= 1 then
         -- TODO: decide whether to float or substitute.
         -- To float, x must not occur freely in rhs
         -- return (mkCcc (Lam x (subst1 v rhs body'))) The simplifier seems to
         -- re-let my dicts if I let it. Will the simplifier re-hoist later? If
         -- so, we can still let-hoist instead of substituting.
         if xInRhs then
           Doing("lam Let subst")
           -- TODO: mkCcc instead of goLam?
           -- Just (mkCcc (Lam x (subst1 v rhs body')))
           -- Sometimes GHC then un-substitutes, leading to a loop.
           -- Using goLam prevents GHC from getting that chance. (Always?)
           goLam x (subst1 v rhs body')
           -- Yet another choice is to lambda-lift the binding over x and then
           -- float the let past the x binding.
         else
           Doing("lam Let float")
           return (Let bind (mkCcc (Lam x body')))
       else
         Doing("lam Let to beta-redex")
         goLam x (App (Lam v body') rhs)
      where
        xInRhs = x `isFreeIn` rhs
     Trying("lam eta-reduce")
     (etaReduce_maybe -> Just e') ->
       Doing("lam eta-reduce")
       goLam x e'
     Trying("lam Lam")
     Lam y e ->
       -- (\ x -> \ y -> U) --> curry (\ z -> U[fst z/x, snd z/y])
       Doing("lam Lam")
       -- dtrace "Lam isDeads" (ppr (isDeadBinder x, isDeadBinder y)) $
       -- dtrace "Lam sub" (ppr sub) $
       -- TODO: maybe let instead of subst
       -- Substitute rather than making a Let, to prevent infinite regress.
       return $ mkCurry cat (mkCcc (Lam z (subst sub e)))
      where
        yty = varType y
        z = freshId (exprFreeVars e) zName (pairTy xty yty)
        zName = uqVarName x ++ "_" ++ uqVarName y
        sub = [(x,mkEx funCat exlV (Var z)),(y,mkEx funCat exrV (Var z))]
        -- TODO: consider using fst & snd instead of exl and exr here
     Trying("lam boxer")
     (boxCon -> Just e') ->
       Doing("lam boxer")
       return (mkCcc (Lam x e'))
     Trying("lam Case of boxer")
     e@(Case scrut wild _ty [(_dc,[unboxedV],rhs)])
       | Just (tc,[]) <- splitTyConApp_maybe (varType wild)
       , Just boxV <- Map.lookup tc boxers
       -> Doing("lam Case of boxer")
          let wild' = setIdOccInfo wild NoOccInfo
              tweak :: Unop CoreExpr
              tweak (Var v) | v == unboxedV =
                pprPanic "lam Case of boxer: bare unboxed var" (ppr e)
              tweak (App (Var f) (Var v)) | f == boxV, v == unboxedV = Var wild'
              tweak e' = e'
          in
            -- Note top-down (everywhere') instead of bottom-up (everywhere)
            -- so that we can find 'boxI v' before v.
            return (mkCcc (Lam x (Let (NonRec wild' scrut) (everywhere' (mkT tweak) rhs))))
     Trying("lam Case default")
     Case _scrut (isDeadBinder -> True) _rhsTy [(DEFAULT,[],rhs)] ->
       Doing("lam case-default")
       return (mkCcc (Lam x rhs))
     Trying("lam Case nullary")
     Case _scrut (isDeadBinder -> True) _rhsTy [(_, [], rhs)] ->
       Doing("lam Case nullary")
       return (mkCcc (Lam x rhs))
       -- TODO: abstract return (mkCcc (Lam x ...))
     Trying("lam Case to let")
     Case scrut v@(isDeadBinder -> False) _rhsTy [(_, bs, rhs)]
       | isEmptyVarSet (mkVarSet bs `intersectVarSet` exprFreeVars rhs) ->
       Doing("lam Case to let")
       return (mkCcc (Lam x (Let (NonRec v scrut) rhs)))

     Trying("lam Case of Bool")
     e@(Case scrut wild rhsTy [(DataAlt false, [], rhsF),(DataAlt true, [], rhsT)])
         | false == falseDataCon && true == trueDataCon ->
       -- To start, require v to be unused. Later, extend.
       if not (isDeadBinder wild) && wild `isFreeIns` [rhsF,rhsT] then
            pprPanic "lam Case of Bool: live wild var (not yet handled)" (ppr e)
       else
          Doing("lam Case of Bool")
          return $
            mkIfC cat rhsTy (mkCcc (Lam x scrut))
              (mkCcc (Lam x rhsT)) (mkCcc (Lam x rhsF))

     Trying("lam Case of product")
     e@(Case scrut wild _rhsTy [(DataAlt dc, [a,b], rhs)])
         | isBoxedTupleTyCon (dataConTyCon dc) ->
       -- To start, require v to be unused. Later, extend.
       if False && not (isDeadBinder wild) && wild `isFreeIn` rhs then
            pprPanic "lam Case of product: live wild var (not yet handled)" (ppr e)
       else
          Doing("lam Case of product")
          --    \ x -> case scrut of c { (a, b) -> rhs }
          -- == \ x -> let c = scrut in let {a = exl c; b = exr c} in rhs
          let -- cName = uqVarName a ++ "_" ++ uqVarName b
              -- c     = freshId (exprFreeVars e) cName (exprType scrut)
              c = zapIdOccInfo wild
              sub   = [(a,mkEx funCat exlV (Var c)),(b,mkEx funCat exrV (Var c))]
          in
            return (mkCcc (Lam x (mkCoreLets
                                  [ NonRec c scrut
                                  , NonRec a (mkEx funCat exlV (Var c))
                                  , NonRec b (mkEx funCat exrV (Var c)) ] rhs)))
     Trying("lam Case unfold")
     Case scrut v altsTy alts
       | Just scrut' <- unfoldMaybe' scrut
       -> Doing("lam Case unfold")
          return $ mkCcc $ Lam x $
           Case scrut' v altsTy alts
     Trying("lam nominal Cast")
     Cast body' co@(setNominalRole_maybe -> Just co') ->
       -- etaExpand turns cast lambdas into themselves
       Doing("lam nominal cast")
       let r  = coercionRole co
           r' = coercionRole co'         -- always Nominal, isn't it?
           co'' = downgradeRole r r' co' -- same as co?
       in
         -- pprTrace "lam nominal Cast" (ppr co $$ text "-->" $$ ppr co'') $
         return (mkCcc (Cast (Lam x body') (FunCo r (mkReflCo r xty) co'')))
     Trying("lam representational cast")
#if 0
     Cast e co ->
       Doing("lam representational cast")
       -- Will I get unnecessary coerceCs due to nominal-able sub-coercions?
       -- TODO: convert to mkCoerceC also. Then eliminate mkCoerceC, and
       -- rename mkCoerceC.
       return $ mkCompose cat (mkCoerceC cat co) $
                mkCcc (Lam x e)
#else
     e@(Cast e' _) ->
       Doing("lam representational cast")
       -- Will I get unnecessary coerceCs due to nominal-able sub-coercions?
       -- TODO: convert to mkCoerceC also. Then eliminate mkCoerceC, and
       -- rename mkCoerceC.
       return $ mkCompose cat (mkCoerceC cat (exprType e') (exprType e)) $
                mkCcc (Lam x e')
#endif
#if 1
     -- Does unfolding suffice as an alternative? Not quite, since lambda-bound
     -- variables can appear as scrutinees. Maybe we could eliminate that
     -- possibility with another transformation.
     -- 2016-01-04: I moved lam abstReprCase after unfold
     Trying("lam abstReprCase")
     -- Do I also need top abstReprCase?
     Case scrut v@(varType -> vty) altsTy alts
       | Just repr <- mkReprC'_maybe funCat vty
       , Just abst <- mkAbstC'_maybe funCat vty
       -> Doing("lam abstReprCase")
          return $ mkCcc $ Lam x $
           Case (inlineE abst `App` (repr `App` scrut)) v altsTy alts
#endif
#if 0
     Trying("lam recast")
     Cast e co ->
       Doing("lam recast")
       -- return (mkCcc (recast co `App` e))
       let re = recast co in
         dtrace "lam recaster" (ppr re) $
         return (mkCcc (Lam x (re `App` e)))
#endif
#if 1
     Trying("lam App compose")
     -- (\ x -> U V) --> U . (\ x -> V) if x not free in U
     u `App` v | liftedExpr v
               , not (x `isFreeIn` u)
               -> Doing("lam App compose")
                  return $ mkCompose cat (mkCcc u) (mkCcc (Lam x v))
#endif
     Trying("lam App")
     -- (\ x -> U V) --> apply . (\ x -> U) &&& (\ x -> V)
     u `App` v | liftedExpr v
               -- , pprTrace "lam App mkApplyMaybe -->" (ppr (mkApplyMaybe cat vty bty, cat)) True
               , Just app <- mkApplyMaybe cat vty bty ->
       Doing("lam App")
       return $ mkCompose cat
                  app -- (mkApply cat vty bty)
                  (mkFork cat (mkCcc (Lam x u)) (mkCcc (Lam x v)))
      where
        vty = exprType v
     Trying("lam unfold")
     e'| Just body' <- unfoldMaybe e'
       -> Doing("lam unfold")
          -- dtrace "lam unfold" (ppr body <+> text "-->" <+> ppr body')
          return (mkCcc (Lam x body'))
          -- goLam x body'
          -- TODO: factor out Lam x (mkCcc ...)
     -- Give up
     _e -> pprPanic "ccc" ("lam Unhandled" <+> ppr _e)
           -- pprTrace "goLam" ("Unhandled" <+> ppr _e) $ Nothing
    where
      xty = varType x
      bty = exprType body
      isConst = not (x `isFreeIn` body)

pattern Coerce :: Cat -> Type -> Type -> CoreExpr
pattern Coerce k a b <-
  -- (collectArgs -> (Var (isCoerceV -> True), [Type k,Type a,Type b,_dict]))
  (collectArgs -> (Var (catSuffix -> Just "coerceC"), [Type k,Type a,Type b,_dict]))
  -- (collectArgs -> (Var (CatVar "coerceC"), [Type k,Type a,Type b,_dict]))

pattern Compose :: Cat -> Type -> Type -> Type -> CoreExpr -> CoreExpr -> CoreExpr
pattern Compose k a b c g f <-
  -- (collectArgs -> (Var (isComposeV -> True), [Type k,Type b,Type c, Type a,_catDict,_ok,g,f]))
  (collectArgs -> (Var (catSuffix -> Just "."), [Type k,Type b,Type c, Type a,_catDict,_ok,g,f]))
  -- (collectArgs -> (Var (CatVar "."), [Type k,Type b,Type c, Type a,_catDict,_ok,g,f]))

-- TODO: when the nested-pattern definition bug
-- (https://ghc.haskell.org/trac/ghc/ticket/12007) gets fixed (GHC 8.0.2), use
-- the CatVar version of Compose and Coerce.

-- For the composition BuiltinRule
composeR :: CccEnv -> Ops -> CoreExpr -> CoreExpr -> Maybe CoreExpr
-- composeR _ _ g f | pprTrace "composeR try" (ppr (g,f)) False = undefined
composeR (CccEnv {..}) (Ops {..}) _g@(Coerce k _b c) _f@(Coerce _k a _b')
  = -- pprTrace "composeR coerce" (ppr _g $$ ppr _f) $
    Just (mkCoerceC k a c)

-- composeR (CccEnv {..}) (Ops {..}) h (Compose _k _ _a _b' g f)
--   | pprTrace "composeR try re-assoc" (ppr h $$ ppr g $$ ppr f) False = undefined

composeR (CccEnv {..}) (Ops {..}) _h@(Coerce k _b c) (Compose _k _ a _b' _g@(Coerce _k' _z _a') f)
  = -- pprTrace "composeR coerce re-assoc" (ppr _h $$ ppr _g $$ ppr f) $
    Just (mkCompose k (mkCoerceC k a c) f)
composeR _ _ _ _ = Nothing

pattern CatVar :: String -> Id
pattern CatVar str <- (fqVarName -> stripPrefix (catModule ++ ".") -> Just str)

catSuffix :: Id -> Maybe String
catSuffix (CatVar suff) = Just suff
catSuffix _             = Nothing

isCoerceV :: Id -> Bool
isCoerceV (CatVar "coerceC") = True
isCoerceV _ = False
-- isCoerceV v = fqVarName v == catModule ++ "." ++ "coerceC"

isComposeV :: Id -> Bool
isComposeV (CatVar ".") = True
isComposeV _ = False
-- isComposeV v = fqVarName v == catModule ++ "." ++ "."

data Ops = Ops
 { inlineE        :: Unop CoreExpr
 , boxCon         :: ReExpr
 , catTy          :: Unop Type
 , reCatCo        :: Rewrite Coercion
 , repTy          :: Unop Type
 , unfoldOkay     :: CoreExpr -> Bool
 , unfoldMaybe'   :: ReExpr
 , unfoldMaybe    :: ReExpr
 , inlineMaybe    :: Id -> Maybe CoreExpr
 , noDictErr      :: forall a. SDoc -> Either SDoc a -> a
 , onDictTry      :: CoreExpr -> Either SDoc CoreExpr
 , onDictMaybe    :: ReExpr
 , onDict         :: Unop CoreExpr
 , buildDictMaybe :: Type -> Either SDoc CoreExpr
 , catOp          :: Cat -> Var -> [Type] -> CoreExpr
 , catOpMaybe     :: Cat -> Var -> [Type] -> Maybe CoreExpr
 , mkCcc          :: Unop CoreExpr  -- Any reason to parametrize over Cat?
 , mkId           :: Cat -> Type -> CoreExpr
 , mkCompose      :: Cat -> Binop CoreExpr
 , mkEx           :: Cat -> Var -> Unop CoreExpr
 , mkFork         :: Cat -> Binop CoreExpr
 , mkApplyMaybe   :: Cat -> Type -> Type -> Maybe CoreExpr
 , isClosed       :: Cat -> Bool
 , mkCurry        :: Cat -> Unop CoreExpr
 , mkUncurryMaybe :: Cat -> ReExpr
 , mkIfC          :: Cat -> Type -> Ternop CoreExpr
 , mkBottomC      :: Cat -> Type -> Type -> Maybe CoreExpr
 , mkConst        :: Cat -> Type -> ReExpr
 , mkConstFun     :: Cat -> Type -> ReExpr
 , mkConst'       :: Cat -> Type -> ReExpr
 , mkAbstC        :: Cat -> Type -> CoreExpr
 , mkReprC        :: Cat -> Type -> CoreExpr
 , mkReprC'       :: Cat -> Type -> CoreExpr
 , mkAbstC'       :: Cat -> Type -> CoreExpr
 , mkReprC'_maybe :: Cat -> Type -> Maybe CoreExpr
 , mkAbstC'_maybe :: Cat -> Type -> Maybe CoreExpr
 , mkCoerceC      :: Cat -> Type -> Type -> CoreExpr
 , traceRewrite   :: forall f a b. (Functor f, Outputable a, Outputable b) => String -> Unop (a -> f b)
 , tyArgs2_maybe  :: Type -> Maybe (Type,Type)
 , tyArgs2        :: Type -> (Type,Type)
 , pprTrans       :: forall a b. (Outputable a, Outputable b) => String -> a -> b -> b
 , lintReExpr     :: Unop ReExpr
 , catFun         :: ReExpr
 , transCatOp     :: ReExpr
 , reCat          :: ReExpr
 , isPseudoApp    :: CoreExpr -> Bool
 , isPseudoFun    :: Id -> Bool
 }

mkOps :: CccEnv -> ModGuts -> AnnEnv -> FamInstEnvs
      -> DynFlags -> InScopeEnv -> Type -> Ops
mkOps (CccEnv {..}) guts annotations famEnvs dflags inScope cat = Ops {..}
 where
   inlineE :: Unop CoreExpr
   inlineE e = varApps inlineV [exprType e] [e]  -- move outward
   -- Replace boxing constructors by their boxing function synonyms (boxI etc)
   boxCon :: ReExpr
   boxCon e0 | tweaked   = -- dtrace "boxCon" (ppr (e0,e1)) $
                           Just e1
             | otherwise = Nothing
    where
      (Any tweaked,e1) = everywhereM (mkM tweak) e0
      tweak :: CoreExpr -> (Any,CoreExpr)
      tweak e@(App (Var con) e')
        | isDataConWorkId con
        , Just (tc,[]) <- splitTyConApp_maybe (exprType e)
        , Just boxV <- Map.lookup tc boxers
        = (Any True, Var boxV `App` e')
      tweak ((Var v `App` Type ty) `App` e')
        | v == tagToEnumV && ty `eqType` boolTy
        = (Any True, Var boxIBV `App` e')
      tweak e = (Any False, e)
   -- hrMeth :: Type -> Maybe (Id -> CoreExpr)
   -- hrMeth ty = -- dtrace "hasRepMeth:" (ppr ty) $
   --             hasRepMeth dflags guts inScope ty
   -- Change categories
   catTy :: Unop Type
   catTy (tyArgs2 -> (a,b)) = mkAppTys cat [a,b]
   reCatCo :: Rewrite Coercion
   -- reCatCo co | dtrace "reCatCo" (ppr co) False = undefined
   reCatCo (FunCo r a b) = Just (mkAppCos (mkReflCo r cat) [a,b])
   reCatCo (splitAppCo_maybe -> Just
            (splitAppCo_maybe -> Just
             (Refl r _k,a),b)) =
     dtrace "reCatCo app" (ppr (r,_k,a,b))
     Just (mkAppCos (mkReflCo r cat) [a,b])
   reCatCo (co1 `TransCo` co2) = TransCo <$> reCatCo co1 <*> reCatCo co2
   reCatCo co = pprTrace "ccc reCatCo: unhandled coercion" (ppr co) $
                Nothing
   -- Interpret a representational cast
   -- TODO: Try swapping argument order
   repTy :: Unop Type
   repTy t = mkTyConApp repTc [t]
   -- coercibleTy :: Unop Type
   -- coercibleTy t = mkTyConApp coercibleTc [t]
   unfoldOkay :: CoreExpr -> Bool
   unfoldOkay (exprHead -> Just v) =
     -- pprTrace "unfoldOkay head" (ppr (v,isNothing (catFun (Var v)))) $
     isNothing (catFun (Var v))
   unfoldOkay _                    = False
   -- Temp hack: avoid exl/exr and reprC/abstC.
   unfoldMaybe' :: ReExpr
   unfoldMaybe' e@(exprHead -> Just v)
     | not (isSelectorId v || isAbstReprId v) = unfoldMaybe e
   unfoldMaybe' _ = Nothing                                    
   unfoldMaybe :: ReExpr
   -- unfoldMaybe e | dtrace "unfoldMaybe" (ppr (e,collectArgsPred isTyCoDictArg e)) False = undefined
   unfoldMaybe e | unfoldOkay e
                 -- | (Var v, _) <- collectArgsPred isTyCoDictArg e
                 -- -- , dtrace "unfoldMaybe" (text (fqVarName v)) True
                 -- , isNothing (catFun (Var v))
                 -- | True  -- experiment: don't restrict unfolding
                 = onExprHead ({- traceRewrite "inlineMaybe" -} inlineMaybe) e
                 | otherwise = Nothing
   -- unfoldMaybe = -- traceRewrite "unfoldMaybe" $
   --               onExprHead ({-traceRewrite "inlineMaybe"-} inlineMaybe)
   inlineMaybe :: Id -> Maybe CoreExpr
   -- inlineMaybe v | dtrace "inlineMaybe" (ppr v) False = undefined
   inlineMaybe v = (inlineId <+ -- onInlineFail <+ traceRewrite "inlineClassOp"
                                inlineClassOp) v
   -- onInlineFail :: Id -> Maybe CoreExpr
   -- onInlineFail v =
   --   pprTrace "onInlineFail idDetails" (ppr v <+> colon <+> ppr (idDetails v))
   --   Nothing
   noDictErr :: SDoc -> Either SDoc a -> a
   noDictErr doc =
     either (\ msg -> pprPanic "ccc - couldn't build dictionary for" (doc <> colon $$ msg)) id
   onDictTry :: CoreExpr -> Either SDoc CoreExpr
   onDictTry e | Just (ty,_) <- splitFunTy_maybe (exprType e)
               , isPredTy' ty = App e <$> buildDictMaybe ty
               | otherwise = return e
                             -- pprPanic "ccc / onDictMaybe: not a function from pred" (pprWithType e)
   onDictMaybe :: ReExpr
   onDictMaybe e = eitherToMaybe (onDictTry e)
   onDict :: Unop CoreExpr
   onDict f = noDictErr (pprWithType f) (onDictTry f)
   -- Yet another variant: keep applying to dictionaries as long as we have
   -- a predicate type. TODO: reassess and refactor these variants.
   onDicts :: Unop CoreExpr
   onDicts e | Just (ty,_) <- splitFunTy_maybe (exprType e)
             , isPredTy' ty = onDicts (onDict e)
             | otherwise    = e
   buildDictMaybe :: Type -> Either SDoc CoreExpr
   buildDictMaybe ty = simplifyE dflags False <$>  -- remove simplifyE call later?
                       buildDictionary hsc_env dflags guts inScope ty
   catOp :: Cat -> Var -> [Type] -> CoreExpr
   -- catOp k op tys | dtrace "catOp" (ppr (k,op,tys)) False = undefined
   catOp k op tys -- | dtrace "catOp" (pprWithType (Var op `mkTyApps` (k : tys))) True
                  = onDicts (Var op `mkTyApps` (k : tys))
   -- TODO: refactor catOp and catOpMaybe when the dust settles
   -- catOp :: Cat -> Var -> CoreExpr
   -- catOp k op = catOp k op []
   catOpMaybe :: Cat -> Var -> [Type] -> Maybe CoreExpr
   catOpMaybe k op tys = onDictMaybe (Var op `mkTyApps` (k : tys))
   mkCcc :: Unop CoreExpr  -- Any reason to parametrize over Cat?
   mkCcc e = varApps cccV [cat,a,b] [e]
    where
      (a,b) = fromMaybe (pprPanic "mkCcc non-function:" (pprWithType e)) $
              splitFunTy_maybe (exprType e)
   -- TODO: replace composeV with mkCompose in CccEnv
   -- Maybe other variables as well
   mkId :: Cat -> Type -> CoreExpr
   mkId k ty = onDict (catOp k idV [ty])
               -- onDict (catOp k idV `App` Type ty)
   mkCompose :: Cat -> Binop CoreExpr
   -- (.) :: forall b c a. (b -> c) -> (a -> b) -> a -> c
   mkCompose k g f
     | Just (b,c ) <- tyArgs2_maybe (exprType g)
     , Just (a,b') <- tyArgs2_maybe (exprType f)
     , b `eqType` b'
     = -- mkCoreApps (onDict (catOp k composeV `mkTyApps` [b,c,a])) [g,f]
       mkCoreApps (onDict (catOp k composeV [b,c,a])) [g,f]
     | otherwise = pprPanic "mkCompose mismatch:" (pprWithType g $$ pprWithType f)
   mkEx :: Cat -> Var -> Unop CoreExpr
   mkEx k ex z =
     -- -- For the class method aliases (exl, exr):
     -- pprTrace "mkEx" (pprWithType z) $
     -- pprTrace "mkEx" (pprWithType (Var ex)) $
     -- pprTrace "mkEx" (pprWithType (catOp k ex [a,b])) $
     -- pprTrace "mkEx" (pprWithType (onDict (catOp k ex [a,b]))) $
     -- pprTrace "mkEx" (pprWithType (onDict (catOp k ex [a,b]) `App` z)) $
     -- -- pprPanic "mkEx" (text "bailing")
     onDict (catOp k ex [a,b]) `App` z
    where
      (a,b)  = tyArgs2 (exprType z)
   mkFork :: Cat -> Binop CoreExpr
   -- mkFork k f g | pprTrace "mkFork" (sep [ppr k, ppr f, ppr g]) False = undefined
   mkFork k f g =
     -- (&&&) :: forall {k :: * -> * -> *} {a} {c} {d}.
     --          (ProductCat k, Ok k d, Ok k c, Ok k a)
     --       => k a c -> k a d -> k a (Prod k c d)
     -- onDict (catOp k forkV `mkTyApps` [a,c,d]) `mkCoreApps` [f,g]
     onDict (catOp k forkV [a,c,d]) `mkCoreApps` [f,g]
    where
      (a,c) = tyArgs2 (exprType f)
      (_,d) = tyArgs2 (exprType g)
   mkApplyMaybe :: Cat -> Type -> Type -> Maybe CoreExpr
   mkApplyMaybe k a b =
     -- apply :: forall {k :: * -> * -> *} {a} {b}. (ClosedCat k, Ok k b, Ok k a)
     --       => k (Prod k (Exp k a b) a) b
     -- onDict (catOp k applyV `mkTyApps` [a,b])
     onDictMaybe =<< catOpMaybe k applyV [a,b]
   isClosed :: Cat -> Bool
   isClosed k = isJust (mkApplyMaybe k unitTy unitTy)
   mkCurry :: Cat -> Unop CoreExpr
   -- mkCurry k e | dtrace "mkCurry" (ppr k <+> pprWithType e) False = undefined
   mkCurry k e =
     -- curry :: forall {k :: * -> * -> *} {a} {b} {c}.
     --          (ClosedCat k, Ok k c, Ok k b, Ok k a)
     --       => k (Prod k a b) c -> k a (Exp k b c)
     -- onDict (catOp k curryV `mkTyApps` [a,b,c]) `App` e
     -- dtrace "mkCurry: (a,b,c) ==" (ppr (a,b,c)) $
     onDict (catOp k curryV [a,b,c]) `App` e
    where
      (tyArgs2 -> (tyArgs2 -> (a,b),c)) = exprType e
      -- (splitAppTys -> (_,[splitAppTys -> (_,[a,b]),c])) = exprType e
   mkUncurryMaybe :: Cat -> ReExpr
   mkUncurryMaybe k e =
     -- uncurry :: forall {k :: * -> * -> *} {a} {b} {c}.
     --            (ClosedCat k, Ok k c, Ok k b, C1 (Ok k) a)
     --         => k a (Exp k b c) -> k (Prod k a b) c
     -- onDict (catOp k uncurryV `mkTyApps` [a,b,c]) `App` e
     (`App` e) <$> (onDictMaybe =<< catOpMaybe k uncurryV [a,b,c] )
    where
      (tyArgs2 -> (a, tyArgs2 -> (b,c))) = exprType e
   mkIfC :: Cat -> Type -> Ternop CoreExpr
   mkIfC k ty cond true false =
     mkCompose cat (catOp k ifV [ty])
       (mkFork cat cond (mkFork cat true false))
   mkBottomC :: Cat -> Type -> Type -> Maybe CoreExpr
   mkBottomC k dom cod = catOpMaybe k bottomCV [dom,cod]
   mkConst :: Cat -> Type -> ReExpr
   mkConst k dom e =
     -- const :: forall (k :: * -> * -> *) b. ConstCat k b => forall dom.
     --          Ok k dom => b -> k dom (ConstObj k b)
     -- (`App` e) <$> onDictMaybe (catOp k constV [exprType e, dom])
     (`App` e) <$> (onDictMaybe =<< catOpMaybe k constV [exprType e, dom])
     -- onDict (catOp k constV [exprType e] `App` Type dom) `App` e
   mkConstFun :: Cat -> Type -> ReExpr
   mkConstFun k dom e =
     -- constFun :: forall k p a b. (ClosedCat k, Oks k '[p, a, b])
     --          => k a b -> k p (Exp k a b)
     -- (`App` e) <$> onDictMaybe (catOp k constFunV [dom,a,b])
     (`App` e) <$> (onDictMaybe =<< catOpMaybe k constFunV [dom,a,b])
    where
      (a,b) = tyArgs2 (exprType e)
   -- Split k a b into a & b.
   -- TODO: check that k == cat
   -- Turn U into either const U or constFun (mkCcc U) if possible.
   mkConst' :: Cat -> Type -> ReExpr
   -- mkConst' k dom e | dtrace "mkConst'" (ppr (k,dom) <+> pprWithType e) False = undefined
   -- mkConst' k dom e = (mkConst k dom <+ (mkConstFun k dom . mkCcc)) e
   mkConst' k dom e | isFunTy (exprType e) = mkConstFun k dom (mkCcc e)
                    | otherwise            = mkConst k dom e
   -- TODO: refactor mkReprC and mkAbstC into one function that takes an Id. p
   mkAbstC :: Cat -> Type -> CoreExpr
   mkAbstC k ty =
     -- pprTrace "mkAbstC" (ppr ty) $
     -- pprTrace "mkAbstC" (pprWithType (Var abstCV)) $
     -- pprTrace "mkAbstC" (pprWithType (catOp k abstCV [ty])) $
     -- pprPanic "mkAbstC" (text "bailing")
     catOp k abstCV [ty]
   mkReprC :: Cat -> Type -> CoreExpr
   mkReprC k ty =
     -- pprTrace "mkReprC" (ppr ty) $
     -- pprTrace "mkReprC" (pprWithType (Var reprCV)) $
     -- pprTrace "mkReprC" (pprWithType (catOp k reprCV [ty])) $
     -- pprPanic "mkReprC" (text "bailing")
     catOp k reprCV [ty]
   mkReprC',mkAbstC' :: Cat -> Type -> CoreExpr
   mkReprC' k ty =
     fromMaybe (pprPanic "mkReprC' fail" (ppr (k,ty))) (mkReprC'_maybe k ty)
   mkAbstC' k ty =
     fromMaybe (pprPanic "mkAbstC' fail" (ppr (k,ty))) (mkAbstC'_maybe k ty)
   -- TODO: Combine mkReprC'_maybe and mkAbstC'_maybe for efficiency.
   -- TODO: Remove non-maybe versions, and drop "_maybe" from names.
   mkReprC'_maybe :: Cat -> Type -> Maybe CoreExpr
   mkReprC'_maybe k a =
     -- pprTrace "mkReprC 1" (ppr (a,r)) $
     -- pprTrace "mkReprC 2" (pprWithType (Var reprCV)) $
     -- pprTrace "mkReprC 3" (pprMbWithType (catOpMaybe k reprCV [a,r])) $
     catOpMaybe k reprCV [a,r]
    where
      (_co,r) = normaliseType famEnvs Nominal (repTy a)
   mkAbstC'_maybe :: Cat -> Type -> Maybe CoreExpr
   mkAbstC'_maybe k a =
     -- pprTrace "mkAbstC 1" (ppr (r,a)) $
     -- pprTrace "mkAbstC 2" (pprWithType (Var abstCV)) $
     -- pprTrace "mkAbstC 3" (pprMbWithType (catOpMaybe k abstCV [a,r])) $
     catOpMaybe k abstCV [a,r]
    where
      (_co,r) = normaliseType famEnvs Nominal (repTy a)
   mkCoerceC :: Cat -> Type -> Type -> CoreExpr
   mkCoerceC k dom cod
     | dom `eqType` cod = mkId k dom
     | otherwise = catOp k coerceV [dom,cod]
   tyArgs2_maybe :: Type -> Maybe (Type,Type)
   -- tyArgs2_maybe (splitAppTys -> (_,(a:b:_))) = Just (a,b)
   tyArgs2_maybe _ty@(splitAppTy_maybe -> Just (splitAppTy_maybe -> Just (_,a),b)) =
     -- dtrace "tyArgs2_maybe" (ppr _ty <+> text "-->" <+> (ppr (a,b))) $
     Just (a,b)
   tyArgs2_maybe _ = Nothing
   -- tyArgs2_maybe ty = do (t1,b) <- splitAppTy_maybe ty
   --                          (_ ,a) <- splitAppTy_maybe t1
   --                          return (a,b)
   tyArgs2 :: Type -> (Type,Type)
   tyArgs2 (tyArgs2_maybe -> Just ab) = ab
   tyArgs2 ty = pprPanic "tyArgs2" (ppr ty)
   -- traceRewrite :: (Outputable a, Outputable (f b)) => String -> Unop (a -> f b)
   -- traceRewrite str f a = pprTrans str a (f a)
   -- traceRewrite :: (Outputable a, Outputable (f b)) => String -> Unop (a -> f b)
   traceRewrite str f a = pprTrans str a <$> f a
   pprTrans :: (Outputable a, Outputable b) => String -> a -> b -> b
   pprTrans str a b = dtrace str (ppr a $$ "-->" $$ ppr b) b
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
          (lintExpr dflags (varSetElems (exprFreeVars after)) after)
   catFun :: ReExpr
   -- catFun e | dtrace "catFun" (pprWithType e) False = undefined
   catFun (Var v) | Just (op,tys) <- Map.lookup fullName monoOps =
     -- Apply to types and dictionaries, and possibly curry.
     -- dtrace "catFun: found" (ppr (op,tys)) $
     return $ (if twoArgs ty then mkCurry cat else id) (catOp cat op tys)
    where
      ty = varType v
      fullName = fqVarName v
      twoArgs (tyArgs2_maybe -> Just (_,tyArgs2_maybe -> Just _)) = True
      twoArgs _ = False
   catFun (collectTyArgs -> (Var v, tys))
     | True || dtrace "catFun poly" (text (fqVarName v) <+> dcolon <+> ppr (varType v)) True
     , Just op <- Map.lookup (fqVarName v) polyOps
     = dtrace "catFun poly" (ppr (v,tys,op) <+> text "-->" <+> ppr (onDictMaybe (catOp cat op tys))) $
       return ({- onDict -} (catOp cat op tys))
   -- TODO: handle Prelude.const. Or let it inline.
   catFun _ = Nothing
   transCatOp :: ReExpr
#if 0
   -- transCatOp e | dtrace "transCatOp" (ppr e) False = undefined
   transCatOp (collectArgs -> (Var v, Type _wasCat : rest))
     | True || dtrace "transCatOp v _wasCat rest" (text (fqVarName v) <+> ppr _wasCat <+> ppr rest) True
     , Just (catArgs,nonCatArgs) <- Map.lookup (fqVarName v) catOpArities
     -- , dtrace "transCatOp arities" (ppr (catArgs,nonCatArgs)) True
     , length (filter (not . isTyCoDictArg) rest) == catArgs + nonCatArgs
     -- , dtrace "transCatOp" (text "arity match") True
     = let -- Track how many regular (non-TyCo, non-pred) arguments we've seen
           addArg :: Maybe (Int,CoreExpr) -> CoreExpr -> Maybe (Int,CoreExpr)
           -- addArg a b | dtrace "transCatOp addArg" (ppr (a,b)) False = undefined
           addArg Nothing _ = -- dtrace "transCatOp Nothing" (text "bailing") $
                              Nothing
           addArg (Just (i,e)) arg
              | isTyCoArg arg
              = -- dtrace "addArg isTyCoArg" (ppr arg)
                Just (i,e `App` arg)
              | isPred arg
              = --- dtrace "addArg isPred" (ppr arg)
                -- onDictMaybe may fail (Nothing) in the target category.
                (i,) <$> onDictMaybe e  --  fails gracefully
                -- Just (i,onDict e)    -- succeed or die
              | otherwise
              = -- dtrace "addArg otherwise" (ppr (i,arg))
                -- TODO: logic to sort out cat vs non-cat args.
                -- We currently don't have both.
                Just (i+1,e `App` (if i < catArgs then mkCcc else id) arg)
       in
         snd <$> foldl addArg (Just (0,Var v `App` Type cat)) rest
   transCatOp _ = -- pprTrace "transCatOp" (text "fail") $
                  Nothing
#else
   transCatOp (collectArgs -> (Var v, Type (TyConApp (isFunTyCon -> True) []) : rest))
     -- | dtrace "transCatOp v rest" (text (fqVarName v) <+> ppr rest) False = undefined
     | okArgs
     = let -- Track how many regular (non-TyCo, non-pred) arguments we've seen
           addArg :: Maybe CoreExpr -> CoreExpr -> Maybe CoreExpr
           -- addArg a b | dtrace "transCatOp addArg" (ppr (a,b)) False = undefined
           addArg Nothing _ = -- dtrace "transCatOp Nothing" (text "bailing") $
                              Nothing
           addArg (Just e) arg
              | isTyCoArg arg
              = -- dtrace "addArg isTyCoArg" (ppr arg)
                Just (e `App` arg)
              | isPred arg
              = -- dtrace "addArg isPred" (ppr arg)
                -- onDictMaybe may fail (Nothing) in the target category.
                onDictMaybe e  --  fails gracefully
              | otherwise
              = -- dtrace "addArg otherwise" (ppr (i,arg))
                -- TODO: logic to sort out cat vs non-cat args.
                -- We currently don't have both.
                Just (e `App` (if isFunTy (exprType arg) then mkCcc else id) arg)
       in
         foldl addArg (Just (Var v `App` Type cat)) rest
      where
       mbArities = Map.lookup (fqVarName v) catOpArities
       okArgs | Nothing <- mbArities = True
              | Just (catArgs,nonCatArgs) <- mbArities
              = -- dtrace "transCatOp arities" (ppr (catArgs,nonCatArgs)) $
                length (filter (not . isTyCoDictArg) rest) == catArgs + nonCatArgs
   transCatOp _ = -- pprTrace "transCatOp" (text "fail") $
                   Nothing

#endif
   reCat :: ReExpr
   reCat = {- traceFail "reCat" <+ -} transCatOp <+ catFun
   traceFail :: String -> ReExpr
   traceFail str a = dtrace str (pprWithType a) Nothing
   -- TODO: refactor transCatOp & isPartialCatOp
   -- TODO: phase out hasRules, since I'm using annotations instead
   isPseudoApp :: CoreExpr -> Bool
   isPseudoApp (collectArgs -> (Var v,_)) = isPseudoFun v
   isPseudoApp _ = False
   isPseudoFun :: Id -> Bool
   isPseudoFun = not . null . pseudoAnns
    where
      pseudoAnns :: Id -> [PseudoFun]
      pseudoAnns = findAnns deserializeWithData annotations . NamedTarget . varName

substFriendly :: Bool -> CoreExpr -> Bool
-- substFriendly catClosed rhs
--   | pprTrace "substFriendly"
--     (ppr ((catClosed,rhs),not (liftedExpr rhs),incompleteCatOp rhs,isTrivial rhs,isFunTy (exprType rhs) && not catClosed))
--     False = undefined
substFriendly catClosed rhs =
     not (liftedExpr rhs)
  -- || substFriendlyTy (exprType rhs)
  || incompleteCatOp rhs
  || -- pprTrace "isTrivial" (ppr rhs <+> text "-->" <+> ppr (isTrivial rhs))
     (isTrivial rhs)
  || isFunTy (exprType rhs) && not catClosed
  -- || isVarTyCos rhs

isVarTyCos :: CoreExpr -> Bool
isVarTyCos (collectTyCoDictArgs -> (Var _,_)) = True
isVarTyCos _ = False

-- Adapted from exprIsTrivial in CoreUtils. This version considers dictionaries
-- trivial as well as application of exl/exr.
isTrivial :: CoreExpr -> Bool
-- isTrivial e | pprTrace "isTrivial" (ppr e) False = undefined
isTrivial (Var _) = True -- See Note [Variables are trivial]
isTrivial (Type _) = True
isTrivial (Coercion _) = True
isTrivial (Lit lit) = litIsTrivial lit
isTrivial (App (isTrivialCatOp -> True) arg) = isTrivial arg
isTrivial (App e arg) = isTyCoDictArg arg && isTrivial e
isTrivial (Tick _ e) = isTrivial e
isTrivial (Cast e _) = isTrivial e
isTrivial (Lam b body) = not (isRuntimeVar b) && isTrivial body
isTrivial (Case _ _ _ [(DEFAULT,[],rhs)]) = isTrivial rhs
isTrivial (Case e _ _ alts) = isTrivial e && all (isTrivial . altRhs) alts
isTrivial _ = False

incompleteCatOp :: CoreExpr -> Bool
#if 1
-- incompleteCatOp e | dtrace "incompleteCatOp" (ppr e) False = undefined
incompleteCatOp e@(collectArgs -> (Var _v, Type (TyConApp (isFunTyCon -> True) []) : _rest))
  = -- pprTrace "incompleteCatOp v rest" (text (fqVarName v) <+> ppr rest) $
    isFunTy (exprType e)
#else
-- incompleteCatOp e | dtrace "incompleteCatOp" (ppr e) False = undefined
incompleteCatOp (collectArgs -> (Var v, Type _wasCat : rest))
  | True || pprTrace "incompleteCatOp v _wasCat rest" (text (fqVarName v) <+> ppr _wasCat <+> ppr rest) True
  , Just (catArgs,_) <- Map.lookup (fqVarName v) catOpArities
  , let seen = length (filter (not . isTyCoDictArg) rest)
  -- , dtrace "incompleteCatOp catArgs" (ppr seen <+> text "vs" <+> ppr catArgs) True
  = seen < catArgs
#endif
incompleteCatOp _ = False

-- Whether to substitute based on type. Experimental. This version: substitute
-- if a function or has a subst-friendly type argument (e.g., pair components).
substFriendlyTy :: Type -> Bool
substFriendlyTy (coreView -> Just ty) = substFriendlyTy ty
substFriendlyTy (splitTyConApp_maybe -> Just (tc,tys)) = isFunTyCon tc || any substFriendlyTy tys
substFriendlyTy _ = False

catModule :: String
catModule = "ConCat.AltCat"

repModule :: String
repModule = "ConCat.Rep"

boxModule :: String
boxModule = "ConCat.Rebox"

extModule :: String
extModule =  "GHC.Exts"

isTrivialCatOp :: CoreExpr -> Bool
-- isTrivialCatOp = liftA2 (||) isSelection isAbstRepr
isTrivialCatOp (collectArgs -> (Var v,length -> n))
  -- | pprTrace "isTrivialCatOp" (ppr (v,n,isSelectorId v,isAbstReprId v)) True
  =    (isSelectorId v && n == 5)  -- exl cat tya tyb dict ok
    || (isAbstReprId v && n == 4)  -- reprCf cat a r repCat
isTrivialCatOp _ = False

isSelectorId :: Id -> Bool
isSelectorId v = fqVarName v `elem` (((catModule ++ ".") ++) <$> ["exl","exr"])

isAbstReprId :: Id -> Bool
isAbstReprId v = fqVarName v `elem` (((catModule ++ ".") ++) <$> ["reprC","abstC"])

-- TODO: refactor

#if 1

-- For each categorical operation, how many non-cat args (first) and how many cat args (last)
catOpArities :: Map String (Int,Int)
catOpArities = Map.fromList $ map (\ (nm,m,n) -> (catModule ++ '.' : nm, (m,n))) $
  [ ("id",0,0), (".",2,0)
  , ("exl",0,0), ("exr",0,0), ("&&&",2,0), ("***",2,0), ("dup",0,0), ("swapP",0,0)
  , ("first",1,0), ("second",1,0), ("lassocP",0,0), ("rassocP",0,0)
  , ("inl",0,0), ("inr",0,0), ("|||",2,0), ("+++",2,0), ("jam",0,0), ("swapS",0,0)
  , ("left",1,0), ("right",1,0), ("lassocS",0,0), ("rassocS",0,0)
  , ("apply",0,0), ("curry",1,0), ("uncurry",1,0)
  , ("distl",0,0), ("distr",0,0)
  , ("it",0,0) ,("unitArrow",0,1) ,("const",0,1)
  , ("notC",0,0), ("andC",0,0), ("orC",0,0), ("xorC",0,0)
  , ("negateC",0,0), ("addC",0,0), ("subC",0,0), ("mulC",0,0), ("powIC",0,0)
  , ("recipC",0,0), ("divideC",0,0)
  , ("expC",0,0), ("cosC",0,0), ("sinC",0,0)
  , ("fromIntegralC",0,0)
  , ("equal",0,0), ("notEqual",0,0)
  , ("lessThan",0,0), ("greaterThan",0,0), ("lessThanOrEqual",0,0), ("greaterThanOrEqual",0,0)
  , ("succC",0,0), ("predC",0,0)
  , ("bottomC",0,0)
  , ("ifC",0,0)
  , ("unknownC",0,0)
  , ("reprC",0,0), ("abstC",0,0)
  , ("reprCp",0,0), ("abstCp",0,0)
  , ("constFun",1,0)
  , ("ambC",0,0)  -- experiment. How to factor out?
  ]

-- TODO: also handle non-categorical arguments, as in unitArrow and const. Maybe
-- return a pair of arities to cover non-categorical and categorical arguments.
-- I could also handle these cases specially. Perhaps arity of -1 as a hack.

#endif

-- TODO: replace idV, composeV, etc with class objects from which I can extract
-- those variables. Better, module objects, since I sometimes want functions
-- that aren't methods.

-- TODO: consider a mkCoreApps variant that automatically inserts dictionaries.

pprWithType :: CoreExpr -> SDoc
pprWithType e = ppr e <+> dcolon <+> ppr (exprType e)

pprMbWithType :: Maybe CoreExpr -> SDoc
pprMbWithType = maybe (text "failed") pprWithType

cccRuleName :: FastString
cccRuleName = fsLit "ccc"

composeRuleName :: FastString
composeRuleName = fsLit "compose/coerce"

cccRules :: FamInstEnvs -> CccEnv -> ModGuts -> AnnEnv -> [CoreRule]
cccRules famEnvs env@(CccEnv {..}) guts annotations =
  [ BuiltinRule { ru_name  = cccRuleName
                , ru_fn    = varName cccV
                , ru_nargs = 4  -- including type args
                , ru_try   = \ dflags inScope _fn ->
                                \ case
                                  -- _args | pprTrace "ccc ru_try args" (ppr _args) False -> undefined
                                  _es@(Type k : Type _a : Type _b : arg : _) ->
                                    -- pprTrace "ccc: going in" (ppr es) $
                                    ccc env (ops dflags inScope k) k arg
                                  _args -> -- pprTrace "ccc ru_try mismatch args" (ppr _args) $
                                           Nothing
                }
#if 1
  , BuiltinRule { ru_name  = composeRuleName
                , ru_fn    = varName composeV
                , ru_nargs = 8  -- including type args and dicts
                , ru_try   = \ dflags inScope _fn ->
                                \ case
                                  [Type k, Type _b,Type _c, Type _a,_catDict,_ok,g,f] ->
                                       composeR env (ops dflags inScope k) g f
                                  _args -> -- pprTrace "compose/coerce ru_try args" (ppr _args) $
                                           Nothing
                }
#endif
  ]
  where
    ops = mkOps env guts annotations famEnvs

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
          hsc_env <- getHscEnv
          pkgFamEnv <- getPackageFamInstEnv
          env <- mkCccEnv opts
          -- Add the rule after existing ones, so that automatically generated
          -- specialized ccc rules are tried first.
          let addRule, delRule :: ModGuts -> CoreM ModGuts
              addRule guts =
                do allAnns <- liftIO (prepareAnnotations hsc_env (Just guts))
                   let famEnvs = (pkgFamEnv, mg_fam_inst_env guts)
                   return (on_mg_rules (++ cccRules famEnvs env guts allAnns) guts)
              delRule guts = return (on_mg_rules (filter (not . isOurRule)) guts)
              isOurRule r = isBuiltinRule r && ru_name r `elem` [cccRuleName,composeRuleName]
              -- isCCC r | is = pprTrace "delRule" (ppr cccRuleName) is
              --         | otherwise = is
              --  where
              --    is = isBuiltinRule r && ru_name r == cccRuleName
              (pre,post) = -- (todos,[])
                           -- ([],todos)
                           splitAt 5 todos  -- guess
                           -- (swap . (reverse *** reverse) . splitAt 1 . reverse) todos
              ours = [ CoreDoPluginPass "Ccc insert rule" addRule
                     , CoreDoSimplify 7 mode
                     , CoreDoPluginPass "Ccc remove rule" delRule
                     , CoreDoPluginPass "Flag remaining ccc calls" (flagCcc env)
                     ]
          -- pprTrace "ccc pre-install todos:" (ppr todos) (return ())
          -- pprTrace "ccc post-install todos:" (ppr (pre ++ ours ++ post)) (return ())
          return $ pre ++ ours ++ post
 where
   flagCcc :: CccEnv -> PluginPass
   flagCcc (CccEnv {..}) guts
     --  | pprTrace "ccc residuals:" (ppr (toList remaining)) False = undefined
     --  | pprTrace "ccc final:" (ppr (mg_binds guts)) False = undefined
     | Seq.null remaining = return guts
     | otherwise = -- pprPanic "ccc residuals:" (ppr (toList remaining))
                   pprTrace "ccc residuals:" (ppr (toList remaining)) $
                   return guts
    where
      remaining :: Seq CoreExpr
      remaining = collectQ cccArgs (mg_binds guts)
      cccArgs :: CoreExpr -> Seq CoreExpr
      -- unVarApps :: CoreExpr -> Maybe (Id,[Type],[CoreExpr])
      -- ccc :: forall k a b. (a -> b) -> k a b
      cccArgs c@(unVarApps -> Just (v,_tys,[_])) | v == cccV = Seq.singleton c
      cccArgs _                                              = mempty
      -- cccArgs = const mempty  -- for now
      collectQ :: (Data a, Monoid m) => (a -> m) -> GenericQ m
      collectQ f = everything mappend (mkQ mempty f)
   -- Extra simplifier pass
   mode = SimplMode { sm_names      = ["Ccc simplifier pass"]
                    , sm_phase      = Phase 1 -- ??
                    , sm_rules      = True  -- important
                    , sm_inline     = True -- False -- ??
                    , sm_eta_expand = False -- ??
                    , sm_case_case  = True 
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
         err = "ccc installation: couldn't find "
               ++ str ++ " in " ++ moduleNameString modu
      lookupTh mkOcc mk modu = lookupRdr (mkModuleName modu) mkOcc mk
      findId      = lookupTh mkVarOcc lookupId
      findTc      = lookupTh mkTcOcc  lookupTyCon
      -- findFloatTy = fmap mkTyConTy . findTc floatModule -- TODO: eliminate
      findCatId   = findId catModule
      findRepTc   = findTc repModule
      findRepId   = findId repModule
      findBoxId   = findId boxModule
      findExtTc   = findTc extModule
      findExtId   = findId extModule
  idV         <- findCatId "id"
  constV      <- findCatId "const"
  composeV    <- findCatId "."
  exlV        <- findCatId "exl"
  exrV        <- findCatId "exr"
  forkV       <- findCatId "&&&"
  applyV      <- findCatId "apply"
  curryV      <- findCatId "curry"
  uncurryV    <- findCatId "uncurry"
  ifV         <- findCatId "ifC"
  constFunV   <- findCatId "constFun"
  abstCV      <- findCatId "abstC"
  reprCV      <- findCatId "reprC"
  -- abstC'V     <- findCatId "abstCp"
  -- reprC'V     <- findCatId "reprCp"
  coerceV     <- findCatId "coerceC"
  bottomCV    <- findCatId "bottomC"
  cccV        <- findCatId "ccc"
  -- floatT      <- findFloatTy "Float"
  -- doubleT     <- findFloatTy "Double"
  -- reprV       <- findRepId "repr"
  -- abstV       <- findRepId "abst"
  -- hasRepTc    <- findRepTc "HasRep"
  repTc       <- findRepTc "Rep"
  -- hasRepMeth  <- hasRepMethodM tracing hasRepTc repTc idV
  prePostV    <- findId "ConCat.Misc" "~>"
  boxIV       <- findBoxId "boxI"
  boxFV       <- findBoxId "boxF"
  boxDV       <- findBoxId "boxD"
  boxIBV      <- findBoxId "boxIB"
  tagToEnumV  <- findId "GHC.Prim" "tagToEnum#"
  bottomV     <- findId "ConCat.Misc" "bottom"
  -- lazyV    <- findExtId "lazy"
  -- reboxV   <- findBoxId "rebox"
  -- coercibleTc <- findExtTc "Coercible"
  -- coerceV     <- findExtId "coerce"
  inlineV     <- findExtId "inline"
  let mkPolyOp :: (String,(String,String)) -> CoreM (String,Var)
      mkPolyOp (stdName,(cmod,cop)) =
        do cv <- findId cmod cop
           return (stdName, cv)
  polyOps <- Map.fromList <$> mapM mkPolyOp polyInfo
  let mkMonoOp :: (String,(String,String,[Type])) -> CoreM (String,(Var,[Type]))
      mkMonoOp (stdName,(cmod,cop,tyArgs)) =
        do cv <- findId cmod cop
           return (stdName, (cv,tyArgs))
  monoOps <- Map.fromList <$> mapM mkMonoOp monoInfo
  ruleBase <- eps_rule_base <$> (liftIO $ hscEPS hsc_env)
  -- pprTrace "ruleBase" (ppr ruleBase) (return ())
  let boxers = Map.fromList [(intTyCon,boxIV),(doubleTyCon,boxDV),(floatTyCon,boxFV)]
#if 0
  let idAt t = Var idV `App` Type t     -- varApps idV [t] []
      [hasRepDc] = tyConDataCons hasRepTc
      mkHasRep :: Binop CoreExpr
      mkHasRep repr abst = conApps hasRepDc [ty] [repr,abst]
       where
         FunTy ty _ = exprType repr
      -- co :: Rep t ~#R t, i.e., abst. repr comes first in the dictionary.
      hasRepFromAbstCo co = mkHasRep (caster (mkSymCo co)) (caster co)
      caster :: Coercion -> CoreExpr
      caster co@(pFst . coercionKind -> dom) =
        mkCast (idAt dom) (mkFunCo Representational (mkRepReflCo dom) co)
#endif
  -- _ <- findId "GHC.Num" "subtract" -- help the plugin find instances for Float and Double
  when (isBottomingId cccV) $
    pprPanic "isBottomingId cccV" empty
  return (CccEnv { .. })

#if 0
type HasRepMeth = DynFlags -> ModGuts -> InScopeEnv -> Type -> Maybe (Id -> CoreExpr)

hasRepMethodM :: Bool -> TyCon -> TyCon -> Id -> CoreM HasRepMeth
hasRepMethodM tracing hasRepTc _repTc _idV =
  do hscEnv <- getHscEnv
     _eps   <- liftIO (hscEPS hscEnv)
     return $ \ dflags guts inScope ty ->
       let dtrace str doc a | tracing   = pprTrace str doc a
                            | otherwise = a
#if 1
           newtypeDict :: Maybe CoreExpr
           newtypeDict = Nothing
#else
           repTy = mkTyConApp _repTc [ty]
           newtypeDict :: Maybe (CoreExpr,(Coercion,Type))
           newtypeDict =
             do (tc,tyArgs) <- splitTyConApp_maybe ty
                (tvs,newtyRhs,_coax) <- unwrapNewTyCon_maybe tc
                -- TODO: refactor to isolate the Maybe stuff.
                -- dtrace "newtypeDict. coax:" (ppr _coax) (return ())
                let ty'   = substTy (zipTvSubst tvs tyArgs) newtyRhs
                    [hasRepDc] = tyConDataCons hasRepTc
                    mkIdFun t = varApps idV [t] []
                    repNt = UnivCo (PluginProv "RepNT") Representational ty repTy
                    reflTo t = mkFunCo Representational (mkRepReflCo t)
                    mkMeth t co = mkCast (mkIdFun t) (reflTo t co)
                    -- repNtIs = mkUnbranchedAxInstCo Nominal _coax tyArgs
                    --             (mkNomReflCo <$> [ty])  -- tyArgs ?? repTy?
                    repNtIs = UnivCo (PluginProv "RepNtIs") Nominal repTy ty'
                    repr = mkMeth    ty          repNt
                    abst = mkMeth repTy (mkSymCo repNt)
                    dict = conApps hasRepDc [ty] [repr,abst]
                return (dict,(repNtIs,ty'))
#endif
           findDict :: Maybe CoreExpr
           findDict = eitherToMaybe $
                      buildDictionary hscEnv dflags guts inScope
                         (mkTyConApp hasRepTc [ty])
           mkMethApp dict =
             -- dtrace "hasRepMeth" (ppr ty <+> "-->" <+> ppr dict) $
             \ meth -> varApps meth [ty] [dict]
       in
          -- Real dictionary or synthesize
          mkMethApp <$> (findDict <|> newtypeDict)

#endif

-- TODO: perhaps consolidate poly & mono.

-- Polymorphic operations. Assoc list from the fully qualified standard Haskell
-- operation name to
-- * module name for categorical counterpart (always catModule now)
-- * categorical operation name
polyInfo :: [(String,(String,String))]
polyInfo = [(hmod++"."++hop,(catModule,cop)) | (hmod,ops) <- info, (hop,cop) <- ops]
 where
   -- Haskell module, Cat Haskell/Cat op names
   -- No cat args. In progress.
   info :: [(String,[(String,String)])]
   info = [ ("GHC.Base"  ,[tw "id"])
          , ("GHC.Tuple", [("(,)","pair"),("swap","swapP")])
          , ("Data.Tuple",[("fst","exl"),("snd","exr")])
          , ("Data.Either", [("Left","inl"),("Right","inr")])
          , ("ConCat.Category", [("arrayFun","array"),("arrAtFun","arrAt")])
          ]
   tw x = (x,x)

-- Variables that have associated ccc rewrite rules in AltCat. If we have
-- sufficient arity for the rule, including types, give it a chance to kick in.
cccRuledArities :: Map String Int
cccRuledArities = Map.fromList
  [("Data.Tuple.curry",4),("Data.Tuple.uncurry",4)]


-- Monomorphic operations. Given newtype-wrapped (Float,Double), yield an assoc
-- list from the fully qualified standard Haskell operation name to
-- * module name for categorical counterpart (always catModule now)
-- * categorical operation name
-- * type arguments to cat op
monoInfo :: [(String,(String,String,[Type]))]
monoInfo =
  [ (hop,(catModule,cop,tyArgs))
  | (cop,ps) <- info
  , (hop,tyArgs) <- ps
  ]
 where
   -- (cat-name, [(std-name,cat-type-args)]
   info :: [(String, [(String, [Type])])]
   info =
     [ ("notC",boolOp "not"), ("andC",boolOp "&&"), ("orC",boolOp "||")
     , ("equal", eqOp "==" <$> ifd) 
     , ("notEqual", eqOp "/=" <$> ifd) 
     , ("lessThan", compOps "lt" "<")
     , ("greaterThan", compOps "gt" ">")
     , ("lessThanOrEqual", compOps "le" "<=")
     , ("greaterThanOrEqual", compOps "ge" ">=")
#if 1
     , ("negateC",numOps "negate"), ("addC",numOps "+")
     , ("subC",numOps "-"), ("mulC",numOps "*")
#endif
       -- powIC

     , ("negateC",fdOps "negate"), ("addC",fdOps "plus")
     , ("subC",fdOps "minus"), ("mulC",fdOps "times")
     , ("recipC", fdOps "recip"), ("divideC", fdOps "divide")
     , ("expC", fdOps "exp")
     , ("cosC", fdOps "cos")
     , ("sinC", fdOps "sin")

     --
     , ("succC",[("GHC.Enum.$fEnumInt_$csucc",[intTy])])
     , ("predC",[("GHC.Enum.$fEnumInt_$cpred",[intTy])])
     ]
    where
      ifd = intTy : fd
      fd = [floatTy,doubleTy]
      boolOp op = [("GHC.Classes."++op,[])]
      -- eqOp ty = ("GHC.Classes.eq"++pp ty,[ty])
      eqOp op ty = ("GHC.Classes."++clsOp,[ty])
       where
         tyName = pp ty
         clsOp =
           case (op,ty) of
             ("==",_) -> "eq"++tyName
             ("/=",isIntTy -> True) -> "ne"++tyName
             _ -> "$fEq"++tyName++"_$c"++op
      compOps opI opFD = compOp <$> ifd
       where
         compOp ty = ("GHC.Classes."++clsOp,[ty])
          where
            clsOp | isIntTy ty = opI ++ tyName
                  | otherwise  = "$fOrd" ++ tyName ++ "_$c" ++ opFD
            tyName = pp ty
#if 1
      numOps op = numOp <$> ifd
       where
         numOp ty = (modu++".$fNum"++tyName++"_$c"++op,[ty])
          where
            tyName = pp ty
            modu | isIntTy ty = "GHC.Num"
                 | otherwise  = floatModule
#endif
      fdOps op = fdOp <$> fd
       where
         fdOp :: Type -> (String, [Type])
         fdOp ty = (floatModule++"."++op++pp ty,[ty]) -- GHC.Float.sinFloat

#if 0
-- An orphan instance to help me debug
instance Show Type where show = pp
#endif

floatModule :: String
floatModule = "GHC.Float"

--    fracOp op ty = ("GHC.Float.$fFractional"++pp ty++"_$c"++op,[ty])
--    floatingOp op ty = ("GHC.Float.$fFloating"++pp ty++"_$c"++op,[ty])

-- (==): eqInt, eqFloat, eqDouble
-- (/=): neInt, $fEqFloat_$c/=, $fEqDouble_$c/=
-- (<):  ltI, $fOrdFloat_$c<

pp :: Outputable a => a -> String
pp = showPpr unsafeGlobalDynFlags


{--------------------------------------------------------------------
    Misc
--------------------------------------------------------------------}

on_mg_rules :: Unop [CoreRule] -> Unop ModGuts
on_mg_rules f mg = mg { mg_rules = f (mg_rules mg) }

fqVarName :: Var -> String
fqVarName = qualifiedName . varName

uqVarName :: Var -> String
uqVarName = getOccString . varName

varModuleName :: Var -> Maybe String
varModuleName = nameModuleName_maybe . varName

-- With dot
nameModuleName_maybe :: Name -> Maybe String
nameModuleName_maybe =
  fmap (moduleNameString . moduleName) . nameModule_maybe

-- Keep consistent with stripName in Exp.
uniqVarName :: Var -> String
uniqVarName v = uqVarName v ++ "_" ++ show (varUnique v)

-- Adapted from HERMIT.GHC
-- | Get the fully qualified name from a 'Name'.
qualifiedName :: Name -> String
qualifiedName nm =
  maybe "" (++ ".") (nameModuleName_maybe nm) ++ getOccString nm

-- | Substitute new subexpressions for variables in an expression. Drop any dead
-- binders, which is handy as dead binders can appear with live binders of the
-- same variable.
subst :: [(Id,CoreExpr)] -> Unop CoreExpr
subst ps = substExpr "subst" (foldr add emptySubst ps')
 where
   add (v,new) sub = extendIdSubst sub v new
   ps' = filter (not . isDeadBinder . fst) ps

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

collectArgsPred :: (CoreExpr -> Bool) -> CoreExpr -> (CoreExpr,[CoreExpr])
collectArgsPred p = go []
 where
   go args (App fun arg) | p arg = go (arg:args) fun
   go args e                     = (e,args)

collectTyCoDictArgs :: CoreExpr -> (CoreExpr,[CoreExpr])
collectTyCoDictArgs = collectArgsPred isTyCoDictArg

collectNonTyCoDictArgs :: CoreExpr -> (CoreExpr,[CoreExpr])
collectNonTyCoDictArgs = collectArgsPred (not . isTyCoDictArg)

isTyCoDictArg :: CoreExpr -> Bool
isTyCoDictArg e = isTyCoArg e || isPredTy' (exprType e)

-- isConApp :: CoreExpr -> Bool
-- isConApp (collectArgs -> (Var (isDataConId_maybe -> Just _), _)) = True
-- isConApp _ = False

-- TODO: More efficient isConApp, discarding args early.

isPred :: CoreExpr -> Bool
isPred e  = not (isTyCoArg e) && isPredTy' (exprType e)

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
coercionTag FunCo       {} = "FunCo" -- pattern synonym
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
-- inlineId v | pprTrace ("inlineId " ++ fqVarName v) (ppr (realIdUnfolding v)) False = undefined
-- inlineId v | pprTrace ("inlineId " ++ uqVarName v) (ppr (maybeUnfoldingTemplate (realIdUnfolding v))) False = undefined
inlineId v = maybeUnfoldingTemplate (realIdUnfolding v)  -- idUnfolding

-- Adapted from Andrew Farmer's getUnfoldingsT in HERMIT.Dictionary.Inline:
inlineClassOp :: Id -> Maybe CoreExpr
inlineClassOp v =
  case idDetails v of
    ClassOpId cls -> mkDictSelRhs cls <$> elemIndex v (classAllSelIds cls)
    _             -> Nothing

exprHead :: CoreExpr -> Maybe Id
exprHead (Var v)     = Just v
exprHead (App fun _) = exprHead fun
exprHead (Cast e _)  = exprHead e
exprHead _           = Nothing

onExprHead :: (Id -> Maybe CoreExpr) -> ReExpr
onExprHead h = (fmap.fmap) simpleOptExpr $
               go id
 where
   go cont (Var v)       = cont <$> h v
   go cont (App fun arg) = go (cont . (`App` arg)) fun
   go cont (Cast e co)   = go (cont . (`Cast` co)) e
   go _ _                = Nothing

-- TODO: try go using Maybe fmap instead of continuation.

-- The simpleOptExpr here helped keep simplification going.
-- TODO: try without.

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

isFreeIn :: Var -> CoreExpr -> Bool
v `isFreeIn` e = v `elemVarSet` (exprFreeVars e)

isFreeIns :: Var -> [CoreExpr] -> Bool
v `isFreeIns` es = all (v `isFreeIn`) es

-- exprFreeVars :: CoreExpr -> VarSet
-- elemVarSet      :: Var -> VarSet -> Bool

pairTy :: Binop Type
pairTy a b = mkBoxedTupleTy [a,b]

etaReduce_maybe :: ReExpr
etaReduce_maybe (Lam x (App e (Var y))) | x == y && not (x `isFreeIn` e) = Just e
etaReduce_maybe _ = Nothing

-- TODO: phase out etaReduce1 and etaReduce1N in favor of etaReduce_maybe.
-- Then rename etaReduce_maybe to "etaReduce"
etaReduce1 :: Unop CoreExpr
etaReduce1 e = fromMaybe e (etaReduce_maybe e)

etaReduceN :: Unop CoreExpr
etaReduceN (Lam x (etaReduceN -> body')) = etaReduce1 (Lam x body')
etaReduceN e = e

-- The function category
funCat :: Cat
funCat = mkTyConTy funTyCon

liftedExpr :: CoreExpr -> Bool
liftedExpr e = not (isTyCoDictArg e) && liftedType (exprType e)

liftedType :: Type -> Bool
liftedType = isLiftedTypeKind . typeKind

pattern PairVar :: CoreExpr
pattern PairVar <- Var (isPairVar -> True)
                   -- Var PairVarName
                   -- Var (fqVarName -> "GHC.Tuple.(,)")

isPairVar :: Var -> Bool
isPairVar = (== "GHC.Tuple.(,)") . fqVarName

isMonoTy :: Type -> Bool
isMonoTy (TyConApp _ tys)      = all isMonoTy tys
isMonoTy (AppTy u v)           = isMonoTy u && isMonoTy v
isMonoTy (ForAllTy (Anon u) v) = isMonoTy u && isMonoTy v
isMonoTy _                     = False

-- | Number of occurrences of a given Id in an expression
idOccs :: Id -> CoreExpr -> Int
idOccs x = go
 where
   -- go e | pprTrace "idOccs go" (ppr e) False = undefined
   go (Lit _)                  = 0
   go (Type _)                 = 0
   go (Coercion _)             = 0
   go (Var y)      | y == x    = -- pprTrace "idOccs found" (ppr y) $
                                 1
                   | otherwise = 0
   go (App u v)                = go u + go v
   go (Tick _ e)               = go e
   go (Cast e _)               = go e
   go (Lam y body) | y == x    = 0
                   | otherwise = go body
   go (Let bind body)          = goBind bind + go body
   go (Case e _ _ alts)        = go e + sum (goAlt <$> alts)
   goBind (NonRec y rhs) = goB (y,rhs)
   goBind (Rec ps)       = sum (goB <$> ps)
   goB (y,rhs) | y == x    = 0
               | otherwise = go rhs
   -- goAlt alt | pprTrace "idOccs goAlt" (ppr alt) False = undefined
   goAlt (_,ys,rhs) | x `elem` ys = 0
                    | otherwise   = go rhs

-- GHC's isPredTy says "no" to unboxed tuples of pred types.
isPredTy' :: Type -> Bool
-- isPredTy' ty | pprTrace "isPredTy'" (ppr (ty,splitTyConApp_maybe ty)) False = undefined
isPredTy' ty = isPredTy ty || others ty
 where
   others (splitTyConApp_maybe -> Just (tc,tys)) =
     -- pprTrace "isPredTy' tyCon arity" (ppr (tyConArity tc)) $
     -- The first half of the arguments are representation types ('PtrRepLifted)
     isUnboxedTupleTyCon tc && all isPredTy' (drop (length tys `div` 2) tys)
   others _ = False

#if 0

isUnboxedTupleType :: Type -> Bool
isUnboxedTupleType ty = case tyConAppTyCon_maybe ty of
                           Just tc -> isUnboxedTupleTyCon tc
                           _       -> False

splitTyConApp_maybe :: Type -> Maybe (TyCon, [Type])

#endif

starKind :: Kind
starKind = mkTyConTy starKindTyCon

castE :: Coercion -> CoreExpr
castE co = Lam x (mkCast (Var x) co)
 where
   x = freshId emptyVarSet "w" dom
   Pair dom _ = coercionKind co

pprCoWithType :: Coercion -> SDoc
pprCoWithType co = ppr co <+> dcolon $$ ppr (coercionType co)

#if 0
-- | Converts a coercion to be nominal, if possible.
-- See Note [Role twiddling functions]
setNominalRole_maybe' :: Coercion -> Maybe Coercion
setNominalRole_maybe' co | pprTrace ("setNominalRole_maybe "++coercionTag co) (ppr (coercionRole co) <+> pprCoWithType co) False = undefined
setNominalRole_maybe' co
  | Nominal <- coercionRole co = Just co
setNominalRole_maybe' (SubCo co)  = Just co
setNominalRole_maybe' (Refl _ ty) = Just $ Refl Nominal ty
setNominalRole_maybe' (TyConAppCo Representational tc cs)
  = do { cos' <- mapM setNominalRole_maybe' cs
       ; return $ TyConAppCo Nominal tc cos' }
setNominalRole_maybe' (SymCo co)
  = SymCo <$> setNominalRole_maybe' co
setNominalRole_maybe' (TransCo co1 co2)
  = TransCo <$> setNominalRole_maybe' co1 <*> setNominalRole_maybe' co2
setNominalRole_maybe' (AppCo co1 co2)
  = AppCo <$> setNominalRole_maybe' co1 <*> pure co2
setNominalRole_maybe' (ForAllCo tv kind_co co)
  = ForAllCo tv kind_co <$> setNominalRole_maybe' co
setNominalRole_maybe' (NthCo n co)
  = NthCo n <$> setNominalRole_maybe' co
setNominalRole_maybe' (InstCo co arg)
  = InstCo <$> setNominalRole_maybe' co <*> pure arg
setNominalRole_maybe' (CoherenceCo co1 co2)
  = CoherenceCo <$> setNominalRole_maybe' co1 <*> pure co2
setNominalRole_maybe' (UnivCo prov _ co1 co2)
  | case prov of UnsafeCoerceProv -> True   -- it's always unsafe
                 PhantomProv _    -> False  -- should always be phantom
                 ProofIrrelProv _ -> True   -- it's always safe
                 PluginProv _     -> False  -- who knows? This choice is conservative.
                 HoleProv _       -> False  -- no no no.
  = Just $ UnivCo prov Nominal co1 co2
setNominalRole_maybe' _ = Nothing
#endif

-- Exists somewhere?
eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe = either (const Nothing) Just

altRhs :: Alt b -> Expr b
altRhs (_,_,rhs) = rhs

isCast :: Expr b -> Bool
isCast (Cast {}) = True
isCast _         = False

-- | Monadic variation on everywhere (bottom-up)
-- everywhereM :: Monad m => GenericM m -> GenericM m
-- everywhereM f = f <=< gmapM (everywhereM2 f)

-- | Monadic variation on everywhere' (top-down)
everywhereM' :: Monad m => GenericM m -> GenericM m
everywhereM' f = gmapM (everywhereM' f) <=< f
