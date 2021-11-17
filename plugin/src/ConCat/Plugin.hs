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
import Data.Either (isRight)
import Data.Maybe (isNothing,isJust,fromMaybe,catMaybes,listToMaybe)
import Data.List (isPrefixOf,isSuffixOf,elemIndex,sort,stripPrefix)
import Data.Char (toLower)
import Data.Data (Data)
import Data.Generics (GenericQ,GenericM,gmapM,mkQ,mkT,mkM,everything,everywhere',everywhereM)
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
--import qualified Data.Set (Set) as OrdSet
import qualified Data.Set as OrdSet
--import qualified Data.Map (Map) as OrdMap
import qualified Data.Map as OrdMap
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
import qualified UniqDFM as DFMap
#endif
import Text.Printf (printf)
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef

import GhcPlugins as GHC hiding (substTy,cat)
import Class (classAllSelIds)
import CoreArity (etaExpand)
import CoreLint (lintExpr)
import DynamicLoading
import MkId (mkDictSelRhs,coerceId)
import Pair (Pair(..))
import PrelNames (leftDataConName,rightDataConName
                 ,floatTyConKey,doubleTyConKey,integerTyConKey
                 ,intTyConKey,boolTyConKey)
import Type (coreView)
import TcType (isFloatTy,isDoubleTy,isIntegerTy,isIntTy,isBoolTy,isUnitTy
              ,tcSplitTyConApp_maybe)
import TysPrim (intPrimTyCon)
import FamInstEnv (normaliseType)
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
import CoreOpt (simpleOptExpr)
#endif
import TyCoRep
import GHC.Classes
import Unique (mkBuiltinUnique)
-- For normaliseType etc
import FamInstEnv

import ConCat.Misc (Unop,Binop,Ternop,PseudoFun(..),(~>))
import ConCat.BuildDictionary
-- import ConCat.Simplify

-- GHC 8.10 FunTy as an extra operand
#if MIN_VERSION_GLASGOW_HASKELL(8,10,0,0)
pattern FunTy' a r <-
  FunTy _ a r

mkFunTy' :: Type -> Type -> Type
mkFunTy' a b = FunTy VisArg a b
#else
pattern FunTy' a r = FunTy a r

mkFunTy' :: Type -> Type -> Type
mkFunTy' a b = FunTy a b
#endif

-- Information needed for reification. We construct this info in
-- CoreM and use it in the ccc rule, which must be pure.
data CccEnv = CccEnv { dtrace           :: forall a. String -> SDoc -> a -> a
                     , cccV             :: Id
                     , cccPV            :: Id -- evidence-annotated version, toCcc''
                     , uncccV           :: Id
                     , closedTc         :: TyCon
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
                     , fmapV            :: Id
                     , fmapT1V          :: Id
                     , fmapT2V          :: Id
                     , casePairTopTV    :: Id
                     , casePairTV       :: Id
                     , casePairLTV      :: Id
                     , casePairRTV      :: Id
                     , flipForkTV       :: Id
                     , castConstTV      :: Id
                     , reprCV           :: Id
                     , abstCV           :: Id
                     , coerceV          :: Id
                     , bottomTV         :: Id
                     , repTc            :: TyCon
                  -- , hasRepMeth       :: HasRepMeth
                     -- , hasRepFromAbstCo :: Coercion   -> CoreExpr
                     , prePostV         :: Id
                  -- , lazyV            :: Id
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
                     , boxers           :: DFMap.UniqDFM {- TyCo-} Id  -- to remove
#else
                     , boxers           :: OrdMap.Map TyCon Id
#endif
                     , tagToEnumV       :: Id
                     , bottomV          :: Id
                     , boxIBV           :: Id
                     , ifEqIntHash      :: Id
                  -- , reboxV           :: Id
                     , inlineV          :: Id
                     , uniqSupply       :: UniqSupply
                  -- , coercibleTc      :: TyCon
                  -- , coerceV          :: Id
                  -- , polyOps          :: PolyOpsMap
                  -- , monoOps          :: MonoOpsMap
                     , hsc_env          :: HscEnv
                     , ruleBase         :: RuleBase  -- to remove
                     , okTypeTc         :: TyCon
                     , enablePolymorphism :: Bool -- experimental
                     }

-- Whether to run Core Lint after every step
lintSteps :: Bool
lintSteps = True -- False

type Rewrite a = a -> Maybe a
type ReExpr = Rewrite CoreExpr
type ReExpr2 = CoreExpr -> Rewrite CoreExpr

trying :: (String -> SDoc -> Bool -> Bool) -> String -> a -> Bool
trying tr str a = tr ("Trying " ++ str) (a `seq` empty) False
{-# NOINLINE trying #-}

-- #define Trying(str) e_ | trying dtrace (str) e_ -> undefined
#define Trying(str)

#define Doing(str) dtrace "Doing" (text (str)) id $
-- #define Doing(str) pprTrace "Doing" (text (str)) id $
-- #define Doing(str)

-- Category
type Cat = Type

ccc :: CccEnv -> Ops -> Type -> ReExpr
-- ccc _ _ _ _ _ | pprTrace "ccc" empty False = undefined
ccc (CccEnv {..}) (Ops {..}) cat =
  traceRewrite "toCcc''" $
  (if lintSteps then lintReExpr else id) $
  go
 where
   go :: ReExpr
   go = \ case
     -- Temporarily make `ccc` bail on polymorphic terms. Doing so will speed up
     -- my experiments, since much time is spent optimizing rules, IIUC. It'll
     -- be important to restore polymorphic transformation later for useful
     -- separate compilation. Put first, to remove tracing clutter
     -- Trying("top poly bail")
     (isMono -> False) | not enablePolymorphism ->
       -- Doing("top poly bail")
       Nothing
     e | dtrace ("go ccc "++pp cat++":") (pprWithType' e) False -> undefined
     -- Sanity check: ccc should only take functions.
     e@(exprType -> isFunTy -> False) ->
       pprPanic "ccc/go: not of function type" (pprWithType e)
#if 0
     -- An alternative to curry. Play with this one later.
     Trying("top flipForkT")
     -- f | pprTrace "flipForkT tests"
     --      (ppr ( splitFunTy (exprType f)
     --              , second splitFunTy_maybe (splitFunTy (exprType f))
     --              , not catClosed)) False = undefined
     f | z `FunTy` (a `FunTy` b) <- exprType f
       , not catClosed
       -> Doing("top flipForkT")
          -- pprTrace "flipForkT type" (ppr (varType flipForkTV)) $
          return (onDicts (varApps flipForkTV [cat,z,a,b] []) `App` f)
#endif
     Trying("top Lam")
     Lam x body -> goLam x body
     Trying("top Let")
     Let bind@(NonRec v rhs) body ->
       -- Experiment: always float.
       if alwaysSubst rhs then
         -- Experiment:
         Doing("top Let subst")
         go (subst1 v rhs body)
         -- return (mkCcc (subst1 v rhs body))
       else if
          -- dtrace "top Let tests" (ppr (not catClosed, substFriendly catClosed rhs, idOccs False v body)) $
          not (isMonoTy (varType v)) ||
          not catClosed ||  -- experiment
          substFriendly catClosed rhs || idOccs False v body <= 1 then
         Doing("top Let float")
         return (Let bind (mkCcc body))
       else
         Doing("top Let to beta-redex")
         go (App (Lam v body) rhs)
     Trying("top reCat")
     (reCat -> Just e') ->
       Doing("top reCat")
       Just e'
     Trying("top Avoid pseudo-app")
     (isPseudoApp -> True) ->
       Doing("top Avoid pseudo-app")
       Nothing
  Trying("top Case of bottom")
     e@(Case (collectArgs -> (Var v,_args)) _wild _rhsTy _alts)
       |  v == bottomV
       ,  FunTy' dom cod <- exprType e
       -> Doing("top Case of bottom")
          mkBottomC cat dom cod
     Trying("top Case live wild")
     (deadifyCaseWild -> Just e') ->
       Doing("top Case live wild")
       go e'
     -- See journal 2018-02-02.
     Trying("top Case of product")
     Case scrut _ _rhsTy [(DataAlt dc, [b,c], rhs)]
         | isBoxedTupleTyCon (dataConTyCon dc) ->
       Doing("top Case of product")
       return $ mkCcc $
         varApps casePairTopTV
           [varType b,varType c,_rhsTy]
           [scrut, mkLams [b,c] rhs]
     -- ccc-of-case. Maybe restrict to isTyCoDictArg for all bound variables, but
     -- perhaps I don't need to.
     Trying("top Case unfold")
     -- Case scrut@(unfoldMaybe -> Nothing) _wild _rhsTy _alts
     --   | pprTrace "top Case failed to unfold scrutinee" (ppr scrut) False -> undefined
     Case scrut wild rhsTy alts
       | Just scrut' <- unfoldMaybe scrut
       -> Doing("top Case unfold")  --  of dictionary
          return $ mkCcc (Case scrut' wild rhsTy alts)
          -- TODO: also for lam?
     Trying("top nominal Cast")
     Cast e co@( -- dtrace "top nominal cast co" (pprCoWithType co {-<+> (ppr (setNominalRole_maybe co))-}) id
                setNominalRole_maybe' -> Just (reCatCo -> Just co')) ->
       -- etaExpand turns cast lambdas into themselves
       Doing("top nominal cast")
       let co'' = downgradeRole (coercionRole co) (coercionRole co') co' in
         -- pprTrace "top nominal Cast" (ppr co $$ text "-->" $$ ppr co'') $
         return (Cast (mkCcc e) co'')
       -- I think GHC is undoing this transformation, so continue eagerly
       -- (`Cast` co') <$> go e
     Trying("top const cast")
     Cast (Lam v e) (FunCo _r _ co'@(coercionKind -> Pair b b'))
       | not (v `isFreeIn` e)
       -- , dtrace "top const cast" (ppr (varWithType castConstTV)) True
       , Just mk <- onDictMaybe <=< onDictMaybe $
                      varApps castConstTV [cat,varType v,b,b'] []
       -> Doing("top const cast")
          return (mk `App` mkCoercible starKind b b' co' `App` e)
     Trying("top representational cast")
     -- This version fails gracefully when we can't make the coercions.
     -- Then we can see further into the error.
     e@(Cast e' (coercionRole -> Representational))
       | FunTy' a  b  <- exprType e
       , FunTy' a' b' <- exprType e'
       , Just coA    <- mkCoerceC_maybe cat a a'
       , Just coB    <- mkCoerceC_maybe cat b' b
       ->
          Doing("top representational cast")
          -- Will I get unnecessary coerceCs due to nominal-able sub-coercions?
          return $ mkCompose cat coB $ mkCompose cat (mkCcc e') $ coA
     Trying("top cast unfold")
     Cast (unfoldMaybe -> Just body') co ->
       Doing("top cast unfoldMaybe")
       return $ mkCcc $ mkCast body' co
     Trying("top con abstRepr")
     -- Constructor application
     e@(collectArgs -> (Var (isDataConId_maybe -> Just dc),_))
       | let (binds,body) = collectBinders (etaExpand (dataConRepArity dc) e)
             bodyTy = exprType body
       -- , dtrace "top con abstRepr abst type" (ppr bodyTy) True
       , Just repr <- mkReprC'_maybe funCat bodyTy
       , Just abst <- mkAbstC'_maybe funCat bodyTy
       -> Doing("top con abstRepr")
          return $ mkCcc $
           mkLams binds $
            abst `App` (inlineE repr `App` body)
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
       -- dtrace "top App tests" (ppr (exprType v,liftedExpr v, mkConst' cat dom v,mkUncurryMaybe cat (mkCcc u))) False -> undefined
       | catClosed, liftedExpr v
       , Just v' <- mkConst' cat dom v
       -- , dtrace "top App  --> " (pprWithType v') True
       , Just uncU' <- mkUncurryMaybe cat (mkCcc u)
       -- , dtrace "top App uncU'" (pprWithType uncU') True
       -> Doing("top App")
          -- u v == uncurry u . (constFun v &&& id)
          -- dtrace "mkFork cat v' (mkId cat dom) -->" (ppr (mkFork cat v' (mkId cat dom))) $
          -- dtrace "mkCompose cat uncU' (mkFork cat v' (mkId cat dom)) -->" (ppr (mkCompose cat uncU' (mkFork cat v' (mkId cat dom)))) $
          -- dtrace "top App result" (ppr (mkCompose cat uncU' (mkFork cat v' (mkId cat dom)))) $
          return (mkCompose cat uncU' (mkFork cat v' (mkId cat dom)))
      where
        Just (dom,_) = splitFunTy_maybe (exprType e)
     Tick t e -> Doing("top tick")
                 return $ Tick t (mkCcc e)
     _e -> Doing("top Unhandled")
           -- pprTrace "ccc go. Unhandled" (ppr _e) $ Nothing
           -- pprPanic "ccc go. Unhandled" (ppr _e)
           Nothing
   -- go _ = Nothing
   -- goLam x body | dtrace "goLam:" (ppr (Lam x body)) False = undefined
   -- goLam x body | dtrace ("goLam body constr: " ++ exprConstr body) (ppr (Lam x body)) False = undefined
    where
      catClosed = isClosed cat
   goLam' x body =
     dtrace ("goLam "++pp x++" "++pp cat++":") (pprWithType body) $
     goLam x body
#if 0
   goLam x body
     | Just e' <- etaReduce_maybe (Lam x body) =
    Doing("lam eta-reduce")
    return (mkCcc e')
#endif
   goLam x body = case body of
     Trying("lam Id")
     Var y | x == y -> Doing("lam Id")
                       return (mkId cat xty)
     Trying("lam Poly const")
     _ | not enablePolymorphism, isConst, not (isFunTy bty), not (isMonoTy bty)
       -> Doing("lam Poly const bail")
          -- dtrace("lam Poly const: bty, isFunTy, isMonoTy") (ppr (bty, isFunTy bty, isMonoTy bty)) $
          Nothing
     Trying("lam bottom") -- must come before "lam Const" and "lam App"
     -- TODO: translate to bottomC in Rebox or AltCat.
     -- Maybe I don't need anything here.
     -- toCcc (\ x -> bottom @ t) --> bottomC
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
       -- let (Var _v, _) = collectArgs body in -- TEMP
       --   pprTrace ("lam Avoid pseudo-app " ++ uqVarName _v) empty $
         Doing("lam Avoid pseudo-app")
         Nothing

     Trying("lam Pair")
     (collectArgs -> (PairVar,(Type a : Type b : rest))) ->
       --  | dtrace "Pair" (ppr rest) False -> undefined
       case rest of
         []    -> -- (,) == curry id
                  -- Do we still need this case, or is it handled by catFun?
                  Doing("lam Plain (,)")
                  -- return (mkCurry cat (mkId cat (pairTy a b)))
                  mkCurry' cat (mkId cat (pairTy a b))
         [_]   -> Doing("lam Pair eta-expand")
                  goLam' x (etaExpand 1 body)
         [u,v] -> Doing("lam Pair")
                  -- dtrace "Pair test" (pprWithType u <> comma <+> pprWithType v) $
                  return (mkFork cat (mkCcc (Lam x u)) (mkCcc (Lam x v)))
         _     -> pprPanic "goLam Pair: too many arguments: " (ppr rest)
     -- Revisit.
     Trying("lam con abstRepr")
     -- Constructor applied to ty/co/dict arguments
     e@(collectNonTyCoDictArgs ->
        (collectTyCoDictArgs -> (Var (isDataConId_maybe -> Just dc),_), args))
       | let (binds,body') = collectBinders (etaExpand (dataConRepArity dc - length args) e)
             bodyTy = exprType body'
       , Just repr <- mkReprC'_maybe funCat bodyTy
       , Just abst <- mkAbstC'_maybe funCat bodyTy
       -> Doing("lam con abstRepr")
          return $ mkCcc $ Lam x $
            mkLams binds $ abst `App` (inlineE repr `App` body')
     -- (\ x -> let y = f x in g y) --> g . f
     -- (\ x -> let y = RHS in BODY) --> (\ y -> BODY) . (\ x -> RHS)
     --    if x not free in B
     Trying("lam Let compose")
     Let (NonRec y rhs) body'
       | not (x `isFreeIn` body')
       , Just comp <- mkCompose' cat (mkCcc (Lam y body')) (mkCcc (Lam x rhs))
       -> Doing("lam Let compose")
          return comp
     Trying("lam Let")
     -- TODO: refactor with top Let
     _e@(Let bind@(NonRec v rhs) body') ->
       -- dtrace "lam Let subst criteria" (ppr (substFriendly catClosed rhs, not xInRhs, idOccs True v body')) $
       if not catClosed || -- experiment
          substFriendly catClosed rhs || not xInRhs || idOccs True v body' <= 1 then
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
           goLam' x (subst1 v rhs body')
           -- Yet another choice is to lambda-lift the binding over x and then
           -- float the let past the x binding.
         else
           Doing("lam Let float")
           return (Let bind (mkCcc (Lam x body')))
       else
         Doing("lam Let to beta-redex")
         goLam' x (App (Lam v body') rhs)
      where
        xInRhs = x `isFreeIn` rhs
     -- Trying("lam letrec")
     -- _e@(Let bind@(Rec [(v,rhs)]) body') ->
     --    Doing("lam letrec")
     --    undefined
     Trying("lam inner eta-reduce")
     (etaReduce_maybe -> Just e') ->
       Doing("lam inner eta-reduce")
       goLam' x e'
     Trying("lam Lam")
     Lam y e ->
       -- (\ x -> \ y -> U) --> curry (\ z -> U[fst z/x, snd z/y])
       Doing("lam Lam")
       -- dtrace "Lam isDeads" (ppr (isDeadBinder x, isDeadBinder y)) $
       -- dtrace "Lam sub" (ppr sub) $
       -- TODO: maybe let instead of subst
       -- Substitute rather than making a Let, to prevent infinite regress.
       -- return $ mkCurry cat (mkCcc (Lam z (subst sub e)))
       -- Fail gracefully when we can't mkCurry, giving inlining a chance to
       -- resolve polymorphism to monomorphism. See 2017-10-18 notes.
       (if isNothing mbe' then dtrace "lam Lam fail" empty id else id) $
       mbe'
      where
        yty = varType y
        z = freshId (exprFreeVars e) zName (pairTy xty yty)
        zName = uqVarName x ++ "_" ++ uqVarName y
        sub = [(x,mkEx funCat exlV (Var z)),(y,mkEx funCat exrV (Var z))]
        -- TODO: consider using fst & snd instead of exl and exr here
        mbe' = mkCurry' cat (mkCcc (Lam z (subst sub e)))
     Trying("lam boxer")
     (boxCon -> Just e') ->
       Doing("lam boxer")
       return (mkCcc (Lam x e'))
     Trying("lam Case of boxer")
     e@(Case scrut wild _ty [(_dc,[unboxedV],rhs)])
       | Just (tc,[]) <- splitTyConApp_maybe (varType wild)
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
       , Just boxV <- flip DFMap.lookupUDFM tc boxers
#else
       , Just boxV <- OrdMap.lookup         tc boxers
#endif
       -> Doing("lam Case of boxer")
          -- dtrace "boxV" (ppr boxV) $
          let wild' = setIdOccInfo wild compatNoOccInfo
              tweak :: Unop CoreExpr
              tweak (Var v) | v == unboxedV =
                pprPanic ("lam Case of boxer: bare unboxed var") (ppr e)
              tweak (App (Var f) (Var v)) | f == boxV, v == unboxedV = Var wild'
              tweak e' = e'
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
              compatNoOccInfo = noOccInfo
#else
              compatNoOccInfo = NoOccInfo
#endif
          in
            -- Note top-down (everywhere') instead of bottom-up (everywhere)
            -- so that we can find 'boxI v' before v.
            return (mkCcc (Lam x (Let (NonRec wild' scrut) (everywhere' (mkT tweak) rhs))))
     Trying("lam Case hoist")
     Case scrut wild ty [(dc,vs,rhs)]
       | not (x `isFreeIn` scrut)
       -> Doing("lam Case hoist")
          return $
           mkCcc (Case scrut wild (mkFunTy' xty ty) [(dc,vs, Lam x rhs)])
          -- pprPanic ("lam Case hoist") empty
     Trying("lam Case to let")
     Case scrut v@(isDeadBinder -> False) _rhsTy [(_, bs, rhs)]
       | isEmptyVarSet (mkVarSet bs `intersectVarSet` exprFreeVars rhs) ->
       Doing("lam Case to let")
       return (mkCcc (Lam x (Let (NonRec v scrut) rhs)))
     Trying("lam Case live wild")
     (deadifyCaseWild -> Just e') ->
       Doing("lam Case live wild")
       goLam' x e'
     Trying("lam Case default")
     Case _scrut _ _rhsTy [(DEFAULT,[],rhs)] ->
       Doing("lam case-default")
       return (mkCcc (Lam x rhs))
     Trying("lam Case nullary")
     Case _scrut _ _rhsTy [(_, [], rhs)] ->
       Doing("lam Case nullary")
       return (mkCcc (Lam x rhs))
       -- TODO: abstract return (mkCcc (Lam x ...))
     Trying("lam Case of Bool")
     Case scrut _ rhsTy [(DataAlt false, [], rhsF),(DataAlt true, [], rhsT)]
         | false == falseDataCon && true == trueDataCon ->
       -- To start, require v to be unused. Later, extend.
       -- if not (isDeadBinder wild) && wild `isFreeIns` [rhsF,rhsT] then
       --      pprPanic "lam Case of Bool: live wild var (not yet handled)" (ppr e)
       -- else
          Doing("lam Case of Bool")
          return $
            mkIfC cat rhsTy (mkCcc (Lam x scrut))
              (mkCcc (Lam x rhsT)) (mkCcc (Lam x rhsF))
     Trying("lam Case of product")
     Case scrut _ _rhsTy [(DataAlt dc, [a,b], rhs)]
         | isBoxedTupleTyCon (dataConTyCon dc) ->
       Doing("lam Case of product")
       if --  | not (isDeadBinder wild) ->  -- About to remove
          --     pprPanic "lam Case of product live wild binder" (ppr e)
          | not (b `isFreeIn` rhs) ->
              return $ mkCcc $ -- inlineE $  -- already inlines early
                varApps casePairLTV
                  [xty,varType a,varType b,_rhsTy]
                  [Lam x scrut, mkLams [x,a] rhs]
          | not (a `isFreeIn` rhs) ->
              return $ mkCcc $ -- inlineE $  -- already inlines early
                varApps casePairRTV
                  [xty,varType a, varType b,_rhsTy]
                  [Lam x scrut, mkLams [x,b] rhs]
          -- TODO: do the L & R optimizations help?
          | otherwise ->
              return $ mkCcc $ inlineE $  -- wasn't inlining early
                varApps casePairTV
                  [xty,varType a,varType b,_rhsTy]
                  [Lam x scrut, mkLams [x,a,b] rhs]

     -- Trying("lam Case cast")
     -- Case (Cast scrut (setNominalRole_maybe -> Just co')) v altsTy alts
     --   -> Doing("lam Case cast")
     --           Trying("lam Case cast")
     Trying("lam Case unfold")
     Case scrut v altsTy alts
       --  | pprTrace "lam Case unfold" (ppr (scrut,unfoldMaybe' scrut)) False -> undefined
       | Just scrut' <- unfoldMaybe' scrut
       -> Doing("lam Case unfold")
          return $ mkCcc $ Lam x $
           Case scrut' v altsTy alts
     -- Does unfolding suffice as an alternative? Not quite, since lambda-bound
     -- variables can appear as scrutinees. Maybe we could eliminate that
     -- possibility with another transformation.
     -- 2016-01-04: I moved lam case abstRepr after unfold
     -- Do I also need top case abstRepr?
     Trying("lam case abstRepr")
     Case scrut v@(varType -> vty) altsTy alts
       | Just repr <- mkReprC'_maybe funCat vty
       , Just abst <- mkAbstC'_maybe funCat vty
       -> Doing("lam case abstRepr")
          return $ mkCcc $ Lam x $
           Case (inlineE abst `App` (repr `App` scrut)) v altsTy alts
     Trying("lam nominal Cast")
     Cast body' co@(setNominalRole_maybe' -> Just co') ->
       -- etaExpand turns cast lambdas into themselves
       Doing("lam nominal cast")
       let r  = coercionRole co
           r' = coercionRole co'         -- always Nominal, isn't it?
           co'' = downgradeRole r r' co' -- same as co?
       in
         -- pprTrace "lam nominal Cast" (ppr co $$ text "-->" $$ ppr co'') $
         return (mkCcc (Cast (Lam x body') (FunCo r (mkReflCo r xty) co'')))
     Trying("lam representational cast")
     e@(Cast e' _) ->
       Doing("lam representational cast")
       -- Will I get unnecessary coerceCs due to nominal-able sub-coercions?
       -- TODO: convert to mkCoerceC also. Then eliminate mkCoerceC, and
       -- rename mkCoerceC.
       return $ mkCompose cat (mkCoerceC cat (exprType e') (exprType e)) $
                mkCcc (Lam x e')
     Trying("lam fmap unfold")
     e@(collectArgs -> (Var v, Type (isFunCat -> False) : _))
        | v == fmapV
        , Just body' <- unfoldMaybe e
        -> Doing("lam fmap unfold")
           -- dtrace "lam fmap unfold" (ppr body') $
           return (mkCcc (Lam x body'))

     Trying("lam fmap 1")
     _e@(collectArgs -> (Var v, [Type _ {-(isFunTy -> True)-},Type h,Type b,Type c,_dict,_ok,f])) | v == fmapV ->
        Doing("lam fmap 1")
        -- pprTrace "lam fmap body" (ppr _e) $
        -- pprTrace "lam fmap pieces" (ppr (h,xty,b,c,f)) $
        -- -- (\ x -> fmap F BS)  -->  fmapTrans' (\ x -> F)
        -- pprTrace "fmapT1" (ppr (varWithType fmapT1V)) $
        let e' = onDicts (varApps fmapT1V [h,xty,b,c] []) `mkCoreApps` [Lam x f] in
          -- pprTrace "fmap constructed expression" (ppr e') $
          -- pprPanic "lam fmap bailing" empty
          return (mkCcc e')

     Trying("lam App compose")
     -- (\ x -> U V) --> U . (\ x -> V) if x not free in U
     u `App` v | liftedExpr v
               , not (x `isFreeIn` u)
               , okType (exprType v)
               -> case mkCompose' cat (mkCcc u) (mkCcc (Lam x v)) of
                    Nothing ->
                      Doing("lam App compose bail")
                      Nothing
                    Just e' ->
                      Doing("lam App compose")
                      return e'

     Trying("lam fmap 2")
     -- This rule goes after lam App compose, so we know that the fmap'd
     -- function depends on x, and the extra complexity is warranted.
     -- HM. It's *not* after lam App compose.
     _e@(collectArgs -> (Var v, [Type _ {-(isFunTy -> True)-},Type h,Type b,Type c,_dict,_ok,f,bs])) | v == fmapV ->
        Doing("lam fmap 2")
        -- pprTrace "lam fmap body" (ppr _e) $
        -- pprTrace "lam fmap pieces" (ppr (h,xty,b,c,f,bs)) $
        -- -- (\ x -> fmap F BS)  -->  fmapTrans' (\ x -> F) (\ x -> BS)
        -- pprTrace "fmapT2" (ppr (varWithType fmapT2V)) $
        let e' = onDicts (varApps fmapT2V [h,xty,b,c] []) `mkCoreApps` [Lam x f, Lam x bs] in
          -- pprTrace "fmap constructed expression" (ppr e') $
          -- pprPanic "lam fmap bailing" empty
          return (mkCcc e')

     Trying("lam App")
     -- (\ x -> U V) --> apply . (\ x -> U) &&& (\ x -> V)
     u `App` v --  | pprTrace "lam App" (ppr (u,v)) False -> undefined
               | catClosed, liftedExpr v, okType (exprType v)
               -- , pprTrace "lam App mkApplyMaybe -->" (ppr (mkApplyMaybe cat vty bty, cat)) True
               , mbComp <- do app  <- mkApplyMaybe cat vty bty
                              fork <- mkFork' cat (mkCcc (Lam x u)) (mkCcc (Lam x v))
                              mkCompose' cat app fork
               -> case mbComp of
                    Nothing ->
                      Doing("lam App bail")
                      Nothing
                    Just e' ->
                      Doing("lam App")
                      return e'
      where
        vty = exprType v
     Trying("lam unfold")
     e'| Just body' <- unfoldMaybe e'
       -> Doing("lam unfold")
          -- dtrace "lam unfold" (ppr body $$ text "-->" $$ ppr body') $
          return (mkCcc (Lam x body'))
          -- goLam' x body'
          -- TODO: factor out Lam x (mkCcc ...)
     Tick t e -> Doing("lam tick")
                 return $ Tick t (mkCcc (Lam x e))
     -- Give up
     _e -> -- pprPanic "ccc" ("lam Unhandled" <+> ppr (Lam x _e))
           -- pprTrace "goLam" ("Unhandled" <+> ppr _e) $
           Nothing
    where
      xty = varType x
      bty = exprType body
      isConst = not (x `isFreeIn` body)
      catClosed = isClosed cat

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
composeR :: CccEnv -> Ops -> ReExpr2
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
 -- , unfoldOkay     :: CoreExpr -> Bool
 , unfoldMaybe'   :: ReExpr
 , unfoldMaybe    :: ReExpr
 , inlineMaybe    :: Id -> Maybe CoreExpr
 , noDictErr      :: forall a. SDoc -> Either SDoc a -> a
 , onDictTry      :: CoreExpr -> Either SDoc CoreExpr
 , onDictMaybe    :: ReExpr
 , onDict         :: Unop CoreExpr
 , onDicts        :: Unop CoreExpr
 , buildDictMaybe :: Type -> Either SDoc CoreExpr
 , catOp          :: Cat -> Var -> [Type] -> CoreExpr
 , catOpMaybe     :: Cat -> Var -> [Type] -> Maybe CoreExpr
 , mkCcc          :: Unop CoreExpr  -- Any reason to parametrize over Cat?
 , mkId           :: Cat -> Type -> CoreExpr
 , mkCompose      :: Cat -> Binop CoreExpr
 , mkCompose'     :: Cat -> ReExpr2  -- experiment
 , mkEx           :: Cat -> Var -> Unop CoreExpr
 , mkFork         :: Cat -> Binop CoreExpr
 , mkFork'        :: Cat -> ReExpr2 -- experiment
 , mkApplyMaybe   :: Cat -> Type -> Type -> Maybe CoreExpr
 , isClosed       :: Cat -> Bool
 , mkCurry        :: Cat -> Unop CoreExpr
 , mkCurry'       :: Cat -> ReExpr
 , mkUncurryMaybe :: Cat -> ReExpr
 , mkIfC          :: Cat -> Type -> Ternop CoreExpr
 , mkBottomC      :: Cat -> Type -> Type -> Maybe CoreExpr
 , mkConst        :: Cat -> Type -> ReExpr
 , mkConst'       :: Cat -> Type -> ReExpr
 , mkConstFun     :: Cat -> Type -> ReExpr
 , mkAbstC        :: Cat -> Type -> CoreExpr
 , mkReprC        :: Cat -> Type -> CoreExpr
 , mkReprC'       :: Cat -> Type -> CoreExpr
 , mkAbstC'       :: Cat -> Type -> CoreExpr
 , mkReprC'_maybe :: Cat -> Type -> Maybe CoreExpr
 , mkAbstC'_maybe :: Cat -> Type -> Maybe CoreExpr
 , mkCoerceC      :: Cat -> Type -> Type -> CoreExpr
 , mkCoerceC_maybe :: Cat -> Type -> Type -> Maybe CoreExpr
 , traceRewrite   :: forall f a b. (Functor f, Outputable a, Outputable b) => String -> Unop (a -> f b)
 , tyArgs2_maybe  :: Type -> Maybe (Type,Type)
 , tyArgs2        :: Type -> (Type,Type)
 , pprTrans       :: forall a b. (Outputable a, Outputable b) => String -> a -> b -> b
 , lintReExpr     :: Unop ReExpr
 -- , catFun         :: ReExpr
 , transCatOp     :: ReExpr
 , reCat          :: ReExpr
 , isPseudoApp    :: CoreExpr -> Bool
 , normType       :: Role -> Type -> (Coercion, Type)
 , okType         :: Type -> Bool
 }

mkOps :: CccEnv -> ModGuts -> AnnEnv -> FamInstEnvs
      -> DynFlags -> InScopeEnv -> Type -> CoreExpr -> Type -> Ops
mkOps (CccEnv {..}) guts annotations famEnvs dflags inScope evTy ev cat = Ops {..}
 where
   okType t = isRight (buildDictMaybe (mkTyConApp okTypeTc [t]))
   -- okType _ = True
   inlineE :: Unop CoreExpr
   inlineE e = varApps inlineV [exprType e] [e]  -- move outward
   -- Replace boxing constructors by their boxing function synonyms (boxI etc)
   boxCon :: ReExpr
   boxCon e0 | tweaked   = -- dtrace "boxCon" (ppr (e0,e1)) $
                           Just e1
             | otherwise = Nothing
    where
      (Any tweaked,e1) = everywhereM (mkM tweak) e0
      success = (Any True,)
      tweak :: CoreExpr -> (Any,CoreExpr)
      tweak e@(App (Var con) e')
        | isDataConWorkId con
        , Just (tc,[]) <- splitTyConApp_maybe (exprType e)
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
        , Just  boxV <- flip DFMap.lookupUDFM  tc boxers
#else
        , Just  boxV <- OrdMap.lookup          tc boxers
#endif
        = success $ Var boxV `App` e'
      tweak ((Var v `App` Type ty) `App` e')
        | v == tagToEnumV && ty `eqType` boolTy
        = success $ Var boxIBV `App` e'
      -- Int equality turns into matching, which takes some care.
      tweak (Case scrut v rhsTy ((DEFAULT, [], d) : (mapM litAlt -> Just las)))
       | notNull las
       , hasTyCon intPrimTyCon vty
       = Doing("lam Case of Int#")
         -- TODO: let-bind scrut or use live binder
         success $ mkCoreLet (NonRec scrutV scrut) $ foldr mkIf d las
        where
         vty = varType v
         scrutV = zapIdOccInfo v
         scrut' = Var scrutV
         mkIf (lit,rhs) e = varApps ifEqIntHash [rhsTy] [scrut',Lit lit,rhs,e]
      tweak e = (Any False, e)
      litAlt (LitAlt lit,[],rhs) = Just (lit,rhs)
      litAlt _ = Nothing
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
#if MIN_VERSION_GLASGOW_HASKELL(8,8,0,0)
             (GRefl r _k mrefl,a),b)) =
     -- dtrace "reCatCo app" (ppr (r,_k,a,b)) $
     Just (mkAppCos (mkGReflCo r cat mrefl) [a,b])
#else
             (Refl r _k,a),b)) =
     -- dtrace "reCatCo app" (ppr (r,_k,a,b)) $
     Just (mkAppCos (mkReflCo r cat) [a,b])
#endif
   reCatCo (co1 `TransCo` co2) = TransCo <$> reCatCo co1 <*> reCatCo co2
   reCatCo co = pprTrace "ccc reCatCo: unhandled coercion" (ppr co) $
                Nothing
   -- Interpret a representational cast
   -- TODO: Try swapping argument order
   repTy :: Unop Type
   repTy t = mkTyConApp repTc [t]
   -- coercibleTy :: Unop Type
   -- coercibleTy t = mkTyConApp coercibleTc [t]
   -- Temp hack: avoid exl/exr and reprC/abstC.
   unfoldMaybe' :: ReExpr
   -- unfoldMaybe' e | pprTrace "unfoldMaybe'" (ppr (e,exprHead e)) False = undefined
   unfoldMaybe' e@(exprHead -> Just v)
     | not (isSelectorId v || isAbstReprId v) = unfoldMaybe e
   unfoldMaybe' _ = Nothing
   unfoldMaybe :: ReExpr
   -- unfoldMaybe e | dtrace "unfoldMaybe" (ppr (e,collectArgsPred isTyCoDictArg e)) False = undefined
   unfoldMaybe e --  | unfoldOkay e
                 --  | (Var v, _) <- collectArgsPred isTyCoDictArg e
                 -- -- , dtrace "unfoldMaybe" (text (fqVarName v)) True
                 -- , isNothing (catFun (Var v))
                 --  | True  -- experiment: don't restrict unfolding
                 = onExprHead dflags ({- traceRewrite "inlineMaybe" -} inlineMaybe) e
                 --  | otherwise = Nothing
   -- unfoldMaybe = -- traceRewrite "unfoldMaybe" $
   --               onExprHead ({-traceRewrite "inlineMaybe"-} inlineMaybe)
   inlineMaybe :: Id -> Maybe CoreExpr
   -- inlineMaybe v | dtrace ("inlineMaybe " ++ fqVarName v) (ppr ()) False = undefined
   -- inlineMaybe v | dtrace "inlineMaybe" (ppr v) False = undefined
   inlineMaybe v = (inlineId <+ -- onInlineFail <+ traceRewrite "inlineClassOp"
                                inlineClassOp) v
   -- onInlineFail :: Id -> Maybe CoreExpr
   -- onInlineFail v =
   --   pprTrace "onInlineFail idDetails" (ppr v <+> colon <+> ppr (idDetails v))
   --   Nothing
   noDictErr :: SDoc -> Either SDoc a -> a
   noDictErr doc =
     either (\ msg -> pprPanic "ccc - couldn't build dictionary for" (doc GHC.<> colon $$ msg)) id
   onDictTry :: CoreExpr -> Either SDoc CoreExpr
   onDictTry e | Just (ty,_) <- splitFunTy_maybe (exprType e)
               , isPredTy' ty = App e <$> buildDictMaybe ty
               | otherwise = return e
                             -- pprPanic "ccc / onDictTy: not a function from pred" (pprWithType e)
   onDictMaybe :: ReExpr
   -- TODO: refactor onDictMaybe
   onDictMaybe e = case onDictTry e of
                     Left  msg  -> dtrace "Couldn't build dictionary for"
                                     (pprWithType e GHC.<> colon $$ msg) $
                                   Nothing
                     Right dict -> Just dict
   onDict :: Unop CoreExpr
   onDict f = -- trace "onDict" $
              noDictErr (pprWithType f) (onDictTry f)
   -- Yet another variant: keep applying to dictionaries as long as we have
   -- a predicate type. TODO: reassess and refactor these variants.
   onDicts :: Unop CoreExpr
   onDicts e | Just (ty,_) <- splitFunTy_maybe (exprType e)
             , isPredTy' ty = onDicts (onDict e)
             | otherwise    = e
   buildDictMaybe :: Type -> Either SDoc CoreExpr
   buildDictMaybe ty = unsafePerformIO $
                       buildDictionary hsc_env dflags guts uniqSupply inScope evTy ev ty
   catOp :: Cat -> Var -> [Type] -> CoreExpr
   -- catOp k op tys | dtrace "catOp" (ppr (k,op,tys)) False = undefined
   catOp k op tys --  | dtrace "catOp" (pprWithType (Var op `mkTyApps` (k : tys))) True
                  = onDicts (Var op `mkTyApps` (k : tys))
   -- TODO: refactor catOp and catOpMaybe when the dust settles
   -- catOp :: Cat -> Var -> CoreExpr
   -- catOp k op = catOp k op []
   catOpMaybe :: Cat -> Var -> [Type] -> Maybe CoreExpr
   catOpMaybe k op tys = onDictMaybe (Var op `mkTyApps` (k : tys))
   mkCcc' :: Unop CoreExpr  -- Any reason to parametrize over Cat?
   mkCcc' e = varApps cccPV [cat,a,b,evTy] [ev,e]
    where
      (a,b) = fromMaybe (pprPanic "mkCcc non-function:" (pprWithType e)) $
              splitFunTy_maybe (exprType e)
   mkCcc :: Unop CoreExpr  -- Any reason to parametrize over Cat?
   mkCcc e = -- dtrace "mkCcc" (ppr (cat, e)) $
             mkCcc' e
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

   -- Experiment
   mkCompose' :: Cat -> ReExpr2
   -- (.) :: forall b c a. (b -> c) -> (a -> b) -> a -> c
   mkCompose' k g f
     | Just (b,c ) <- tyArgs2_maybe (exprType g)
     , Just (a,b') <- tyArgs2_maybe (exprType f)
     , b `eqType` b'
     = -- flip mkCoreApps [g,f] <$> onDictMaybe (catOp k composeV [b,c,a])
       -- (flip mkCoreApps [g,f] . onDict) <$> catOpMaybe k composeV [b,c,a]
       flip mkCoreApps [g,f] <$> (onDictMaybe =<< catOpMaybe k composeV [b,c,a])
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
   mkFork' :: Cat -> ReExpr2
   -- mkFork k f g | pprTrace "mkFork" (sep [ppr k, ppr f, ppr g]) False = undefined
   mkFork' k f g =
     -- (&&&) :: forall {k :: * -> * -> *} {a} {c} {d}.
     --          (ProductCat k, Ok k d, Ok k c, Ok k a)
     --       => k a c -> k a d -> k a (Prod k c d)
     -- return $ onDict (catOp k forkV [a,c,d]) `mkCoreApps` [f,g]
     flip mkCoreApps [f,g] <$> (onDictMaybe =<< catOpMaybe k forkV [a,c,d])
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
   -- isClosed k = isJust (mkApplyMaybe k unitTy unitTy)
   isClosed k = isRight (buildDictMaybe (TyConApp closedTc [k]))
   normType = normaliseType famEnvs

   mkCurry' :: Cat -> ReExpr
   -- mkCurry' k e | dtrace "mkCurry'" (ppr k <+> pprWithType e) False = undefined
   mkCurry' k e =
     -- curry :: forall {k :: * -> * -> *} {a} {b} {c}.
     --          (ClosedCat k, Ok k c, Ok k b, Ok k a)
     --       => k (Prod k a b) c -> k a (Exp k b c)
     -- onDict (catOp k curryV `mkTyApps` [a,b,c]) `App` e
     -- dtrace "mkCurry: (a,b,c) ==" (ppr (a,b,c)) $
     (`App` e) <$> (onDictMaybe =<< catOpMaybe k curryV [a,b,c])
    where
      (tyArgs2 -> (tyArgs2 -> (a,b),c)) = exprType e
      -- (splitAppTys -> (_,[splitAppTys -> (_,[a,b]),c])) = exprType e

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
   mkBottomC k dom cod =
     -- dtrace "mkBottomC bottomTV" (pprWithType (Var bottomTV)) $
     onDicts <$> catOpMaybe k bottomTV [dom,cod]
   mkConst :: Cat -> Type -> ReExpr
   -- mkConst k dom e | dtrace "mkConst1" (ppr (k,dom,e)) False = undefined
   -- mkConst k dom e | dtrace "mkConst2" (ppr ((`App` e) <$> (onDictMaybe =<< catOpMaybe k constV [exprType e, dom]))) False = undefined
   mkConst k dom e =
     -- const :: forall (k :: * -> * -> *) b. ConstCat k b => forall dom.
     --          Ok k dom => b -> k dom (ConstObj k b)
     -- (`App` e) <$> onDictMaybe (catOp k constV [exprType e, dom])
     (`App` e) <$> (onDictMaybe =<< catOpMaybe k constV [exprType e, dom])
     -- onDict (catOp k constV [exprType e] `App` Type dom) `App` e
   mkConstFun :: Cat -> Type -> ReExpr
   -- mkConstFun k dom e | dtrace "mkConstFun" (ppr (k,dom,e)) False = undefined
   mkConstFun k dom e =
     -- constFun :: forall k p a b. (ClosedCat k, Oks k '[p, a, b])
     --          => k a b -> k p (Exp k a b)
     -- (`App` e) <$> onDictMaybe (catOp k constFunV [dom,a,b])
     -- constFun isn't inlining on its own, so push it.
     (`App` e) <$> (onDictMaybe . inlineE =<< catOpMaybe k constFunV [dom,a,b])
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
      (_co,r) = normType Nominal (repTy a)
   mkAbstC'_maybe :: Cat -> Type -> Maybe CoreExpr
   mkAbstC'_maybe k a =
     -- pprTrace "mkAbstC 1" (ppr (r,a)) $
     -- pprTrace "mkAbstC 2" (pprWithType (Var abstCV)) $
     -- pprTrace "mkAbstC 3" (pprMbWithType (catOpMaybe k abstCV [a,r])) $
     catOpMaybe k abstCV [a,r]
    where
      (_co,r) = normType Nominal (repTy a)
   mkCoerceC :: Cat -> Type -> Type -> CoreExpr
   mkCoerceC k dom cod
     | dom `eqType` cod = mkId k dom
     | otherwise = catOp k coerceV [dom,cod]
   mkCoerceC_maybe :: Cat -> Type -> Type -> Maybe CoreExpr
   mkCoerceC_maybe k dom cod
     | dom `eqType` cod = return $ mkId k dom
     | otherwise = catOpMaybe k coerceV [dom,cod]
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
        let before' = mkCcc' before
            oops str doc = pprPanic ("ccc post-transfo check. " ++ str)
                             (doc $$ ppr before' $$ "-->" $$ ppr after)
            beforeTy = exprType before'
            afterTy  = exprType after
        maybe (if beforeTy `eqType` afterTy then
                 return after
               else
                 oops "type change"
                  (ppr beforeTy <+> "vs" $$ ppr afterTy <+> "in"))
              (oops "Lint")
          (lintExpr dflags (uniqSetToList (exprFreeVars after)) after)
   transCatOp :: ReExpr
   transCatOp orig@(collectArgs -> (Var v, Type (isFunCat -> True) : rest))
     | isFunCat cat = Just orig
     -- Take care with const, so we don't transform it alone.
     -- TODO: look for a more general suitable test for wrong number of arguments.
     --  | pprTrace "transCatOp" (ppr (WithType (Var v),WithType <$> rest,length rest, orig)) False = undefined
     | v == constV && length rest /= 5 = Nothing
     | varModuleName v == Just catModule
     , uqVarName v `elem`
         ["forkF","crossF","joinF","plusF","joinPF","plusPF"]
     , length rest /= 6 = Nothing
     | otherwise
     = -- dtrace "transCatOp v rest" (text (fqVarName v) <+> ppr rest) $
       let -- Track how many regular (non-TyCo, non-pred) arguments we've seen
           addArg :: Maybe CoreExpr -> CoreExpr -> Maybe CoreExpr
           -- addArg a b | -- dtrace "transCatOp addArg" (ppr (a,b)) False = undefined
           addArg Nothing _ = -- dtrace "transCatOp Nothing" (text "bailing") $
                              Nothing
           addArg (Just e) arg
             | isTyCoArg arg
             = -- dtrace "addArg isTyCoArg" (ppr arg) $
               Just (e `App` arg)
             | isPred arg
             = -- dtrace "addArg isPred" (ppr arg) $
               -- onDictMaybe may fail (Nothing) in the target category.
               onDictMaybe e  --  fails gracefully
             | FunTy' dom _ <- exprType e
             = -- dtrace "addArg otherwise" (ppr arg) $
               -- TODO: logic to sort out cat vs non-cat args.
               -- We currently don't have both.
               Just (e `App` (if isCatTy dom then mkCcc else id) arg)
               -- Just (e `App` (if isFunTy (exprType arg) then mkCcc else id) arg)
             | otherwise
             = -- dtrace "addArg: not a function type" (ppr (exprType e)) $
               Nothing
           final = foldl addArg (Just (Var v `App` Type cat)) rest
       in
         -- Make sure we have no remaining cat arguments
         -- dtrace "transCatOp final" (ppr final) $
         case final of
           Just e' | -- dtrace "hasCatArg" (ppr (hasCatArg e')) $
                     not (hasCatArg e') -> Just e'
           _                            -> Nothing
   transCatOp _ = -- dtrace "transCatOp" (text "fail") $
                  Nothing

   isCatTy :: Type -> Bool
   isCatTy (splitAppTy_maybe -> Just (splitAppTy_maybe -> Just (k,_),_)) =
     k `eqType` cat
   isCatTy _ = False
   hasCatArg :: CoreExpr -> Bool
   hasCatArg (exprType -> FunTy' t _) = isCatTy t
   hasCatArg _                       = False
   reCat :: ReExpr
   reCat = -- (traceFail "reCat" <+ ) $
           -- 2017-10-17: disable catFun to see if everything still works
           transCatOp -- <+ catFun
   traceFail :: String -> ReExpr
   traceFail str a = dtrace str (pprWithType a) Nothing
   -- TODO: refactor transCatOp & isPartialCatOp
   -- TODO: phase out hasRules, since I'm using annotations instead
   isPseudoApp :: CoreExpr -> Bool
   isPseudoApp (collectArgs -> (Var v,args)) =
     case isPseudoFun v of
       Just n -> n == length (filter (not . isTyCoDictArg) args)
       Nothing -> False
   isPseudoApp _ = False
   isPseudoFun :: Id -> Maybe Int
   isPseudoFun = fmap pseudoArgs . listToMaybe . pseudoAnns
    where
      pseudoAnns :: Id -> [PseudoFun]
      pseudoAnns = findAnns deserializeWithData annotations . NamedTarget . varName

substFriendly :: Bool -> CoreExpr -> Bool
-- substFriendly catClosed rhs
 --  | pprTrace "substFriendly"
 --    (ppr ((catClosed,rhs),not (liftedExpr rhs),incompleteCatOp rhs,isTrivial rhs,isFunTy ty && not catClosed,isIntegerTy ty))
 --    False = undefined
 -- where
 --   ty = exprType rhs
substFriendly catClosed rhs =
     not (liftedExpr rhs)
  --  || substFriendlyTy (exprType rhs)
  || incompleteCatOp rhs
  || -- pprTrace "isTrivial" (ppr rhs <+> text "-->" <+> ppr (isTrivial rhs))
     (isTrivial rhs)
  || isFunTy ty && not catClosed
  || isIntegerTy ty -- TODO: replace with something more general
  --  || isVarTyCos rhs
 where
   ty = exprType rhs

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
-- incompleteCatOp e | dtrace "incompleteCatOp" (ppr e) False = undefined
incompleteCatOp e@(collectArgs -> (Var _v, Type (TyConApp (isFunTyCon -> True) []) : _rest))
  = -- pprTrace "incompleteCatOp v rest" (text (fqVarName v) <+> ppr rest) $
    isFunTy (exprType e)
incompleteCatOp _ = False

-- Whether to substitute based on type. Experimental. This version: substitute
-- if a function or has a subst-friendly type argument (e.g., pair components).
substFriendlyTy :: Type -> Bool
substFriendlyTy (coreView -> Just ty) = substFriendlyTy ty
substFriendlyTy (splitTyConApp_maybe -> Just (tc,tys)) = isFunTyCon tc || any substFriendlyTy tys
substFriendlyTy _ = False

catModule :: String
catModule = "ConCat.AltCat"

trnModule :: String
trnModule = "ConCat.Translators"

repModule :: String
repModule = "ConCat.Rep"

boxModule :: String
boxModule = "ConCat.Rebox"

okTypeModule :: String
okTypeModule = "ConCat.OkType"

extModule :: String
extModule =  "GHC.Exts"

isTrivialCatOp :: CoreExpr -> Bool
-- isTrivialCatOp = liftA2 (||) isSelection isAbstRepr
isTrivialCatOp (collectArgs -> (Var v,length -> n))
  --  | pprTrace "isTrivialCatOp" (ppr (v,n,isSelectorId v,isAbstReprId v)) True
  =    (isSelectorId v && n == 5)  -- exl cat tya tyb dict ok
    || (isAbstReprId v && n == 4)  -- reprCf cat a r repCat
isTrivialCatOp _ = False

isSelectorId :: Id -> Bool
isSelectorId v = fqVarName v `elem` (((catModule ++ ".") ++) <$> ["exl","exr"])

isAbstReprId :: Id -> Bool
isAbstReprId v = fqVarName v `elem` (((catModule ++ ".") ++) <$> ["reprC","abstC"])

-- TODO: refactor

pprWithType :: CoreExpr -> SDoc
pprWithType = ppr . WithType
-- pprWithType e = ppr e <+> dcolon <+> ppr (exprType e)

pprWithType' :: CoreExpr -> SDoc
pprWithType' e = ppr e $+$ dcolon <+> ppr (exprType e)

pprMbWithType :: Maybe CoreExpr -> SDoc
pprMbWithType = maybe (text "failed") pprWithType

cccRuleName :: FastString
cccRuleName = fsLit "toCcc'"

composeRuleName :: FastString
composeRuleName = fsLit "compose/coerce"

evidenceRuleName :: FastString
evidenceRuleName = fsLit "evidence annotation"

cccRules :: Maybe (IORef Int) -> FamInstEnvs -> CccEnv -> ModGuts -> AnnEnv -> [CoreRule]
cccRules steps famEnvs env@(CccEnv {..}) guts annotations =
  [ BuiltinRule { ru_name  = cccRuleName
                , ru_fn    = varName cccPV
                , ru_nargs = 6  -- including type args
                , ru_try   = \ dflags inScope _fn ->
                                \ case
                                  -- _args | pprTrace "ccc ru_try args" (ppr _args) False -> undefined
                                  _es@(Type k : Type _a : Type _b : Type evType : ev : arg : _) ->
                                    -- pprTrace "ccc: going in" (ppr es) $
                                    -- ccc env (ops dflags inScope k) k arg
                                    unsafeLimit steps $
                                      ccc env (ops dflags inScope evType ev k) k arg
                                  _args -> -- pprTrace "ccc ru_try mismatch args" (ppr _args) $
                                           Nothing
                }
#if 0
  -- Are we still using the special composition rules?
  -- FIXME: needs a version with evidence argument
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

evidencePass :: CccEnv -> ModGuts -> CoreM ModGuts
evidencePass (CccEnv {..}) guts = bindsOnlyPass (mapM (annotateEvidence cccV cccPV 3)) guts

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install
#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
                       , pluginRecompile = purePlugin
#endif
                       }

-- Find an option "foo=bar" for optName "foo", returning a read of "bar".
parseOpt :: Read a => String -> [CommandLineOption] -> Maybe a
parseOpt optName = listToMaybe . catMaybes . map parse
 where
   parse = fmap read . stripPrefix (optName ++ "=")

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos =
  do -- pprTrace ("CCC install " ++ show opts) empty (return ())
     dflags <- getDynFlags
     -- Unfortunately, the plugin doesn't work in GHCi. Until fixed,
     -- disable under GHCi, so we can at least type-check conveniently.
     if hscTarget dflags == HscInterpreted then
        return todos
      else
       do
#if !MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
          reinitializeGlobals
#endif
          hsc_env <- getHscEnv
          pkgFamEnv <- getPackageFamInstEnv
          env <- mkCccEnv opts
          -- Add the rule after existing ones, so that automatically generated
          -- specialized ccc rules are tried first.
          let addCccRule, delCccRule :: ModGuts -> CoreM ModGuts
              addCccRule guts =
                -- pprTrace "Program binds before ccc" (ppr (mg_binds guts)) $
                do allAnns <- liftIO (prepareAnnotations hsc_env (Just guts))
                   let famEnvs = (pkgFamEnv, mg_fam_inst_env guts)
                       maxSteps = (unsafePerformIO . newIORef) <$>
                                  parseOpt "maxSteps" opts
                   return (on_mg_rules (++ cccRules maxSteps famEnvs env guts allAnns) guts)
              delCccRule guts = return (on_mg_rules (filter (not . isCccRule)) guts)
              isCccRule r = isBuiltinRule r && ru_name r `elem` [cccRuleName,composeRuleName]
              -- isCCC r | is = pprTrace "delRule" (ppr cccRuleName) is
              --         | otherwise = is
              --  where
              --    is = isBuiltinRule r && ru_name r == cccRuleName
              (pre,post) = -- (todos,[])
                           -- ([],todos)
                           splitAt 5 todos  -- guess
                           -- (swap . (reverse *** reverse) . splitAt 1 . reverse) todos
              annotateEvidencePass = CoreDoPluginPass "evidence-annotate toCcc'" (evidencePass env)
              ours = [ annotateEvidencePass
                     , CoreDoPluginPass "Ccc insert rule" addCccRule
                     , CoreDoSimplify 7 (mode dflags)
                     , CoreDoPluginPass "Ccc remove rule" delCccRule
                     , CoreDoPluginPass "Flag remaining ccc calls" (flagCcc env)
                     ]
          -- pprTrace "ccc pre-install todos:" (ppr todos) (return ())
          -- pprTrace "ccc post-install todos:" (ppr (pre ++ ours ++ post)) (return ())
          return (pre ++ ours ++ post)
 where
#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
   flagCcc :: CccEnv -> CorePluginPass
#else
   flagCcc :: CccEnv -> PluginPass
#endif
   flagCcc (CccEnv {..}) guts
     | showCcc && pprTrace "ccc final:" (ppr (mg_binds guts)) False = undefined
     | not (Seq.null remaining) &&
       showResiduals &&
       pprTrace "ccc residuals:" (ppr (toList remaining)) False = undefined
     | otherwise = return guts
    where
      showCcc = "showCcc" `elem` opts
      showResiduals = "showResiduals" `elem` opts
      remaining :: Seq CoreExpr
      remaining = collectQ cccArgs (mg_binds guts)
      cccArgs :: CoreExpr -> Seq CoreExpr
      -- unVarApps :: CoreExpr -> Maybe (Id,[Type],[CoreExpr])
      -- ccc :: forall k a b. (a -> b) -> k a b
      -- cccArgs c@(unVarApps -> Just (v,_tys,[_])) | v == cccV = Seq.singleton c
      cccArgs c@(unVarApps -> Just (v,_tys,[arg]))
        | v == cccPV, enablePolymorphism || isMono arg = Seq.singleton c
      cccArgs _                                  = mempty
      -- cccArgs = const mempty  -- for now
      collectQ :: (Data a, Monoid m) => (a -> m) -> GenericQ m
      collectQ f = everything mappend (mkQ mempty f)
   -- Extra simplifier pass
   mode
#if MIN_VERSION_GLASGOW_HASKELL(8,4,0,0)
     dflags
#else
     _dflags
#endif
        = SimplMode { sm_names      = ["Ccc simplifier pass"]
                    , sm_phase      = Phase 2 -- avoid inlining i.e. Vector which is at phase 1
                    , sm_rules      = True  -- important
                    , sm_inline     = True -- False -- ??
                    , sm_eta_expand = False -- ??
                    , sm_case_case  = True
#if MIN_VERSION_GLASGOW_HASKELL(8,4,0,0)
                    , sm_dflags     = dflags
#endif
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
        maybe (panic err) mkThing' =<<
          liftIO (lookupRdrNameInModuleForPlugins hsc_env modu (Unqual (mkOcc str)))
       where
         err = "ccc installation: couldn't find "
               ++ str ++ " in " ++ moduleNameString modu

#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
         -- In GHC 8.6, lookupRdrNameInModuleForPlugins returns a (Name, Module)
         -- where earlier it was just a Name
         mkThing' = mkThing . fst
#else
         mkThing' = mkThing
#endif

      lookupTh mkOcc mk modu = lookupRdr (mkModuleName modu) mkOcc mk
      enablePolymorphism = "enablePolymorphism" `elem` opts
      findId      = lookupTh mkVarOcc lookupId
      findTc      = lookupTh mkTcOcc  lookupTyCon
      -- findFloatTy = fmap mkTyConTy . findTc floatModule -- TODO: eliminate
      findCatId   = findId catModule
      findTrnId   = findId trnModule
      findRepTc   = findTc repModule
      findOkTyTc  = findTc okTypeModule
      findRepId   = findId repModule
      findBoxId   = findId boxModule
      findExtTc   = findTc extModule
      findExtId   = findId extModule
  closedTc      <- findTc catModule "ClosedCat"
  idV           <- findCatId "id"
  constV        <- findCatId "const"
  composeV      <- findCatId "."
  exlV          <- findCatId "exl"
  exrV          <- findCatId "exr"
  forkV         <- findCatId "&&&"
  applyV        <- findCatId "apply"
  curryV        <- findCatId "curry"
  uncurryV      <- findCatId "uncurry"
  ifV           <- findCatId "ifC"
  constFunV     <- findCatId "constFun"
  abstCV        <- findCatId "abstC"
  reprCV        <- findCatId "reprC"
  coerceV       <- findCatId "coerceC"
  cccV          <- findCatId "toCcc'"
  cccPV         <- findCatId "toCcc''"
  uncccV        <- findCatId "unCcc'"
  fmapV         <- findCatId "fmapC"
  fmapT1V       <- findTrnId "fmapT1"
  fmapT2V       <- findTrnId "fmapT2"
  casePairTopTV <- findTrnId "casePairTopT"
  casePairTV    <- findTrnId "casePairT"
  casePairLTV   <- findTrnId "casePairLT"
  casePairRTV   <- findTrnId "casePairRT"
  flipForkTV    <- findTrnId "flipForkT"
  castConstTV   <- findTrnId "castConstT"
  bottomTV      <- findTrnId "bottomT"
  repTc         <- findRepTc "Rep"
  okTypeTc      <- findOkTyTc "OkType"
  prePostV      <- findId "ConCat.Misc" "~>"
  boxIV         <- findBoxId "boxI"
  boxFV         <- findBoxId "boxF"
  boxDV         <- findBoxId "boxD"
  boxIBV        <- findBoxId "boxIB"
  ifEqIntHash   <- findBoxId "ifEqInt#"
  tagToEnumV    <- findId "GHC.Prim" "tagToEnum#"
  bottomV       <- findId "ConCat.Misc" "bottom"
  inlineV       <- findExtId "inline"
  uniqSupply    <- getUniqueSupplyM
  let mkPolyOp :: (String,(String,String)) -> CoreM (String,Var)
      mkPolyOp (stdName,(cmod,cop)) =
        do cv <- findId cmod cop
           return (stdName, cv)
  ruleBase <- eps_rule_base <$> (liftIO $ hscEPS hsc_env)
  -- pprTrace "ruleBase" (ppr ruleBase) (return ())
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
  -- TODO: refactor to eliminate duplicate code here and elsewhere.
  let boxers = DFMap.listToUDFM [(intTyCon,boxIV),(doubleTyCon,boxDV),(floatTyCon,boxFV)]
#else
  let boxers = OrdMap.fromList  [(intTyCon,boxIV),(doubleTyCon,boxDV),(floatTyCon,boxFV)]
#endif
  -- _ <- findId "GHC.Num" "subtract" -- help the plugin find instances for Float and Double
  when (isBottomingId cccV) $
    pprPanic "isBottomingId cccV" empty
  return (CccEnv { .. })

-- Variables that have associated ccc rewrite rules in AltCat. If we have
-- sufficient arity for the rule, including types, give it a chance to kick in.
cccRuledArities :: OrdMap.Map String Int
cccRuledArities = OrdMap.fromList
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
   -- (cat-name, [(std-name,cat-type-args)])
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
     -- , ("negateC",fdOps "negate"), ("addC",fdOps "plus")
     -- , ("subC",fdOps "minus"), ("mulC",fdOps "times")
     -- , ("recipC", fdOps "recip"), ("divideC", fdOps "divide")
     -- , ("expC", fdOps "exp") , ("cosC", fdOps "cos") , ("sinC", fdOps "sin")

     , ("succC",[("GHC.Enum.$fEnumInt_$csucc",[intTy])])
     , ("predC",[("GHC.Enum.$fEnumInt_$cpred",[intTy])])
     , ("divC",[("GHC.Real.$fIntegralInt_$cdiv",[intTy])])
     , ("modC",[("GHC.Real.$fIntegralInt_$cmod",[intTy])])
     --
     , ("floorC",[("GHC.Float.RealFracMethods.floorDoubleInt",[doubleTy,intTy])])
     , ("ceilingC",[("GHC.Float.RealFracMethods.ceilingDoubleInt",[doubleTy,intTy])])
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
      numOps op = numOp <$> ifd
       where
         numOp ty = (modu++".$fNum"++tyName++"_$c"++op,[ty])
          where
            tyName = pp ty
            modu | isIntTy ty = "GHC.Num"
                 | otherwise  = floatModule  -- Really?
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


--------------------------------------------------
-- * Misc

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
#if MIN_VERSION_GLASGOW_HASKELL(8,8,0,0)
stringExpr = Lit . mkLitString
#else
stringExpr = Lit . mkMachString
#endif

varNameExpr :: Id -> CoreExpr
varNameExpr = stringExpr . uniqVarName

#if ! MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)

pattern FunTy :: Type -> Type -> Type
pattern FunTy dom ran <- (splitFunTy_maybe -> Just (dom,ran))
 where FunTy = mkFunTy

-- TODO: Replace explicit uses of splitFunTy_maybe

-- TODO: Look for other useful pattern synonyms

pattern FunCo :: Role -> Coercion -> Coercion -> Coercion
pattern FunCo r dom ran <- TyConAppCo r (isFunTyCon -> True) [dom,ran]
 where FunCo = mkFunCo

#endif

onCaseRhs :: Type -> Unop (Unop CoreExpr)
onCaseRhs altsTy' f (Case scrut v _ alts) =
  Case scrut v altsTy' (onAltRhs f <$> alts)
onCaseRhs _ _ e = pprPanic "onCaseRhs. Not a case: " (ppr e)

onAltRhs :: Unop CoreExpr -> Unop CoreAlt
onAltRhs f (con,bs,rhs) = (con,bs,f rhs)

-- To help debug. Sometimes I'm unsure what constructor goes with what ppr.
coercionTag :: Coercion -> String
coercionTag Refl        {} = "Refl"
#if MIN_VERSION_GLASGOW_HASKELL(8,8,0,0)
coercionTag GRefl        {} = "GRefl"
#endif
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
#if !MIN_VERSION_GLASGOW_HASKELL(8,8,0,0)
coercionTag CoherenceCo {} = "CoherenceCo"
#endif
coercionTag KindCo      {} = "KindCo"
coercionTag SubCo       {} = "SubCo"
#if MIN_VERSION_GLASGOW_HASKELL(8,4,0,0)
coercionTag HoleCo      {} = "HoleCo"
#endif

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

-- TODO: reconcile with inlineClassOp from ConCat.Inline.ClassOp

exprHead :: CoreExpr -> Maybe Id
exprHead (Var v)     = Just v
exprHead (App fun _) = exprHead fun
exprHead (Cast e _)  = exprHead e
exprHead _           = Nothing

onExprHead :: DynFlags -> (Id -> Maybe CoreExpr) -> ReExpr
onExprHead _dflags h = (fmap.fmap) simpleOptExpr' $
                       go id
 where
   go cont (Var v)       = cont <$> h v
   go cont (App fun arg) = go (cont . (`App` arg)) fun
   go cont (Cast e co)   = go (cont . (`Cast` co)) e
   go _ _                = Nothing

#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
   simpleOptExpr' = simpleOptExpr _dflags
#else
   simpleOptExpr' = simpleOptExpr
#endif

-- TODO: try go using Maybe fmap instead of continuation.

-- The simpleOptExpr here helped keep simplification going.
-- TODO: try without.

-- Identifier not occurring in a given variable set
freshId :: VarSet -> String -> Type -> Id
freshId used nm ty =
  uniqAway (mkInScopeSet used) $
  mkSysLocal (fsLit nm) (mkBuiltinUnique 17) ty

freshDeadId :: VarSet -> String -> Type -> Id
freshDeadId used nm ty = setIdOccInfo (freshId used nm ty) IAmDead

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
#if MIN_VERSION_GLASGOW_HASKELL(8,2,0,0)
funCat = mkTyConApp funTyCon [liftedRepDataConTy, liftedRepDataConTy]
#else
funCat = mkTyConTy funTyCon
#endif

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
isMonoTy (TyConApp _ tys) = all isMonoTy tys
isMonoTy (AppTy u v)      = isMonoTy u && isMonoTy v
isMonoTy (FunTy' u v)     = isMonoTy u && isMonoTy v
isMonoTy (LitTy _)        = True
isMonoTy _                = False

isMono :: CoreExpr -> Bool
isMono = isMonoTy . exprType

-- isMonoTy t | pprTrace "isMonoTy" (ppr t) False = undefined

-- | Number of occurrences of a given Id in an expression.
-- Gives a large value if the Id appears under a lambda.
idOccs :: Bool -> Id -> CoreExpr -> Int
idOccs penalizeUnderLambda x = go
 where
   lamFactor | penalizeUnderLambda = 100
             | otherwise           = 1
   -- go e | pprTrace "idOccs go" (ppr e) False = undefined
   go (Type _)                 = 0
   go (Coercion _)             = 0
   go _e@(exprType -> isPredTy' -> True)
     --  | pprTrace "idOccs predicate" (pprWithType _e) False = undefined
     = 0
   go (Lit _)                  = 0
   go (Var y)      | y == x    = -- pprTrace "idOccs found" (ppr y) $
                                 1
                   | otherwise = 0
   go (App u v)                = go u + go v
   go (Tick _ e)               = go e
   go (Cast e _)               = go e
   go (Lam y body) | y == x    = 0
                   | otherwise = lamFactor * go body
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
-- isPredTy' ty | pprTrace "isPredTy'" (ppr (ty,isPredTy ty,splitTyConApp_maybe ty)) False = undefined
isPredTy' ty = isPredTy ty || others ty
 where
   others (splitTyConApp_maybe -> Just (tc,tys)) =
     -- pprTrace "isPredTy' tyCon arity" (ppr (tyConArity tc)) $
     -- The first half of the arguments are representation types ('PtrRepLifted)
     isUnboxedTupleTyCon tc && all isPredTy' (drop (length tys `div` 2) tys)
   others _ = False

starKind :: Kind
#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
starKind = liftedTypeKind
#else
starKind = mkTyConTy starKindTyCon
#endif

castE :: Coercion -> CoreExpr
castE co = Lam x (mkCast (Var x) co)
 where
   x = freshId emptyVarSet "w" dom
   Pair dom _ = coercionKind co

pprCoWithType :: Coercion -> SDoc
pprCoWithType co = ppr co <+> dcolon $$ ppr (coercionType co)

setNominalRole_maybe' :: Coercion -> Maybe Coercion
#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
setNominalRole_maybe' c = setNominalRole_maybe (coercionRole c) c
#else
setNominalRole_maybe' = setNominalRole_maybe
#endif

-- Exists somewhere?
eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe = either (const Nothing) Just

altRhs :: Alt b -> Expr b
altRhs (_,_,rhs) = rhs

altVars :: Alt b -> [b]
altVars (_,bs,_) = bs

isCast :: Expr b -> Bool
isCast (Cast {}) = True
isCast _         = False

-- | Monadic variation on everywhere (bottom-up)
-- everywhereM :: Monad m => GenericM m -> GenericM m
-- everywhereM f = f <=< gmapM (everywhereM2 f)

-- | Monadic variation on everywhere' (top-down)
everywhereM' :: Monad m => GenericM m -> GenericM m
everywhereM' f = gmapM (everywhereM' f) <=< f

exprConstr :: Expr b -> String
exprConstr (Var {})      = "Var"
exprConstr (Lit {})      = "Lit"
exprConstr (App {})      = "App"
exprConstr (Lam {})      = "Lam"
exprConstr (Let {})      = "Let"
exprConstr (Case {})     = "Case"
exprConstr (Cast {})     = "Cast"
exprConstr (Tick {})     = "Tick"
exprConstr (Type {})     = "Type"
exprConstr (Coercion {}) = "Coercion"

hasTyCon :: TyCon -> Type -> Bool
hasTyCon tc (tcSplitTyConApp_maybe -> Just (tc', _)) = tc' == tc
hasTyCon _ _ = False

-- Alternative to Case when we don't want to work out the alternatives type, and
-- we're willing to crash on empty alternatives.
mkCase1 :: CoreExpr -> Id -> [CoreAlt] -> CoreExpr
mkCase1 scrut v alts@(alt0:_) = Case scrut v (exprType (altRhs alt0)) alts
mkCase1 _ _ _ = pprPanic "mkCase1 with empty alts" empty

-- Experiment: wrap a stateful counter around a Maybe.
unsafeLimit :: Maybe (IORef Int) -> Unop (Maybe a)
unsafeLimit Nothing = id
unsafeLimit (Just r) = \ a -> unsafePerformIO $
  do n <- readIORef r
     if n == 0 then
       return Nothing
      else
       do -- pprTrace "unsafeLimit" (ppr n) (return ())
          writeIORef r (n-1)
          return a
{-# NOINLINE unsafeLimit #-}

-- experiment
alwaysSubst :: CoreExpr -> Bool
-- alwaysSubst e@(collectArgs -> (Var _, args))
--   | pprTrace "alwaysSubst" (ppr (e,not (isTyCoDictArg e), all isTyCoDictArg args)) False = undefined
alwaysSubst e@(collectArgs -> (Var _, args)) =
  not (isTyCoDictArg e) && all isTyCoDictArg args
alwaysSubst _ = False

mkCoercible :: Kind -> Type -> Type -> Coercion -> CoreExpr
mkCoercible k a b co =
  Var (dataConWrapId coercibleDataCon) `mkTyApps` [k,a,b] `App` Coercion co

isFunCat :: Type -> Bool
isFunCat (TyConApp tc _) = isFunTyCon tc
isFunCat _               = False

-- If the wild variable in a Case is not dead, make a new dead wild var and
-- transform to a Let.
deadifyCaseWild :: ReExpr
deadifyCaseWild e@(Case scrut wild _rhsTy [(DataAlt dc, [a,b], rhs)])
  | not (isDeadBinder wild) =
  Just (Let (NonRec wild scrut)
         (Case (Var wild) wild' _rhsTy [(DataAlt dc, [a,b], rhs)]))
 where
   wild' = freshDeadId (exprFreeVars e) "newWild" (varType wild)
deadifyCaseWild _ = Nothing
