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

-- | GHC plugin converting to CCC form.

module ConCat.Plugin (plugin) where

import Data.Monoid (Any(..))
import Control.Arrow (first,second,(***))
import Control.Applicative (liftA2,(<|>))
import Control.Monad (unless,when,guard,(<=<))
import Data.Foldable (toList)
import Data.Maybe (isNothing,isJust,fromMaybe,catMaybes,listToMaybe)
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
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef

import GhcPlugins hiding (substTy,cat)
import Class (classAllSelIds)
import CoreArity (etaExpand)
import CoreLint (lintExpr)
import DynamicLoading
import MkId (mkDictSelRhs,coerceId)
import Pair (Pair(..))
import PrelNames (leftDataConName,rightDataConName)
import Type (coreView)
import TcType (isIntTy,isIntegerTy,tcSplitTyConApp_maybe)
import TysPrim (intPrimTyCon)
import FamInstEnv (normaliseType)
import TyCoRep                          -- TODO: explicit imports
import Unique (mkBuiltinUnique)
-- For normaliseType etc
import FamInstEnv

import ConCat.Misc (Unop,Binop,Ternop,PseudoFun(..),(~>))
import ConCat.BuildDictionary
-- import ConCat.Simplify

-- Information needed for reification. We construct this info in
-- CoreM and use it in the ccc rule, which must be pure.
data CccEnv = CccEnv { dtrace           :: forall a. String -> SDoc -> a -> a
                     , cccV             :: Id
                     , uncccV           :: Id
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
                     , fmapTV           :: Id
                     , casePairTV       :: Id
                     , casePairLTV      :: Id
                     , casePairRTV      :: Id
                     , reprCV           :: Id
                     , abstCV           :: Id
                     , coerceV          :: Id
                     , bottomCV         :: Id
                     , repTc            :: TyCon
                     , prePostV         :: Id
                     , boxers           :: Map TyCon Id  -- to remove
                     , tagToEnumV       :: Id
                     , bottomV          :: Id
                     , boxIBV           :: Id
                     , ifEqIntHash      :: Id
                     , inlineV          :: Id
                     , hsc_env          :: HscEnv
                     , ruleBase         :: RuleBase  -- to remove
                     }

-- Whether to run Core Lint after every step
lintSteps :: Bool
lintSteps = True -- False

type Rewrite a = a -> Maybe a
type ReExpr = Rewrite CoreExpr
type ReExpr2 = CoreExpr -> Rewrite CoreExpr

#define Doing(str) dtrace "Doing" (text (str)) id $

-- Category
type Cat = Type

ccc :: CccEnv -> Ops -> Type -> ReExpr
ccc (CccEnv {..}) (Ops {..}) cat =
  traceRewrite "toCcc'" $
  (if lintSteps then lintReExpr else id) $
  go
 where
   go :: ReExpr
   go = \ case
     e | dtrace ("go ccc "++pp cat++":") (pprWithType e) False -> undefined
     -- Sanity check: ccc should only take functions.
     e@(exprType -> isFunTy -> False) ->
       pprPanic "ccc/go: not of function type" (pprWithType e)

     Lam x body -> goLam x body

     Let bind@(NonRec v rhs) body ->
       -- Experiment: always float.
       if -- dtrace "top Let tests" (ppr (not (isClosed cat), substFriendly (isClosed cat) rhs, idOccs False v body)) $
          not (isClosed cat) ||  -- experiment
          substFriendly (isClosed cat) rhs || idOccs False v body <= 1 then
         Doing("top Let float")
         return (Let bind (mkCcc body))
       else
         Doing("top Let to beta-redex")
         go (App (Lam v body) rhs)

     (reCat -> Just e') ->
       Doing("top reCat")
       Just e'

     (isPseudoApp -> True) ->
       Doing("top Avoid pseudo-app")
       Nothing

     -- ccc-of-case. Maybe restrict to isTyCoDictArg for all bound variables, but
     -- perhaps I don't need to.
     Case scrut wild rhsTy alts
       | Just scrut' <- unfoldMaybe scrut
       -> Doing("top Case unfold")  --  of dictionary
          return $ mkCcc (Case scrut' wild rhsTy alts)
          -- TODO: also for lam?

     Case scrut wild rhsTy alts ->
       Doing("top Case")
       -- TODO: take care about orphaning regular variables
       return $ Case scrut wild (catTy rhsTy) (onAltRhs mkCcc <$> alts)

     Cast e co@( -- dtrace "top nominal cast co" (pprCoWithType co {-<+> (ppr (setNominalRole_maybe co))-}) id
                setNominalRole_maybe -> Just (reCatCo -> Just co')) ->
       -- etaExpand turns cast lambdas into themselves
       Doing("top nominal cast")
       let co'' = downgradeRole (coercionRole co) (coercionRole co') co' in
         -- pprTrace "top nominal Cast" (ppr co $$ text "-->" $$ ppr co'') $
         return (Cast (mkCcc e) co'')
       -- I think GHC is undoing this transformation, so continue eagerly
       -- (`Cast` co') <$> go e

     e@(Cast e' (coercionRole -> Representational))
       | FunTy a  b  <- exprType e
       , FunTy a' b' <- exprType e'
       ->
          Doing("top representational cast")
          -- Will I get unnecessary coerceCs due to nominal-able sub-coercions?
          return $ mkCompose cat (mkCoerceC cat b' b) $
                   mkCompose cat (mkCcc e') $
                   mkCoerceC cat a a'

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

     e@(App u v)
       | liftedExpr v
       , Just v' <- mkConst' cat dom v
       , Just uncU' <- mkUncurryMaybe cat (mkCcc u)
       -> Doing("top App")
          return (mkCompose cat uncU' (mkFork cat v' (mkId cat dom)))
      where
        Just (dom,_) = splitFunTy_maybe (exprType e)

     e@(exprHead -> Just _v)
       | -- Temp hack: avoid unfold/case-of-product loop.
         Just e' <- unfoldMaybe e
       -> Doing("top unfold")
          return (mkCcc e')

     Tick t e -> Doing("top tick")
                 return $ Tick t (mkCcc e)
     _e -> Doing("top Unhandled")
           Nothing

   goLam x body = case body of
     Var y | x == y -> Doing("lam Id")
                       return (mkId cat xty)

     _ | isConst, not (isFunTy bty), not (isMonoTy bty)
       -> Doing("lam Poly const bail")
          Nothing
      -- must come before "lam Const" and "lam App"
     (collectArgs -> (Var ((== bottomV) -> True),[Type ty]))
       | Just e' <- mkBottomC cat xty ty
       -> Doing("lam bottom")
          return e'

     _ | isConst, Just body' <- mkConst' cat xty body
       -> Doing("lam mkConst'")
       return body'

     (isPseudoApp -> True) ->
         Doing("lam Avoid pseudo-app")
         Nothing

     (collectArgs -> (PairVar,(Type a : Type b : rest))) ->
       case rest of
         []    -> -- (,) == curry id
                  -- Do we still need this case, or is it handled by catFun?
                  dtrace "Doing" (text ("lam Plain (,)")) id $
                  -- return (mkCurry cat (mkId cat (pairTy a b)))
                  mkCurry' cat (mkId cat (pairTy a b))
         [_]   -> Doing("lam Pair eta-expand")
                  goLam x (etaExpand 1 body)
         [u,v] -> Doing("lam Pair")
                  -- dtrace "Pair test" (pprWithType u <> comma <+> pprWithType v) $
                  return (mkFork cat (mkCcc (Lam x u)) (mkCcc (Lam x v)))
         _     -> pprPanic "goLam Pair: too many arguments: " (ppr rest)

     -- Revisit.

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

     -- TODO: refactor with top Let
     _e@(Let bind@(NonRec v rhs) body') ->
       -- dtrace "lam Let subst criteria" (ppr (substFriendly (isClosed cat) rhs, not xInRhs, idOccs True v body')) $
       if not (isClosed cat) || -- experiment
          substFriendly (isClosed cat) rhs || not xInRhs || idOccs True v body' <= 1 then
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

     (etaReduce_maybe -> Just e') ->
       Doing("lam eta-reduce")
       goLam x e'

     Lam y e ->
       -- (\ x -> \ y -> U) --> curry (\ z -> U[fst z/x, snd z/y])
       Doing("lam Lam")
       -- TODO: maybe let instead of subst
       -- Substitute rather than making a Let, to prevent infinite regress.
       -- return $ mkCurry cat (mkCcc (Lam z (subst sub e)))
       -- Fail gracefully when we can't mkCurry, giving inlining a chance to
       -- resolve polymorphism to monomorphism. See 2017-10-18 notes.
       mkCurry' cat (mkCcc (Lam z (subst sub e)))
      where
        yty = varType y
        z = freshId (exprFreeVars e) zName (pairTy xty yty)
        zName = uqVarName x ++ "_" ++ uqVarName y
        sub = [(x,mkEx funCat exlV (Var z)),(y,mkEx funCat exrV (Var z))]
        -- TODO: consider using fst & snd instead of exl and exr here

     e@(Case scrut wild _ty [(_dc,[unboxedV],rhs)])
       | Just (tc,[]) <- splitTyConApp_maybe (varType wild)
       , Just boxV <- Map.lookup tc boxers
       -> Doing("lam Case of boxer")
          let wild' = setIdOccInfo wild NoOccInfo
              tweak :: Unop CoreExpr
              tweak (Var v) | v == unboxedV =
                pprPanic ("lam Case of boxer: bare unboxed var") (ppr e)
              tweak (App (Var f) (Var v)) | f == boxV, v == unboxedV = Var wild'
              tweak e' = e'
          in
            -- Note top-down (everywhere') instead of bottom-up (everywhere)
            -- so that we can find 'boxI v' before v.
            return (mkCcc (Lam x (Let (NonRec wild' scrut) (everywhere' (mkT tweak) rhs))))

     Case _scrut (isDeadBinder -> True) _rhsTy [(DEFAULT,[],rhs)] ->
       Doing("lam case-default")
       return (mkCcc (Lam x rhs))

     Case _scrut (isDeadBinder -> True) _rhsTy [(_, [], rhs)] ->
       Doing("lam Case nullary")
       return (mkCcc (Lam x rhs))
       -- TODO: abstract return (mkCcc (Lam x ...))

     Case scrut v@(isDeadBinder -> False) _rhsTy [(_, bs, rhs)]
       | isEmptyVarSet (mkVarSet bs `intersectVarSet` exprFreeVars rhs) ->
       Doing("lam Case to let")
       return (mkCcc (Lam x (Let (NonRec v scrut) rhs)))

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

     e@(Case scrut wild _rhsTy [(DataAlt dc, [a,b], rhs)])
         | isBoxedTupleTyCon (dataConTyCon dc) ->
       Doing("lam Case of product")

       if | not (isDeadBinder wild) ->
              -- TODO: handle this case
              pprPanic "lam Case of product live wild binder" (ppr e)
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

     --
     -- Case (Cast scrut (setNominalRole_maybe -> Just co')) v altsTy alts
     --   -> Doing("lam Case cast")
     --
     Case scrut v altsTy alts
       | Just scrut' <- unfoldMaybe' scrut
       -> Doing("lam Case unfold")
          return $ mkCcc $ Lam x $
           Case scrut' v altsTy alts

     Cast body' co@(setNominalRole_maybe -> Just co') ->
       -- etaExpand turns cast lambdas into themselves
       Doing("lam nominal cast")
       let r  = coercionRole co
           r' = coercionRole co'         -- always Nominal, isn't it?
           co'' = downgradeRole r r' co' -- same as co?
       in
         return (mkCcc (Cast (Lam x body') (FunCo r (mkReflCo r xty) co'')))

     e@(Cast e' _) ->
       Doing("lam representational cast")
       -- Will I get unnecessary coerceCs due to nominal-able sub-coercions?
       -- TODO: convert to mkCoerceC also. Then eliminate mkCoerceC, and
       -- rename mkCoerceC.
       return $ mkCompose cat (mkCoerceC cat (exprType e') (exprType e)) $
                mkCcc (Lam x e')

     -- Does unfolding suffice as an alternative? Not quite, since lambda-bound
     -- variables can appear as scrutinees. Maybe we could eliminate that
     -- possibility with another transformation.
     -- 2016-01-04: I moved lam abstReprCase after unfold

     -- Do I also need top abstReprCase?
     Case scrut v@(varType -> vty) altsTy alts
       | Just repr <- mkReprC'_maybe funCat vty
       , Just abst <- mkAbstC'_maybe funCat vty
       -> Doing("lam abstReprCase")
          return $ mkCcc $ Lam x $
           Case (inlineE abst `App` (repr `App` scrut)) v altsTy alts

     -- This rule goes after lam App compose, so we know that the fmap'd
     -- function depends on x, and the extra complexity is warranted.
     _e@(collectArgs -> (Var v, [_arrow,Type h,Type b,Type c,_dict,_ok,f])) | v == fmapV ->
        Doing("lam fmap")
        -- pprTrace "fmapT type" (ppr (varType fmapTV)) $
        -- pprTrace "lam fmap arg" (ppr _e) $
        -- pprTrace "lam fmap pieces" (ppr (h,b,c,f)) $
        let e' = mkCcc (onDict (varApps fmapTV [h,xty,b,c] []) `App` Lam x f) in
          -- pprTrace "fmap constructed expression" (ppr e') $
          -- pprPanic "lam fmap bailing" empty
          return e'

     -- (\ x -> U V) --> U . (\ x -> V) if x not free in U
     u `App` v | liftedExpr v
               , not (x `isFreeIn` u)
               -> case mkCompose' cat (mkCcc u) (mkCcc (Lam x v)) of
                    Nothing ->
                      Doing("lam App compose bail")
                      Nothing
                    Just e' ->
                      Doing("lam App compose")
                      return e'

     -- (\ x -> U V) --> apply . (\ x -> U) &&& (\ x -> V)
     u `App` v | liftedExpr v
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

     e'| Just body' <- unfoldMaybe e'
       -> Doing("lam unfold")
          return (mkCcc (Lam x body'))
          -- TODO: factor out Lam x (mkCcc ...)
     Tick t e -> Doing("lam tick")
                 return $ Tick t (mkCcc (Lam x e))
     -- Give up
     _e -> Nothing
    where
      xty = varType x
      bty = exprType body
      isConst = not (x `isFreeIn` body)

pattern Coerce :: Cat -> Type -> Type -> CoreExpr
pattern Coerce k a b <-
  (collectArgs -> (Var (catSuffix -> Just "coerceC"), [Type k,Type a,Type b,_dict]))

pattern Compose :: Cat -> Type -> Type -> Type -> CoreExpr -> CoreExpr -> CoreExpr
pattern Compose k a b c g f <-
  (collectArgs -> (Var (catSuffix -> Just "."), [Type k,Type b,Type c, Type a,_catDict,_ok,g,f]))

-- TODO: when the nested-pattern definition bug
-- (https://ghc.haskell.org/trac/ghc/ticket/12007) gets fixed (GHC 8.0.2), use
-- the CatVar version of Compose and Coerce.

-- For the composition BuiltinRule
composeR :: CccEnv -> Ops -> ReExpr2
-- composeR _ _ g f | pprTrace "composeR try" (ppr (g,f)) False = undefined
composeR (CccEnv {..}) (Ops {..}) _g@(Coerce k _b c) _f@(Coerce _k a _b')
  = -- pprTrace "composeR coerce" (ppr _g $$ ppr _f) $
    Just (mkCoerceC k a c)

composeR (CccEnv {..}) (Ops {..}) _h@(Coerce k _b c) (Compose _k _ a _b' _g@(Coerce _k' _z _a') f)
  = -- pprTrace "composeR coerce re-assoc" (ppr _h $$ ppr _g $$ ppr f) $
    Just (mkCompose k (mkCoerceC k a c) f)
composeR _ _ _ _ = Nothing

pattern CatVar :: String -> Id
pattern CatVar str <- (fqVarName -> stripPrefix (catModule ++ ".") -> Just str)

catSuffix :: Id -> Maybe String
catSuffix (CatVar suff) = Just suff
catSuffix _             = Nothing

data Ops = Ops
 { inlineE        :: Unop CoreExpr
 , boxCon         :: ReExpr
 , catTy          :: Unop Type
 , reCatCo        :: Rewrite Coercion
 , repTy          :: Unop Type
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
 , traceRewrite   :: forall f a b. (Functor f, Outputable a, Outputable b) => String -> Unop (a -> f b)
 , tyArgs2_maybe  :: Type -> Maybe (Type,Type)
 , tyArgs2        :: Type -> (Type,Type)
 , pprTrans       :: forall a b. (Outputable a, Outputable b) => String -> a -> b -> b
 , lintReExpr     :: Unop ReExpr
 , transCatOp     :: ReExpr
 , reCat          :: ReExpr
 , isPseudoApp    :: CoreExpr -> Bool
 , normType       :: Role -> Type -> (Coercion, Type)

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
      success = (Any True,)

      tweak :: CoreExpr -> (Any,CoreExpr)
      tweak e@(App (Var con) e')
        | isDataConWorkId con
        , Just (tc,[]) <- splitTyConApp_maybe (exprType e)
        , Just boxV <- Map.lookup tc boxers
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

   catTy :: Unop Type
   catTy (tyArgs2 -> (a,b)) = mkAppTys cat [a,b]

   reCatCo :: Rewrite Coercion
   reCatCo (FunCo r a b) = Just (mkAppCos (mkReflCo r cat) [a,b])
   reCatCo (splitAppCo_maybe -> Just
            (splitAppCo_maybe -> Just
             (Refl r _k,a),b)) =
     Just (mkAppCos (mkReflCo r cat) [a,b])

   reCatCo (co1 `TransCo` co2) = TransCo <$> reCatCo co1 <*> reCatCo co2
   reCatCo co = pprTrace "ccc reCatCo: unhandled coercion" (ppr co) $
                Nothing

   -- Interpret a representational cast
   -- TODO: Try swapping argument order
   repTy :: Unop Type
   repTy t = mkTyConApp repTc [t]

   -- Temp hack: avoid exl/exr and reprC/abstC.
   unfoldMaybe' :: ReExpr
   unfoldMaybe' e@(exprHead -> Just v)
     | not (isSelectorId v || isAbstReprId v) = unfoldMaybe e
   unfoldMaybe' _ = Nothing

   unfoldMaybe :: ReExpr
   unfoldMaybe e = onExprHead inlineMaybe e

   inlineMaybe :: Id -> Maybe CoreExpr
   inlineMaybe v = (inlineId <+ inlineClassOp) v

   noDictErr :: SDoc -> Either SDoc a -> a
   noDictErr doc =
     either (\ msg -> pprPanic "ccc - couldn't build dictionary for" (doc <> colon $$ msg)) id

   onDictTry :: CoreExpr -> Either SDoc CoreExpr
   onDictTry e | Just (ty,_) <- splitFunTy_maybe (exprType e)
               , isPredTy' ty = App e <$> buildDictMaybe ty
               | otherwise = return e

   onDictMaybe :: ReExpr
   onDictMaybe e = case onDictTry e of
                     Left  msg  -> dtrace "Couldn't build dictionary for"
                                     (pprWithType e <> colon $$ msg) $
                                   Nothing
                     Right dict -> Just dict

   onDict :: Unop CoreExpr
   onDict f = noDictErr (pprWithType f) (onDictTry f)

   -- Yet another variant: keep applying to dictionaries as long as we have
   -- a predicate type. TODO: reassess and refactor these variants.
   onDicts :: Unop CoreExpr
   onDicts e | Just (ty,_) <- splitFunTy_maybe (exprType e)
             , isPredTy' ty = onDicts (onDict e)
             | otherwise    = e

   buildDictMaybe :: Type -> Either SDoc CoreExpr
   buildDictMaybe ty = unsafePerformIO $
                       buildDictionary hsc_env dflags guts inScope ty

   catOp :: Cat -> Var -> [Type] -> CoreExpr
   catOp k op tys = onDicts (Var op `mkTyApps` (k : tys))

   catOpMaybe :: Cat -> Var -> [Type] -> Maybe CoreExpr
   catOpMaybe k op tys = onDictMaybe (Var op `mkTyApps` (k : tys))

   mkCcc' :: Unop CoreExpr  -- Any reason to parametrize over Cat?
   mkCcc' e = varApps cccV [cat,a,b] [e]
    where
      (a,b) = fromMaybe (pprPanic "mkCcc non-function:" (pprWithType e)) $
              splitFunTy_maybe (exprType e)

   mkCcc :: Unop CoreExpr  -- Any reason to parametrize over Cat?
   mkCcc e = mkCcc' e

   -- TODO: replace composeV with mkCompose in CccEnv
   -- Maybe other variables as well
   mkId :: Cat -> Type -> CoreExpr
   mkId k ty = onDict (catOp k idV [ty])

   mkCompose :: Cat -> Binop CoreExpr
   -- (.) :: forall b c a. (b -> c) -> (a -> b) -> a -> c
   mkCompose k g f
     | Just (b,c ) <- tyArgs2_maybe (exprType g)
     , Just (a,b') <- tyArgs2_maybe (exprType f)
     , b `eqType` b'
     = mkCoreApps (onDict (catOp k composeV [b,c,a])) [g,f]
     | otherwise = pprPanic "mkCompose mismatch:" (pprWithType g $$ pprWithType f)

   -- Experiment
   mkCompose' :: Cat -> CoreExpr -> CoreExpr -> Maybe CoreExpr
   -- (.) :: forall b c a. (b -> c) -> (a -> b) -> a -> c
   mkCompose' k g f
     | Just (b,c ) <- tyArgs2_maybe (exprType g)
     , Just (a,b') <- tyArgs2_maybe (exprType f)
     , b `eqType` b'
     = flip mkCoreApps [g,f] <$> (onDictMaybe =<< catOpMaybe k composeV [b,c,a])
     | otherwise = pprPanic "mkCompose mismatch:" (pprWithType g $$ pprWithType f)

   mkEx :: Cat -> Var -> Unop CoreExpr
   mkEx k ex z =
     -- -- For the class method aliases (exl, exr):
     onDict (catOp k ex [a,b]) `App` z
    where
      (a,b)  = tyArgs2 (exprType z)

   mkFork :: Cat -> Binop CoreExpr
   mkFork k f g =
     -- (&&&) :: forall {k :: * -> * -> *} {a} {c} {d}.
     --          (ProductCat k, Ok k d, Ok k c, Ok k a)
     --       => k a c -> k a d -> k a (Prod k c d)
     onDict (catOp k forkV [a,c,d]) `mkCoreApps` [f,g]
    where
      (a,c) = tyArgs2 (exprType f)
      (_,d) = tyArgs2 (exprType g)

   mkFork' :: Cat -> ReExpr2
   mkFork' k f g =
     -- (&&&) :: forall {k :: * -> * -> *} {a} {c} {d}.
     --          (ProductCat k, Ok k d, Ok k c, Ok k a)
     --       => k a c -> k a d -> k a (Prod k c d)
     flip mkCoreApps [f,g] <$> (onDictMaybe =<< catOpMaybe k forkV [a,c,d])
    where
      (a,c) = tyArgs2 (exprType f)
      (_,d) = tyArgs2 (exprType g)

   mkApplyMaybe :: Cat -> Type -> Type -> Maybe CoreExpr
   mkApplyMaybe k a b =
     -- apply :: forall {k :: * -> * -> *} {a} {b}. (ClosedCat k, Ok k b, Ok k a)
     --       => k (Prod k (Exp k a b) a) b
     onDictMaybe =<< catOpMaybe k applyV [a,b]

   isClosed :: Cat -> Bool
   isClosed k = isJust (mkApplyMaybe k unitTy unitTy)

   normType = normaliseType famEnvs

   mkCurry' :: Cat -> ReExpr
   mkCurry' k e =
     -- curry :: forall {k :: * -> * -> *} {a} {b} {c}.
     --          (ClosedCat k, Ok k c, Ok k b, Ok k a)
     --       => k (Prod k a b) c -> k a (Exp k b c)
     (`App` e) <$> (onDictMaybe =<< catOpMaybe k curryV [a,b,c])
    where
      (tyArgs2 -> (tyArgs2 -> (a,b),c)) = exprType e

   mkCurry :: Cat -> Unop CoreExpr
   mkCurry k e =
     -- curry :: forall {k :: * -> * -> *} {a} {b} {c}.
     --          (ClosedCat k, Ok k c, Ok k b, Ok k a)
     --       => k (Prod k a b) c -> k a (Exp k b c)
     onDict (catOp k curryV [a,b,c]) `App` e
    where
      (tyArgs2 -> (tyArgs2 -> (a,b),c)) = exprType e

   mkUncurryMaybe :: Cat -> ReExpr
   mkUncurryMaybe k e =
     -- uncurry :: forall {k :: * -> * -> *} {a} {b} {c}.
     --            (ClosedCat k, Ok k c, Ok k b, C1 (Ok k) a)
     --         => k a (Exp k b c) -> k (Prod k a b) c
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
     (`App` e) <$> (onDictMaybe =<< catOpMaybe k constV [exprType e, dom])

   mkConstFun :: Cat -> Type -> ReExpr
   mkConstFun k dom e =
     -- constFun :: forall k p a b. (ClosedCat k, Oks k '[p, a, b])
     --          => k a b -> k p (Exp k a b)
     (`App` e) <$> (onDictMaybe . inlineE =<< catOpMaybe k constFunV [dom,a,b])
    where
      (a,b) = tyArgs2 (exprType e)
   -- Split k a b into a & b.
   -- TODO: check that k == cat
   -- Turn U into either const U or constFun (mkCcc U) if possible.

   mkConst' :: Cat -> Type -> ReExpr
   mkConst' k dom e | isFunTy (exprType e) = mkConstFun k dom (mkCcc e)
                    | otherwise            = mkConst k dom e
   -- TODO: refactor mkReprC and mkAbstC into one function that takes an Id. p

   mkAbstC :: Cat -> Type -> CoreExpr
   mkAbstC k ty = catOp k abstCV [ty]

   mkReprC :: Cat -> Type -> CoreExpr
   mkReprC k ty = catOp k reprCV [ty]

   mkReprC',mkAbstC' :: Cat -> Type -> CoreExpr

   mkReprC' k ty =
     fromMaybe (pprPanic "mkReprC' fail" (ppr (k,ty))) (mkReprC'_maybe k ty)

   mkAbstC' k ty =
     fromMaybe (pprPanic "mkAbstC' fail" (ppr (k,ty))) (mkAbstC'_maybe k ty)
   -- TODO: Combine mkReprC'_maybe and mkAbstC'_maybe for efficiency.
   -- TODO: Remove non-maybe versions, and drop "_maybe" from names.

   mkReprC'_maybe :: Cat -> Type -> Maybe CoreExpr
   mkReprC'_maybe k a = catOpMaybe k reprCV [a,r]
    where
      (_co,r) = normType Nominal (repTy a)

   mkAbstC'_maybe :: Cat -> Type -> Maybe CoreExpr
   mkAbstC'_maybe k a =
     catOpMaybe k abstCV [a,r]
    where
      (_co,r) = normType Nominal (repTy a)

   mkCoerceC :: Cat -> Type -> Type -> CoreExpr
   mkCoerceC k dom cod
     | dom `eqType` cod = mkId k dom
     | otherwise = catOp k coerceV [dom,cod]

   tyArgs2_maybe :: Type -> Maybe (Type,Type)
   tyArgs2_maybe _ty@(splitAppTy_maybe -> Just (splitAppTy_maybe -> Just (_,a),b)) =
     Just (a,b)
   tyArgs2_maybe _ = Nothing

   tyArgs2 :: Type -> (Type,Type)
   tyArgs2 (tyArgs2_maybe -> Just ab) = ab
   tyArgs2 ty = pprPanic "tyArgs2" (ppr ty)

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
                  (ppr beforeTy <+> "vs" <+> ppr afterTy <+> "in"))
              (oops "Lint")
          (lintExpr dflags (varSetElems (exprFreeVars after)) after)

   transCatOp :: ReExpr
   transCatOp orig@(collectArgs -> (Var v, Type (isFunCat -> True) : rest))
     | isFunCat cat = Just orig
     | otherwise
     = let -- Track how many regular (non-TyCo, non-pred) arguments we've seen
           addArg :: Maybe CoreExpr -> CoreExpr -> Maybe CoreExpr
           addArg Nothing _ = Nothing
           addArg (Just e) arg
             | isTyCoArg arg
             = Just (e `App` arg)
             | isPred arg
             = onDictMaybe e  --  fails gracefully
             | FunTy dom _ <- exprType e
             = -- TODO: logic to sort out cat vs non-cat args.
               -- We currently don't have both.
               Just (e `App` (if isCatTy dom then mkCcc else id) arg)
             | otherwise
             = Nothing
           final = foldl addArg (Just (Var v `App` Type cat)) rest
       in
         -- Make sure we have no remaining cat arguments
         -- dtrace "transCatOp final" (ppr final) $
         case final of
           Just e' | not (hasCatArg e') -> Just e'
           _                            -> Nothing
   transCatOp _ = Nothing

   isFunCat :: Type -> Bool
   isFunCat (TyConApp tc []) = isFunTyCon tc
   isFunCat _                = False

   isCatTy :: Type -> Bool
   isCatTy (splitAppTy_maybe -> Just (splitAppTy_maybe -> Just (k,_),_)) =
     k `eqType` cat
   isCatTy _ = False

   hasCatArg :: CoreExpr -> Bool
   hasCatArg (exprType -> FunTy t _) = isCatTy t
   hasCatArg _                       = False

   reCat :: ReExpr
   reCat = transCatOp

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
substFriendly catClosed rhs =
     not (liftedExpr rhs)
  || incompleteCatOp rhs
  || (isTrivial rhs)
  || isFunTy ty && not catClosed
  || isIntegerTy ty -- TODO: replace with something more general
 where
   ty = exprType rhs

-- Adapted from exprIsTrivial in CoreUtils. This version considers dictionaries
-- trivial as well as application of exl/exr.
isTrivial :: CoreExpr -> Bool
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

incompleteCatOp e@(collectArgs -> (Var _v, Type (TyConApp (isFunTyCon -> True) []) : _rest))
  = isFunTy (exprType e)
incompleteCatOp _ = False

catModule :: String
catModule = "ConCat.AltCat"

repModule :: String
repModule = "ConCat.Rep"

boxModule :: String
boxModule = "ConCat.Rebox"

extModule :: String
extModule =  "GHC.Exts"

isTrivialCatOp :: CoreExpr -> Bool
isTrivialCatOp (collectArgs -> (Var v,length -> n))
  =    (isSelectorId v && n == 5)  -- exl cat tya tyb dict ok
    || (isAbstReprId v && n == 4)  -- reprCf cat a r repCat
isTrivialCatOp _ = False

isSelectorId :: Id -> Bool
isSelectorId v = fqVarName v `elem` (((catModule ++ ".") ++) <$> ["exl","exr"])

isAbstReprId :: Id -> Bool
isAbstReprId v = fqVarName v `elem` (((catModule ++ ".") ++) <$> ["reprC","abstC"])

pprWithType :: CoreExpr -> SDoc
pprWithType e = ppr e <+> dcolon <+> ppr (exprType e)

cccRuleName :: FastString
cccRuleName = fsLit "toCcc'"

composeRuleName :: FastString
composeRuleName = fsLit "compose/coerce"

cccRules :: Maybe (IORef Int) -> FamInstEnvs -> CccEnv -> ModGuts -> AnnEnv -> [CoreRule]
cccRules steps famEnvs env@(CccEnv {..}) guts annotations =
  [ BuiltinRule { ru_name  = cccRuleName
                , ru_fn    = varName cccV
                , ru_nargs = 4  -- including type args
                , ru_try   = \ dflags inScope _fn ->
                                \ case
                                  _es@(Type k : Type _a : Type _b : arg : _) ->
                                    unsafeLimit steps $
                                      ccc env (ops dflags inScope k) k arg
                                  _args -> Nothing
                }

  -- Are we still using the special composition rules?
  , BuiltinRule { ru_name  = composeRuleName
                , ru_fn    = varName composeV
                , ru_nargs = 8  -- including type args and dicts
                , ru_try   = \ dflags inScope _fn ->
                                \ case
                                  [Type k, Type _b,Type _c, Type _a,_catDict,_ok,g,f] ->
                                       composeR env (ops dflags inScope k) g f
                                  _args -> Nothing
                }

  ]
  where
    ops = mkOps env guts annotations famEnvs

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

-- Find an option "foo=bar" for optName "foo", returning a read of "bar".
parseOpt :: Read a => String -> [CommandLineOption] -> Maybe a
parseOpt optName = listToMaybe . catMaybes . map parse
 where
   parse = fmap read . stripPrefix (optName ++ "=")

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos =
  do dflags <- getDynFlags
     -- Unfortunately, the plugin doesn't work in GHCi. Until fixed,
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
                -- pprTrace "Program binds before ccc" (ppr (mg_binds guts)) $
                do allAnns <- liftIO (prepareAnnotations hsc_env (Just guts))
                   let famEnvs = (pkgFamEnv, mg_fam_inst_env guts)
                       maxSteps = (unsafePerformIO . newIORef) <$>
                                  parseOpt "maxSteps" opts
                   return (on_mg_rules (++ cccRules maxSteps famEnvs env guts allAnns) guts)
              delRule guts = return (on_mg_rules (filter (not . isOurRule)) guts)
              isOurRule r = isBuiltinRule r && ru_name r `elem` [cccRuleName,composeRuleName]

              (pre,post) = splitAt 5 todos  -- guess

              ours = [ CoreDoPluginPass "Ccc insert rule" addRule
                     , CoreDoSimplify 7 mode
                     , CoreDoPluginPass "Ccc remove rule" delRule
                     , CoreDoPluginPass "Flag remaining ccc calls" (flagCcc env)
                     ]

          return $ pre ++ ours ++ post
 where
   flagCcc :: CccEnv -> PluginPass
   flagCcc (CccEnv {..}) guts
     | Seq.null remaining = return guts
     | otherwise = pprTrace "ccc residuals:" (ppr (toList remaining)) $
                   return guts
    where
      remaining :: Seq CoreExpr
      remaining = collectQ cccArgs (mg_binds guts)

      cccArgs :: CoreExpr -> Seq CoreExpr
      cccArgs c@(unVarApps -> Just (v,_tys,[_])) | v == cccV = Seq.singleton c
      cccArgs _                                              = mempty

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

      findCatId   = findId catModule
      findRepTc   = findTc repModule
      findBoxId   = findId boxModule
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
  coerceV     <- findCatId "coerceC"
  bottomCV    <- findCatId "bottomC"
  cccV        <- findCatId "toCcc'"
  uncccV      <- findCatId "unCcc'"
  fmapV       <- findCatId "fmapC"
  fmapTV      <- findCatId "fmapT"
  casePairTV  <- findCatId "casePairT"
  casePairLTV <- findCatId "casePairLT"
  casePairRTV <- findCatId "casePairRT"
  repTc       <- findRepTc "Rep"
  prePostV    <- findId "ConCat.Misc" "~>"
  boxIV       <- findBoxId "boxI"
  boxFV       <- findBoxId "boxF"
  boxDV       <- findBoxId "boxD"
  boxIBV      <- findBoxId "boxIB"
  ifEqIntHash <- findBoxId "ifEqInt#"
  tagToEnumV  <- findId "GHC.Prim" "tagToEnum#"
  bottomV     <- findId "ConCat.Misc" "bottom"
  inlineV     <- findExtId "inline"

  ruleBase <- eps_rule_base <$> (liftIO $ hscEPS hsc_env)
  let boxers = Map.fromList [(intTyCon,boxIV),(doubleTyCon,boxDV),(floatTyCon,boxFV)]

  when (isBottomingId cccV) $
    pprPanic "isBottomingId cccV" empty
  return (CccEnv { .. })

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

-- With dot
nameModuleName_maybe :: Name -> Maybe String
nameModuleName_maybe =
  fmap (moduleNameString . moduleName) . nameModule_maybe

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

isPred :: CoreExpr -> Bool
isPred e  = not (isTyCoArg e) && isPredTy' (exprType e)

pattern FunTy :: Type -> Type -> Type
pattern FunTy dom ran <- (splitFunTy_maybe -> Just (dom,ran))
 where FunTy = mkFunTy

-- TODO: Replace explicit uses of splitFunTy_maybe

-- TODO: Look for other useful pattern synonyms

pattern FunCo :: Role -> Coercion -> Coercion -> Coercion
pattern FunCo r dom ran <- TyConAppCo r (isFunTyCon -> True) [dom,ran]
 where FunCo = mkFunCo

onAltRhs :: Unop CoreExpr -> Unop CoreAlt
onAltRhs f (con,bs,rhs) = (con,bs,f rhs)

-- TODO: Should I unfold (inline application head) earlier? Doing so might
-- result in much simpler generated code by avoiding many beta-redexes. If I
-- do, take care not to inline "primitives". I think it'd be fairly easy.

-- Try to inline an identifier.
-- TODO: Also class ops
inlineId :: Id -> Maybe CoreExpr
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

pairTy :: Binop Type
pairTy a b = mkBoxedTupleTy [a,b]

etaReduce_maybe :: ReExpr
etaReduce_maybe (Lam x (App e (Var y))) | x == y && not (x `isFreeIn` e) = Just e
etaReduce_maybe _ = Nothing

-- The function category
funCat :: Cat
funCat = mkTyConTy funTyCon

liftedExpr :: CoreExpr -> Bool
liftedExpr e = not (isTyCoDictArg e) && liftedType (exprType e)

liftedType :: Type -> Bool
liftedType = isLiftedTypeKind . typeKind

pattern PairVar :: CoreExpr
pattern PairVar <- Var (isPairVar -> True)

isPairVar :: Var -> Bool
isPairVar = (== "GHC.Tuple.(,)") . fqVarName

isMonoTy :: Type -> Bool
isMonoTy (TyConApp _ tys)      = all isMonoTy tys
isMonoTy (AppTy u v)           = isMonoTy u && isMonoTy v
isMonoTy (ForAllTy (Anon u) v) = isMonoTy u && isMonoTy v
isMonoTy (LitTy _)             = True
isMonoTy _                     = False

-- | Number of occurrences of a given Id in an expression.
-- Gives a large value if the Id appears under a lambda.
idOccs :: Bool -> Id -> CoreExpr -> Int
idOccs penalizeUnderLambda x = go
 where
   lamFactor | penalizeUnderLambda = 100
             | otherwise           = 1
   go (Type _)                 = 0
   go (Coercion _)             = 0
   go _e@(exprType -> isPredTy' -> True) = 0
   go (Lit _)                  = 0
   go (Var y)      | y == x    = 1
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
   goAlt (_,ys,rhs) | x `elem` ys = 0
                    | otherwise   = go rhs

-- GHC's isPredTy says "no" to unboxed tuples of pred types.
isPredTy' :: Type -> Bool
isPredTy' ty = isPredTy ty || others ty
 where
   others (splitTyConApp_maybe -> Just (tc,tys)) =
     -- The first half of the arguments are representation types ('PtrRepLifted)
     isUnboxedTupleTyCon tc && all isPredTy' (drop (length tys `div` 2) tys)
   others _ = False

altRhs :: Alt b -> Expr b
altRhs (_,_,rhs) = rhs

hasTyCon :: TyCon -> Type -> Bool
hasTyCon tc (tcSplitTyConApp_maybe -> Just (tc', _)) = tc' == tc
hasTyCon _ _ = False

-- Experiment: wrap a stateful counter around a Maybe.
unsafeLimit :: Maybe (IORef Int) -> Unop (Maybe a)
unsafeLimit Nothing = id
unsafeLimit (Just r) = \ a -> unsafePerformIO $
  do n <- readIORef r
     if n == 0 then
       return Nothing
      else
       do writeIORef r (n-1)
          return a
{-# NOINLINE unsafeLimit #-}
