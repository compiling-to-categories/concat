{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-unused-matches #-} -- TEMP

-- | GHC plugin converting to CCC form.

module ConCat.Plugin where

import Control.Arrow (first)
import Control.Applicative (liftA2,(<|>))
import Control.Monad (unless,guard)
import Data.Foldable (toList)
import Data.Maybe (isNothing,isJust,fromMaybe,catMaybes)
import Data.List (isPrefixOf,isSuffixOf,elemIndex,sort)
import Data.Char (toLower)
import Data.Data (Data)
import Data.Generics (GenericQ,mkQ,everything)
import Data.Sequence (Seq)
import qualified Data.Sequence as S
import Data.Map (Map)
import qualified Data.Map as M
import Text.Printf (printf)

import GhcPlugins hiding (substTy,cat)
import Class (classAllSelIds)
import CoreArity (etaExpand)
import CoreLint (lintExpr)
import DynamicLoading
import MkId (mkDictSelRhs)
import Pair (Pair(..))
import PrelNames (leftDataConName,rightDataConName)
import Type (coreView)
import TcType (isIntTy)
import FamInstEnv (normaliseType)
import TyCoRep                          -- TODO: explicit imports
import Unique (mkBuiltinUnique)

import ConCat.Misc (Unop,Binop,Ternop)
import ConCat.Simplify
import ConCat.BuildDictionary

-- Information needed for reification. We construct this info in
-- CoreM and use it in the ccc rule, which must be pure.
data CccEnv = CccEnv { dtrace    :: forall a. String -> SDoc -> a -> a
                     , cccV      :: Id
                     , idV       :: Id
                     , constV    :: Id
                     , forkV     :: Id
                     , applyV    :: Id
                     , composeV  :: Id
                     , curryV    :: Id
                  -- , uncurryV  :: Id
                     , exlV      :: Id
                     , exrV      :: Id
                     , constFunV :: Id
                     , ops       :: OpsMap
                     , hsc_env   :: HscEnv
                     }

-- Map from fully qualified name of standard operation.
type OpsMap = Map String (Var,[Type])

-- Whether to run Core Lint after every step
lintSteps :: Bool
lintSteps = True -- False

type Rewrite a = a -> Maybe a
type ReExpr = Rewrite CoreExpr

-- #define Trying(str) e | dtrace ("Trying " ++ (str)) (e `seq` empty) False -> undefined

#define Trying(str)

#define Doing(str) dtrace "Doing" (text (str)) id $

-- #define Doing(str)

-- Category
type Cat = Type

ccc :: CccEnv -> ModGuts -> DynFlags -> InScopeEnv -> Type -> ReExpr
ccc (CccEnv {..}) guts dflags inScope cat =
  traceRewrite "ccc" $
  (if lintSteps then lintReExpr else id) $
  go
 where
   go :: ReExpr
   go e | dtrace ("go ccc "++pp cat++":") (ppr e) False = undefined
   go (Lam x body) = goLam x (etaReduceN body)
   go (Let (NonRec v rhs) body) | incompleteCatOp rhs =
     Doing("Let substitution")
     go (subst1 v rhs body)
   go (etaReduceN -> reCat -> Just e') =
     Doing("reCat")
     Just e'
   go (Cast e co) =
     -- etaExpand turns cast lambdas into themselves
     Doing("reCatCo")
     -- dtrace "reCatCo" (ppr co <+> text "-->" <+> ppr (reCatCo co)) $
     -- I think GHC is undoing this transformation, so continue eagerly
     -- return (Cast (mkCcc e) (reCatCo co))
     -- pprPanic "ccc" (text "Cast: not yet handled")
     (`Cast` reCatCo co) <$> go e
   -- Temp hack while testing nested ccc calls.
   -- go (etaReduceN -> Var v) = Doing("Wait for unfolding of " ++ fqVarName v)
   --                            Nothing
   go (unfoldMaybe -> Just e') =
     Doing("unfold")
     return (mkCcc e')
   go (collectArgs -> (Var v,_)) | waitForVar =
     Doing("Wait for unfolding of " ++ fqVarName v)
     Nothing
    where
      -- Expand later
      waitForVar = fqVarName v /= "GHC.Tuple.(,)"
   go e = dtrace "go etaExpand to" (ppr (etaExpand 1 e)) $
          go (etaExpand 1 e)
          -- return $ mkCcc (etaExpand 1 e)
   -- TODO: If I don't etaReduceN, merge goLam back into the go Lam case.
   -- goLam x body | dtrace "go ccc:" (ppr (Lam x body)) False = undefined
   -- go _ = Nothing
   goLam x body = case body of
     -- Trying("constant")
     Trying("Id")
     Var y | x == y -> Doing("Id")
                       return (mkId cat xty)
     Trying("constFun catFun")
     Var _ | isFunTy bty
           , Just e'  <- catFun body
           , Just e'' <- (mkConstFun cat xty e')
           -> Doing("Const catFun")
              return e''
     Trying("Const")
     _ | isConst
       , not isFun
       , Just e' <- mkConst cat xty body
       -> Doing("Const")
         return e'                               
     -- TODO: combine transCatOp and transCatOp.
     -- TODO: handle isConst and isFun via mkConstFun and ccc, but beware cycles.
     Trying("Category operation.")
     _ | isConst
       , Just e'' <- mkConstFun cat xty =<< transCatOp body
       -> Doing("Category operation")
          return e''
     -- Take care not to break up a ccc call as if a regular App
     (collectArgs -> (Var ((== cccV) -> True),_)) ->
       Doing("Postponing ccc-of-ccc")
       Nothing
     Trying("Pair")
     (collectArgs -> (Var (fqVarName -> "GHC.Tuple.(,)"),(Type _ : Type _ : rest)))
       | dtrace "Pair" (ppr rest) False -> undefined
       | [u,v] <- rest ->
          Doing("Pair")
          -- dtrace "Pair test" (ppr (u,v)) $
          return (mkFork cat (mkCcc (Lam x u)) (mkCcc (Lam x v)))
       | otherwise ->
          Doing("Pair eta-expand")
          goLam x (etaExpand (2 - length rest) body)
     Trying("App")
     -- (\ x -> U V) --> apply . (\ x -> U) &&& (\ x -> V)
     u `App` v | liftedExpr v ->
       Doing("App")
       return $ mkCompose cat
                  (mkApply cat vty bty)
                  (mkFork cat (mkCcc (Lam x u)) (mkCcc (Lam x v)))
      where
        vty = exprType v
     Trying("unfold")
     -- Only unfold applications if no argument is a regular value
     e | Just e' <- unfoldMaybe e -> -- lexical oddity
                                     Doing("unfold")
                                     return (mkCcc (Lam x e'))
                                     -- goLam x e'
     Trying("Let")
     Let (NonRec v rhs) body' | liftedExpr rhs ->
       if incompleteCatOp rhs then
         Doing("Let substitution")
         goLam x (subst1 v rhs body')
       else
         Doing("Let")
         -- Convert back to beta-redex. goLam, so GHC can't re-let.
         goLam x (Lam v body' `App` rhs)
     Trying("Lam")
     Lam y e ->
       -- (\ x -> \ y -> U) --> curry (\ z -> U[fst z/x, snd z/y])
       Doing("Lam")
       return $ mkCurry cat (mkCcc (Lam z (subst sub e)))
      where
        yty = varType y
        z = freshId (exprFreeVars e) zName (pairTy xty yty)
        zName = uqVarName x ++ "_" ++ uqVarName y
        sub = [(x,mkEx funCat exlV (Var z)),(y,mkEx funCat exrV (Var z))]
        -- TODO: consider using fst & snd instead of exl and exr here
     Trying("Case of product")
     e@(Case scrut wild _rhsTy [(DataAlt dc, [a,b], rhs)])
         | isBoxedTupleTyCon (dataConTyCon dc) ->
       -- To start, require v to be unused. Later, extend.
       if not (isDeadBinder wild) then
            pprPanic "ccc: product case with live wild var (not yet handled)" (ppr e)
       else
          Doing("Case of product")
          --    \ x -> case scrut of _ { (a, b) -> rhs }
          -- == \ x -> (\ (a,b) -> rhs) scrut
          -- == \ x -> (\ c -> rhs[a/exl c, b/exr c) scrut
          -- TODO: refactor with Lam case
          let c     = freshId (exprFreeVars e) cName (exprType scrut)  -- (pairTy (varTy a) (varTy b))
              cName = uqVarName a ++ "_" ++ uqVarName b
              sub   = [(a,mkEx funCat exlV (Var c)),(b,mkEx funCat exrV (Var c))]
          in
            return (mkCcc (Lam x (App (Lam c (subst sub rhs)) scrut)))
     -- Give up
     _e -> dtrace "ccc" ("Unhandled:" <+> ppr _e) $
           Nothing
    where
      xty = varType x
      bty = exprType body
      isConst = not (isFreeIn x body)
      isFun = isFunTy bty
   reCatCo :: Unop Coercion
   -- reCatCo co | dtrace "reCatCo" (ppr co) False = undefined
   reCatCo (splitAppCo_maybe -> Just (splitAppCo_maybe -> Just (_,a),b)) =
     mkAppCos (mkRepReflCo cat) [a,b]
   reCatCo (co1 `TransCo` co2) = reCatCo co1 `TransCo` reCatCo co2
   reCatCo co = pprPanic "ccc reCatCo: unhandled form" (ppr co)
   unfoldMaybe :: ReExpr
   unfoldMaybe e | (Var v, _) <- collectArgsPred isTyCoDictArg e
                 , isNothing (catFun (Var v))
                 = onExprHead ({-traceRewrite "inlineMaybe"-} inlineMaybe) e
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
   noDictErr :: SDoc -> Maybe a -> a
   noDictErr doc =
     fromMaybe (pprPanic "ccc - couldn't build dictionary for" doc)
   onDictMaybe :: CoreExpr -> Maybe CoreExpr
   onDictMaybe e | Just (ty,_) <- splitFunTy_maybe (exprType e)
                 , isPredTy ty =
                     App e <$> buildDictMaybe ty
                 | otherwise = pprPanic "ccc / onDictMaybe: not a function from pred"
                                 (pprWithType e)
   onDict :: Unop CoreExpr
   onDict f = noDictErr (pprWithType f) (onDictMaybe f)
   buildDictMaybe :: Type -> Maybe CoreExpr
   buildDictMaybe ty = simplifyE dflags False <$>
                       buildDictionary hsc_env dflags guts inScope ty
   -- buildDict :: Type -> CoreExpr
   -- buildDict ty = noDictErr (ppr ty) (buildDictMaybe ty)
   catOp :: Cat -> Var -> [Type] -> CoreExpr
   -- catOp k op tys | dtrace "catOp" (ppr (k,op,tys)) False = undefined
   catOp k op tys = onDict (Var op `mkTyApps` (k : tys))
   -- TODO: refactor catOp and catOpMaybe when the dust settles
   -- catOp :: Cat -> Var -> CoreExpr
   -- catOp k op = catOp k op []
   catOpMaybe :: Cat -> Var -> [Type] -> Maybe CoreExpr
   catOpMaybe k op tys = onDictMaybe (Var op `mkTyApps` (k : tys))
   mkCcc :: Unop CoreExpr  -- Any reason to parametrize over Cat?
   mkCcc e = varApps cccV [cat,a,b] [e]
    where
      (a,b) = splitFunTy (exprType e)
   -- TODO: replace composeV with mkCompose in CccEnv
   -- Maybe other variables as well
   mkId :: Cat -> Type -> CoreExpr
   mkId k ty = onDict (catOp k idV [ty])
               -- onDict (catOp k idV `App` Type ty)
   mkCompose :: Cat -> Binop CoreExpr
   -- (.) :: forall b c a. (b -> c) -> (a -> b) -> a -> c
   mkCompose k g f
     | Just (b,c) <- tyArgs2_maybe (exprType g)
     , Just (a,_) <- tyArgs2_maybe (exprType f)
     = -- mkCoreApps (onDict (catOp k composeV `mkTyApps` [b,c,a])) [g,f]
       mkCoreApps (onDict (catOp k composeV [b,c,a])) [g,f]
     | otherwise = pprPanic "mkCompose:" (pprWithType g <+> text ";" <+> pprWithType f)
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
   mkApply :: Cat -> Type -> Type -> CoreExpr
   mkApply k a b =
     -- apply :: forall {k :: * -> * -> *} {a} {b}. (ClosedCat k, Ok k b, Ok k a)
     --       => k (Prod k (Exp k a b) a) b
     -- onDict (catOp k applyV `mkTyApps` [a,b])
     onDict (catOp k applyV [a,b])
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
   -- mkUncurry :: Cat -> Unop CoreExpr
   -- mkUncurry k e =
   --   -- uncurry :: forall {k :: * -> * -> *} {a} {b} {c}.
   --   --            (ClosedCat k, Ok k c, Ok k b, C1 (Ok k) a)
   --   --         => k a (Exp k b c) -> k (Prod k a b) c
   --   -- onDict (catOp k uncurryV `mkTyApps` [a,b,c]) `App` e
   --   onDict (catOp k uncurryV [a,b,c]) `App` e
   --   -- varApps uncurryV [a,b,c] [e]
   --  where
   --    (tyArgs2 -> (a, tyArgs2 -> (b,c))) = exprType e
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
          (lintExpr dflags (varSetElems (exprFreeVars before)) before)
   catFun :: ReExpr
   catFun (Var v) =
     -- pprTrace "catFun" (text fullName <+> dcolon <+> ppr ty) $
     do (op,tys) <- M.lookup fullName ops
        -- Apply to types and dictionaries, and possibly curry.
        return $ (if twoArgs ty then mkCurry cat else id) (catOp cat op tys)
    where
      ty = varType v
      fullName = fqVarName v
      twoArgs (tyArgs2_maybe -> Just (_,tyArgs2_maybe -> Just _)) = True
      twoArgs _ = False
   catFun _ = Nothing
   reCat :: ReExpr
   reCat = transCatOp <+ catFun
   transCatOp :: ReExpr
   -- transCatOp e | dtrace "transCatOp" (ppr e) False = undefined
   transCatOp (collectArgs -> (Var v, Type _wasCat : rest))
     | True || dtrace "transCatOp v _wasCat rest" (text (fqVarName v) <+> ppr _wasCat <+> ppr rest) True
     , Just (catArgs,nonCatArgs) <- M.lookup (fqVarName v) catOpArities
     -- , dtrace "transCatOp arities" (ppr (catArgs,nonCatArgs)) True
     , length (filter (not . isTyCoDictArg) rest) == catArgs + nonCatArgs
     -- , dtrace "transCatOp" (text "arity match") True
     = let
         -- Track how many regular (non-TyCo, non-pred) arguments we've seen
         addArg :: (Int,CoreExpr) -> CoreExpr -> (Int,CoreExpr)
         addArg (i,e) arg | isTyCoArg arg
                          = -- dtrace "addArg isTyCoArg" (ppr arg)
                            (i,e `App` arg)
                          | isPred arg
                          = -- dtrace "addArg isPred" (ppr arg)
                            (i,onDict e)
                          | otherwise
                          = -- dtrace "addArg otherwise" (ppr (i,arg))
                            -- TODO: logic to sort out cat vs non-cat args.
                            -- We currently don't have both.
                            (i+1,e `App` (if i < catArgs then mkCcc else id) arg)
       in
         Just (snd (foldl addArg (0,Var v `App` Type cat) rest))
   transCatOp _ = -- pprTrace "transCatOp" (text "fail") $
                  Nothing
   incompleteCatOp :: CoreExpr -> Bool
   -- incompleteCatOp e | dtrace "incompleteCatOp" (ppr e) False = undefined
   incompleteCatOp (collectArgs -> (Var v, Type _wasCat : rest))
     | True || dtrace "incompleteCatOp v _wasCat rest" (text (fqVarName v) <+> ppr _wasCat <+> ppr rest) True
     , Just (catArgs,_) <- M.lookup (fqVarName v) catOpArities
     , let seen = length (filter (not . isTyCoDictArg) rest)
     -- , dtrace "incompleteCatOp catArgs" (ppr seen <+> text "vs" <+> ppr catArgs) True
     = seen < catArgs
   incompleteCatOp _ = False
   -- TODO: refactor transCatOp & isPartialCatOp

catModule :: String
catModule = "ConCat.AltCat"

-- For each categorical operation, how many non-cat args (first) and how many cat args (last)
catOpArities :: Map String (Int,Int)
catOpArities = M.fromList $ map (\ (nm,m,n) -> (catModule ++ '.' : nm, (m,n))) $
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
  , ("equal",0,0), ("notEqual",0,0), ("greaterThan",0,0), ("lessThanOrEqual",0,0), ("greaterThanOrEqual",0,0)
  , ("succC",0,0), ("predC",0,0)
  , ("bottomC",0,0)
  , ("ifC",0,0)
  , ("unknownC",0,0)
  , ("reprC",0,0), ("abstC",0,0)
  , ("constFun",1,0)
  ]

-- TODO: also handle non-categorical arguments, as in unitArrow and const. Maybe
-- return a pair of arities to cover non-categorical and categorical arguments.
-- I could also handle these cases specially. Perhaps arity of -1 as a hack.

-- TODO: replace idV, composeV, etc with class objects from which I can extract
-- those variables. Better, module objects, since I sometimes want functions
-- that aren't methods.

-- TODO: consider a mkCoreApps variant that automatically inserts dictionaries.

pprWithType :: CoreExpr -> SDoc
pprWithType e = ppr e <+> dcolon <+> ppr (exprType e)

cccRule :: CccEnv -> ModGuts -> CoreRule
cccRule env guts =
  BuiltinRule { ru_name  = fsLit "ccc"
              , ru_fn    = varName (cccV env)
              , ru_nargs = 4  -- including type args
              , ru_try   = \ dflags inScope _fn ->
                              \ case
                                [Type k, Type _a,Type _b,arg] ->
                                   ccc env guts dflags inScope k arg
                                args -> pprTrace "cccRule ru_try args" (ppr args) $
                                        Nothing
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
                   ++ [CoreDoPluginPass "Flag remaining ccc calls" (flagCcc env)]
 where
   flagCcc :: CccEnv -> PluginPass
   flagCcc (CccEnv {..}) guts
     --  | pprTrace "ccc residuals:" (ppr (toList remaining)) False = undefined
     --  | pprTrace "ccc final:" (ppr (mg_binds guts)) False = undefined
     | S.null remaining = return guts
     | otherwise = pprPanic "ccc residuals:" (ppr (toList remaining))
    where
      remaining :: Seq CoreExpr
      remaining = collect cccArgs (mg_binds guts)
      cccArgs :: CoreExpr -> Seq CoreExpr
      -- unVarApps :: CoreExpr -> Maybe (Id,[Type],[CoreExpr])
      -- ccc :: forall k a b. (a -> b) -> k a b
      cccArgs c@(unVarApps -> Just (v,_tys,[_])) | v == cccV = S.singleton c
      cccArgs _                                              = mempty
      -- cccArgs = const mempty  -- for now
      collect :: (Data a, Monoid m) => (a -> m) -> GenericQ m
      collect f = everything mappend (mkQ mempty f)
   -- Extra simplifier pass
   mode = SimplMode { sm_names      = ["Ccc simplifier pass"]
                    , sm_phase      = InitialPhase
                    , sm_rules      = True  -- important
                    , sm_inline     = True -- False -- ??
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
         err = "ccc installation: couldn't find "
               ++ str ++ " in " ++ moduleNameString modu
      lookupTh mkOcc mk modu = lookupRdr (mkModuleName modu) mkOcc mk
      findId      = lookupTh mkVarOcc  lookupId
      findTc      = lookupTh mkTcOcc   lookupTyCon
      findFloatTy = fmap mkTyConTy . findTc floatModule
      findCatId   = findId catModule
      -- findMiscId  = findId "ConCat.Misc"
      -- findTupleId = findId "Data.Tuple"
      -- findRepTc   = findTc "ConCat.Rep"
      -- findBaseId  = findId "GHC.Base"
      -- findCatTc   = findTc catModule
  -- ruleBase <- getRuleBase
  -- catTc       <- findCatTc "Category"
  -- prodTc      <- findCatTc "ProductCat"
  -- closedTc    <- findCatTc "ClosedCat"
  -- constTc     <- findCatTc "ConstCat"
  -- okTc        <- findCatTc "Ok"
  -- dtrace "mkCccEnv: getRuleBase ==" (ppr ruleBase) (return ())
  -- idV      <- findMiscId  "ident"
  idV         <- findCatId  "id"
  constV      <- findCatId  "const"
  -- constV      <- findMiscId  "konst"
  -- composeV <- findMiscId  "comp"
  composeV    <- findCatId  "."
--   exlV        <- findTupleId "fst"
--   exrV        <- findTupleId "snd"
--   forkV       <- findMiscId  "fork"
  exlV        <- findCatId "exl"  -- Experiment: NOINLINE version
  exrV        <- findCatId "exr"
  forkV       <- findCatId "&&&"
  applyV      <- findCatId "apply"
  curryV      <- findCatId "curry"
--   uncurryV    <- findCatId "uncurry"
  constFunV   <- findCatId "constFun"
  -- notV <- findCatId "notC"
  cccV        <- findCatId  "ccc"
  floatT      <- findFloatTy "Float"
  doubleT     <- findFloatTy "Double"
  let mkOp :: (String,(String,String,[Type])) -> CoreM (String,(Var,[Type]))
      mkOp (stdName,(cmod,cop,tyArgs)) =
        do cv <- findId cmod cop
           return (stdName, (cv,tyArgs))
  ops <- M.fromList <$> mapM mkOp (opsInfo (floatT,doubleT))
  -- liftIO (print (opsInfo (floatT,doubleT)))
  -- Experiment: force loading of numeric instances for Float and Double.
  -- Doesn't help.
  -- floatTc <- findTc "GHC.Float" "Float"
  -- liftIO (forceLoadNameModuleInterface hsc_env (text "mkCccEnv")
  --          (getName floatTc))
  -- fiddleV <- findMiscId "fiddle"
  -- rationalToFloatV <- findId "GHC.Float" "rationalToFloat"  -- experiment
  return (CccEnv { .. })

-- Association list 
opsInfo :: (Type,Type) -> [(String,(String,String,[Type]))]
opsInfo fd = [ (hop,(catModule,cop,tyArgs))
             | (cop,ps) <- monoInfo fd
             , (hop,tyArgs) <- ps
             ]

monoInfo :: (Type,Type) -> [(String, [([Char], [Type])])]
monoInfo (floatT,doubleT) =
  [ ("notC",boolOp "not"), ("andC",boolOp "&&"), ("orC",boolOp "||")
  , ("equal", eqOp "==" <$> ifd) 
  , ("notEqual", eqOp "/=" <$> ifd) 
  , ("lessThan", compOps "lt" "<")
  , ("greaterThan", compOps "gt" ">")
  , ("lessThanOrEqual", compOps "le" "<=")
  , ("greaterThanOrEqual", compOps "ge" ">=")
  , ("negateC",numOps "negate"), ("addC",numOps "+")
  , ("subC",numOps "-"), ("mulC",numOps "*")
    -- powIC
  , ("recipC", fracOp "recip" <$> fd)
  , ("divideC", fracOp "/" <$> fd)
  , ("expC", floatingOp "exp" <$> fd)
  , ("cosC", floatingOp "cos" <$> fd)
  , ("sinC", floatingOp "sin" <$> fd)
  --
  , ("succC",[("GHC.Enum.$fEnumInt_$csucc",[intTy])])
  , ("predC",[("GHC.Enum.$fEnumInt_$cpred",[intTy])])
  ]
 where
   ifd = intTy : fd
   fd = [floatT,doubleT]
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
              | otherwise  = floatModule
   fdOp cls op ty = (floatModule++".$f"++cls++pp ty++"_$c"++op,[ty])
   fracOp = fdOp "Fractional"
   floatingOp = fdOp "Floating"

floatModule :: String
floatModule = "ConCat.Float" -- "GHC.Float"

--    fracOp op ty = ("GHC.Float.$fFractional"++pp ty++"_$c"++op,[ty])
--    floatingOp op ty = ("GHC.Float.$fFloating"++pp ty++"_$c"++op,[ty])

-- (==): eqInt, eqFloat, eqDouble
-- (/=): neInt, $fEqFloat_$c/=, $fEqDouble_$c/=
-- (<):  ltI, $fOrdFloat_$c<

-- -- An orphan instance to help me debug
-- instance Show Type where show = pp

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

isPred :: CoreExpr -> Bool
isPred e  = not (isTyCoArg e) && isPredTy (exprType e)

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

isFreeIn :: Var -> CoreExpr -> Bool
v `isFreeIn` e = v `elemVarSet` (exprFreeVars e)

-- exprFreeVars :: CoreExpr -> VarSet
-- elemVarSet      :: Var -> VarSet -> Bool

pairTy :: Binop Type
pairTy a b = mkBoxedTupleTy [a,b]

etaReduce1 :: Unop CoreExpr
etaReduce1 (Lam x (App e (Var y))) | x == y && not (isFreeIn x e) = e
etaReduce1 e = e

etaReduceN :: Unop CoreExpr
etaReduceN (Lam x (etaReduceN -> body')) = etaReduce1 (Lam x body')
etaReduceN e = e

-- etaReduce :: ReExpr
-- etaReduce (collectTyAndValBinders -> ( []
--                                      , vs@(_:_)
--                                      , collectArgs -> (f,args@(_:_))) )
--   | Just rest <- matchArgs vs args = 

-- The function category
funCat :: Cat
funCat = mkTyConTy funTyCon

liftedExpr :: CoreExpr -> Bool
liftedExpr e = not (isTyCoDictArg e) && liftedType (exprType e)

liftedType :: Type -> Bool
liftedType = isLiftedTypeKind . typeKind

