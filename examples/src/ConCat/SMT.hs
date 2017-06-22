{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall #-}

-- | SMT category built on z3. A re-implementation of
-- <https://github.com/jwiegley/z3cat>, which is described at
-- <http://newartisans.com/2017/04/haskell-and-z3/>

module ConCat.SMT (solve,GenBuses,EvalE) where

import Control.Applicative (liftA2)
import Data.List (sort)
import qualified Data.Map as M

import Control.Monad.State (StateT,runStateT,execStateT,get,gets,put,modify,lift)

import Z3.Monad

import ConCat.Circuit (Comp(..),Bus(..),Ty(..),busTy,GenBuses(..),(:>),mkGraph,pattern CompS)

type E = AST

type M = StateT (M.Map Bus E) Z3

busE :: Bus -> M E
busE b = gets (M.! b)

solve :: forall a. (GenBuses a, EvalE a) => (a :> Bool) -> IO (Maybe a)
solve p =
  -- evalZ3With Nothing (opt "MODEL" True) $ do
  evalZ3 $ do
  do is <- genEs (ty @a)
     m  <- execStateT (mapM_ addComp mids) (M.fromList (busesIn `zip` is))
     assert (m M.! res)
     -- check and get solution
     snd <$> withModel (`evalEs` is)
 where
   (CompS _ "In" [] busesIn,mids, CompS _ "Out" [res] _) =
     splitComps (sort (mkGraph p))

addComp :: Comp -> M ()
addComp (CompS _ prim ins [o]) = do res <- add
                                    modify (M.insert o res)
 where
   add | null ins = lift (constExpr (busTy o) prim)
       | otherwise = do es  <- mapM busE ins
                        lift (app prim es)
addComp comp = error ("ConCat.SMT.addComp: unexpected subgraph comp " ++ show comp)

constExpr :: Ty -> String -> Z3 E
constExpr Bool    = mkBool    . read
constExpr Int     = mkIntNum  . read @Int
constExpr Float   = mkRealNum . read @Float
constExpr Double  = mkRealNum . read @Double
constExpr t       = error ("ConCat.SMT.constExpr: unexpected literal type: " ++ show t)

app :: String -> [E] -> Z3 E
app nm es =
  case nm of
    "not"    -> app1  mkNot
    "&&"     -> app2l mkAnd
    "||"     -> app2l mkOr
    "<"      -> app2  mkLt
    ">"      -> app2  mkGt
    "<="     -> app2  mkLe
    ">="     -> app2  mkGe
    "=="     -> app2  mkEq
    "/="     -> app2  mkNeq
    "negate" -> app1  mkUnaryMinus
    "+"      -> app2l mkAdd
    "-"      -> app2l mkSub
    "*"      -> app2l mkMul
    "/"      -> app2  mkDiv
    "mod"    -> app2  mkMod
    "xor"    -> app2  mkNeq
    fun      -> error ("ConCat.SMT.app: not supported: " ++ show fun)
 where
   err str = error ("app " ++ nm ++ ": expecting " ++ str ++ " but got " ++ show es)
   app1 op | [e] <- es = op e
           | otherwise = err "one argument"
   app2 op | [e1,e2] <- es = op e1 e2
           | otherwise = err "two arguments"
   app2l op = app2 (\ a b -> op [a,b])

mkNeq :: MonadZ3 z3 => E -> E -> z3 E
mkNeq a b = mkNot =<< mkEq a b

{--------------------------------------------------------------------
    Modified from z3cat
--------------------------------------------------------------------}

genPrim :: (String -> Z3 AST) -> Z3 [E]
genPrim mk = (:[]) <$> mk "x"

genEs :: Ty -> Z3 [E]
genEs Unit       = return []
genEs Bool       = genPrim mkFreshBoolVar
genEs Int        = genPrim mkFreshIntVar
genEs Float      = genPrim mkFreshRealVar
genEs Double     = genPrim mkFreshRealVar
genEs (Prod a b) = liftA2 (++) (genEs a) (genEs b)
genEs t          = error ("ConCat.SMT.genEs: " ++ show t)

-- TODO: Use Seq in place of [] in genEs, and compare efficiency.

type EvalM = StateT [E] Z3

-- Assemble a list of Es into a value.
class EvalE a where evalE :: Model -> EvalM a

evalEs :: EvalE a => Model -> [E] -> Z3 a
evalEs model es = do (a,[]) <- runStateT (evalE model) es
                     return a

-- type EvalAst m a = Model -> AST -> m (Maybe a)

evalPrim :: EvalAst Z3 a' -> (a' -> a) -> Model -> EvalM a
evalPrim ev f m =
  do es <- get
     case es of
       []      -> fail "evalPrim: exhausted ASTs"
       (e:es') -> do Just a' <- lift (ev m e)
                     put es'
                     return (f a')

instance EvalE ()     where evalE = evalPrim evalBool (const ())
instance EvalE Bool   where evalE = evalPrim evalBool id
instance EvalE Int    where evalE = evalPrim evalInt  fromInteger
instance EvalE Float  where evalE = evalPrim evalReal fromRational
instance EvalE Double where evalE = evalPrim evalReal fromRational

instance (EvalE a, EvalE b) => EvalE (a,b) where
    evalE m = liftA2 (,) (evalE m) (evalE m)

{--------------------------------------------------------------------
    Copied from GLSL. Move to Circuit.
--------------------------------------------------------------------}

-- Extract input, middle, output components. 
-- TODO: move sort & mkGraph calls here so that we start with a (:>).

splitComps :: [Comp] -> (Comp,[Comp],Comp)
splitComps (i@(CompS _ "In" [] _)
            : (unsnoc -> (mid,o@(CompS _ "Out" _ [])))) = (i,mid,o)
splitComps comps = error ("ConCat.GLSL.splitComps: Oops: " ++ show comps)

unsnoc :: [a] -> ([a],a)
unsnoc as = (mid,o) where (mid,[o]) = splitAt (length as - 1) as
