{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ParallelListComp #-}

{-# OPTIONS_GHC -Wall #-}
-- {-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
-- {-# OPTIONS_GHC -fdefer-typed-holes #-} -- TEMP

-- | Generate GLSL code from a circuit graph

module ConCat.GLSL (Anim,CAnim,genGlsl) where

import Control.Monad (when)
import Data.Char (isAlphaNum)
import Data.List (sort)
import qualified Data.Set as S
import qualified Data.Map as M
import System.Directory (createDirectoryIfMissing)
-- import Debug.Trace (trace)

import Text.ParserCombinators.Parsec (runParser,ParseError)
import Text.PrettyPrint.HughesPJClass -- (Pretty,prettyShow)
import Language.GLSL.Syntax
import Language.GLSL.Pretty ()
import Language.GLSL.Parser hiding (parse)

import ConCat.Misc ((:*),R)
import qualified ConCat.Category as C
import ConCat.Circuit (Comp(..),Bus(..),busTy,(:>),mkGraph,pattern CompS)
import qualified ConCat.Circuit as C

type Image = R :* R -> Bool     -- TODO: color etc

type  Anim = R -> Image
type CAnim = R :> Image

showGraph :: Bool
showGraph = False -- True

genGlsl :: String -> CAnim -> IO ()
genGlsl name anim =
  do when showGraph $ putStrLn $ "genGlsl: Graph " ++ show comps
     createDirectoryIfMissing False outDir
     writeFile (outDir++"/"++name++".frag") (prettyShow fundef ++ "\n")
 where
   comps = sort (mkGraph (C.uncurry anim))
   fundef = fromComps (tweakName name) comps
   outDir = "out"
   tweakName = map tweakChar
   tweakChar c | isAlphaNum c = c
               | otherwise    = '_'

constExpr :: C.Ty -> String -> Expr
constExpr C.Bool   = BoolConstant        . read
constExpr C.Int    = IntConstant Decimal . read
constExpr C.Float  = FloatConstant       . read
constExpr C.Double = FloatConstant       . read
constExpr ty = error ("ConCat.GLSL.constExpr: unexpected literal type: " ++ show ty)

fromComps :: String -> [Comp] -> ExternalDeclaration
-- fromComps _ comps | trace ("fromComps " ++ show comps) False = undefined
fromComps name comps
  | (CompS _ "In" [] inputs,mid, CompS _ "Out" [res] _) <- splitComps comps
  , let (bindings, assignments) = accumComps (uses mid) mid
  = funDef Bool name (paramDecl <$> inputs)
           (map (uncurry initBus) assignments
            ++ [Return (Just (bindings M.! res))])
fromComps name comps = error ("ConCat.GLSL.fromComps: unexpected subgraph comp " ++ show (name,comps))

-- Count uses of each output
uses :: [Comp] -> M.Map Bus Int
uses = M.unionsWith (+) . map uses1

-- Uses map for a single component
uses1 :: Comp -> M.Map Bus Int
uses1 (CompS _ _ ins _) = M.unionsWith (+) (flip M.singleton 1 <$> ins)
uses1 comp = error ("ConCat.GLSL.uses1: unexpected subgraph comp " ++ show comp)

nestExpressions :: Bool
nestExpressions = True -- False

-- Given usage counts, generate delayed bindings and assignments
accumComps :: M.Map Bus Int -> [Comp] -> (M.Map Bus Expr, [(Bus,Expr)])
-- accumComps counts | trace ("accumComps: counts = " ++ show counts) False = undefined
accumComps counts = go M.empty
 where
   -- Generate bindings for outputs used more than once,
   -- and accumulate a map of the others.
   go :: M.Map Bus Expr -> [Comp] -> (M.Map Bus Expr, [(Bus,Expr)])
   -- go saved comps | trace ("accumComps/go " ++ show saved ++ " " ++ show comps) False = undefined
   go saved [] = (saved, [])
   go saved (c@(CompS _ _ _ [o]) : comps) 
     | Just n <- M.lookup o counts, (n > 1 || not nestExpressions) =
         let (saved',bindings') = go saved comps in
           (saved', (o,e) : bindings')
     | otherwise = go (M.insert o e saved) comps
    where
      e = compExpr saved c
   go _ c = error ("ConCat.GLSL.accumComps: oops: " ++ show c)

compExpr :: M.Map Bus Expr -> Comp -> Expr
compExpr _ (CompS _ str [] [Bus _ _ ty]) = constExpr ty str
compExpr saved (CompS _ prim ins _) = app prim (inExpr <$> ins)
 where
   inExpr :: Bus -> Expr
   inExpr b | Just e <- M.lookup b saved = e
            | otherwise = bToE b
compExpr _ comp = error ("ConCat.GLSL.compExpr: unexpected subgraph comp " ++ show comp)

busType :: Bus -> TypeSpecifierNonArray
busType = glslTy . busTy

initBus :: Bus -> Expr -> Statement
initBus b e = initDecl (busType b) (varName b) e

glslTy :: C.Ty -> TypeSpecifierNonArray
glslTy C.Int    = Int
glslTy C.Bool   = Bool
glslTy C.Float  = Float
glslTy C.Double = Float
glslTy ty = error ("ConCat.GLSL.glslTy: unsupported type: " ++ show ty)

varName :: Bus -> String
varName (Bus 0 n _) = "in" ++ show n
varName (Bus c 0 _) = "v" ++ show c
varName b = error ("ConCat.GLSL.varName unexpected " ++ show b)

-- All actual primitives have exactly one output. The fake In primitive can have
-- any number, and the fake Out primitive has none. I think I'd like to
-- eliminate those fake prims, but I'm not ready to rule out multi-output
-- primitives.

app :: String -> [Expr] -> Expr
app nm es = go nm
 where
   go "not"    = app1 UnaryNot
   go "&&"     = app2 And
   go "||"     = app2 Or 
   go "<"      = app2 Lt 
   go ">"      = app2 Gt 
   go "<="     = app2 Lte
   go ">="     = app2 Gte
   go "=="     = app2 Equ
   go "/="     = app2 Neq
   go "negate" = app1 UnaryNegate
   go "+"      = app2 Add
   go "-"      = app2 Sub
   go "−"      = app2 Sub
   go "*"      = app2 Mul
   go "/"      = app2 Div
   go "mod"    = app2 Mod
   go "xor"    = app2 Neq
   go fun | fun `S.member` knownFuncs = funcall fun es
          | otherwise = error ("ConCat.GLSL.app: not supported: " ++ show (fun,es))
   err str = error ("app " ++ nm ++ ": expecting " ++ str ++ " but got " ++ show es)
   app1 op | [e] <- es = op e
           | otherwise = err "one argument"
   app2 op | [e1,e2] <- es = op e1 e2
           | otherwise = err "two arguments"

knownFuncs :: S.Set String
knownFuncs = S.fromList ["exp","cos","sin"]

bToE :: Bus -> Expr
bToE = Variable . varName

-- Extract input, middle, output components. 
splitComps :: [Comp] -> (Comp,[Comp],Comp)
splitComps (i@(CompS _ "In" [] _)
            : (unsnoc -> (mid,o@(CompS _ "Out" _ [])))) = (i,mid,o)
splitComps comps = error ("ConCat.GLSL.splitComps: Oops: " ++ show comps)

unsnoc :: [a] -> ([a],a)
unsnoc as = (mid,o) where (mid,[o]) = splitAt (length as - 1) as

{--------------------------------------------------------------------
    GLSL syntax utilities
--------------------------------------------------------------------}

-- For experiments. Makes it easy to see syntax representations.
_parse :: P a -> String -> Either ParseError a
_parse p = runParser p S "GLSL"

initDecl :: TypeSpecifierNonArray -> String -> Expr -> Statement
initDecl ty var e =
 DeclarationStatement (
  InitDeclaration (
      TypeDeclarator (
          FullType Nothing (TypeSpec Nothing (TypeSpecNoPrecision ty Nothing))))
  [InitDecl var Nothing (Just e)])

paramDecl :: Bus -> ParameterDeclaration
paramDecl b =
  ParameterDeclaration Nothing Nothing 
    (TypeSpec Nothing (TypeSpecNoPrecision (busType b) Nothing))
    (Just (varName b,Nothing))

funDef :: TypeSpecifierNonArray -> String -> [ParameterDeclaration]
       -> [Statement] -> ExternalDeclaration
funDef resultTy name params statements =
  FunctionDefinition (
    FuncProt (FullType Nothing
              (TypeSpec Nothing (TypeSpecNoPrecision resultTy Nothing)))
             name params)
    (Compound statements)

funcall :: String -> [Expr] -> Expr
funcall fun args = FunctionCall (FuncId fun) (Params args)

-- funcall1 :: String -> Expr -> Expr
-- funcall1 fun = funcall fun . (:[])

#if 0
selectField :: String -> String -> Expr
selectField var field = FieldSelection (Variable var) field

assign :: String -> Expr -> Statement
assign v e = ExpressionStatement (Just (Equal (Variable v) e))
#endif
