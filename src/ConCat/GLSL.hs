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

module ConCat.GLSL (CAnim,genGlsl) where

import Control.Monad (when)
import Data.Ord (comparing)
import Data.Char (isAlphaNum)
import Data.List (sortBy)
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
import ConCat.Circuit (CompS(..),PinId(..),Bus(..),(:>), mkGraph, unitize)
import qualified ConCat.Circuit as C

type CAnim = R :* (R :* R) :> Bool

showGraph :: Bool
showGraph = True -- False

genGlsl :: String -> CAnim -> IO ()
genGlsl name0 circ =
  do when showGraph $ putStrLn $ "genGlsl: Graph " ++ show g
     createDirectoryIfMissing False outDir
     writeFile (outDir++"/"++name++".frag") (prettyShow fundef ++ "\n")
 where
   g@(name,compDepths,_report) = mkGraph name0 (unitize circ)
   comps = sortBy (comparing C.compId) (M.keys compDepths)
   fundef = fromComps' (tweakName name) comps
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

fromComps' :: String -> [CompS] -> ExternalDeclaration
-- fromComps' _ comps | trace ("fromComps' " ++ show comps) False = undefined
fromComps' name comps =
  funDef Bool name (paramDecl <$> inputs)
         (map (uncurry initBus) assignments
          ++ [Return (Just (bindings M.! res))])
 where
   (CompS _ "In" [] inputs _,mid, CompS _ "Out" [Bus res _] _ _) = splitComps comps
   (bindings, assignments) = accumComps (uses mid) mid

-- Count uses of each output
uses :: [CompS] -> M.Map PinId Int
uses = M.unionsWith (+) . map uses1

-- Uses map for a single component
uses1 :: CompS -> M.Map PinId Int
uses1 (CompS _ _ ins _ _) = M.unionsWith (+) [M.singleton i 1 | Bus i _ <- ins]

nestExpressions :: Bool
nestExpressions = True -- False

-- Given usage counts, generate delayed bindings and assignments
accumComps :: M.Map PinId Int -> [CompS] -> (M.Map PinId Expr, [(Bus,Expr)])
-- accumComps counts | trace ("accumComps: counts = " ++ show counts) False = undefined
accumComps counts = go M.empty
 where
   -- Generate bindings for outputs used more than once,
   -- and accumulate a map of the others.
   go :: M.Map PinId Expr -> [CompS] -> (M.Map PinId Expr, [(Bus,Expr)])
   -- go saved comps | trace ("accumComps/go " ++ show saved ++ " " ++ show comps) False = undefined
   go saved [] = (saved, [])
   go saved (c@(CompS _ _ _ [b@(Bus o _)] _) : comps) 
     | Just n <- M.lookup o counts, (n > 1 || not nestExpressions) =
         let (saved',bindings') = go saved comps in
           (saved', (b,e) : bindings')
     | otherwise = go (M.insert o e saved) comps
    where
      e = compExpr saved c
   go _ c = error ("ConCat.GLSL.accumComps: oops: " ++ show c)

compExpr :: M.Map PinId Expr -> CompS -> Expr
compExpr _ (CompS _ str [] [Bus _ ty] _) = constExpr ty str
compExpr saved (CompS _ prim ins _ _) = app prim (inExpr <$> ins)
 where
   inExpr :: Bus -> Expr
   inExpr b@(Bus i _) | Just e <- M.lookup i saved = e
                      | otherwise = bToE b

initBus :: Bus -> Expr -> Statement
initBus (Bus pid ty) e = initDecl (glslTy ty) (varName pid) e

glslTy :: C.Ty -> TypeSpecifierNonArray
glslTy C.Int    = Int
glslTy C.Bool   = Bool
glslTy C.Float  = Float
glslTy C.Double = Float
glslTy ty = error ("ConCat.GLSL.glslTy: unsupported type: " ++ show ty)

varName :: PinId -> String
varName (PinId c n) = "v" ++ "_" ++ show c ++ "_" ++ show n

app :: String -> [Expr] -> Expr
app "¬"      [e]     = UnaryNot e
app "∧"      [e1,e2] = And e1 e2
app "∨"      [e1,e2] = Or  e1 e2
app "<"      [e1,e2] = Lt  e1 e2
app ">"      [e1,e2] = Gt  e1 e2
app "≤"      [e1,e2] = Lte e1 e2
app "≥"      [e1,e2] = Gte e1 e2
app "≡"      [e1,e2] = Equ e1 e2
app "≢"      [e1,e2] = Neq e1 e2
app "negate" [e]     = UnaryNegate e
app "+"      [e1,e2] = Add e1 e2
app "-"      [e1,e2] = Sub e1 e2
app "×"      [e1,e2] = Mul e1 e2
app "÷"      [e1,e2] = Div e1 e2
app "mod"    [e1,e2] = Mod e1 e2
app fun args | fun `S.member` knownFuncs = funcall fun args
             | otherwise = error ("ConCat.GLSL.app: not supported: " ++ show (fun,args))

knownFuncs :: S.Set String
knownFuncs = S.fromList ["exp","cos","sin"]

bToE :: Bus -> Expr
bToE (Bus pid _ty) = Variable (varName pid)

-- Extract input, middle, output components. 
splitComps :: [CompS] -> (CompS,[CompS],CompS)
splitComps (i@(CompS 0 "In" [] _ _)
            : (unsnoc -> (mid,o@(CompS _ "Out" _ [] _)))) = (i,mid,o)
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
paramDecl (Bus pid ty) =
  ParameterDeclaration Nothing Nothing 
    (TypeSpec Nothing (TypeSpecNoPrecision (glslTy ty) Nothing))
    (Just (varName pid,Nothing))

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
