{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ParallelListComp #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP
{-# OPTIONS_GHC -fdefer-typed-holes #-} -- TEMP

-- | 

module ConCat.GLSL where

import Control.Monad (when)
import Data.Ord (comparing)
import Data.Char (isAlphaNum)
import Data.List (sortBy)
import Data.Either (rights)
import qualified Data.Map as M
import System.Directory (createDirectoryIfMissing)

import Text.ParserCombinators.Parsec (runParser,ParseError,GenParser)

import Text.PrettyPrint.HughesPJClass -- (Pretty,prettyShow)
import Language.GLSL.Syntax
import Language.GLSL.Pretty

import Language.GLSL.Parser hiding (parse)

import ConCat.Circuit
  ( CompS(..),compName,PinId(..),Bus(..),GenBuses,(:>)
  , GraphInfo, mkGraph, unitize)
import qualified ConCat.Circuit as C
import ConCat.Misc ((:*))

type CIm = Float :* Float :> Bool

type OkIm a b = (a :> b) ~ CIm

showGraph :: Bool
showGraph = False -- True

genGlsl :: OkIm a b => String -> (a :> b) -> IO ()
genGlsl name0 circ =
  do when showGraph $ putStrLn $ "genGlsl: Graph \n" ++ show g
     createDirectoryIfMissing False outDir
     writeFile (outDir++"/"++name++".frag")
       (prettyShow fundef ++ "\n")
 where
   g@(name,compDepths,_report) = mkGraph name0 (unitize circ)
   comps = sortBy (comparing C.compNum) (M.keys compDepths)
   fundef = fromCompSs (tweakName name) comps
   outDir = "out"
   tweakName = map tweakChar
   tweakChar c | isAlphaNum c = c
               | otherwise    = '_'

fromCompSs :: String -> [CompS] -> ExternalDeclaration
fromCompSs name comps =
  funDef Bool name (paramDecl <$> inputs)
         (fromCompS <$> (mid ++ [o]))
 where
   (CompS _ "In" [] inputs _,mid,o) = splitComps comps

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

fromCompS :: CompS -> Statement
fromCompS (CompS _ "Out" [b] [] _) = Return (Just (bToE b))
fromCompS (CompS _ str [] [b@(Bus _ ty)] _) =
  initBus b (
    case ty of
      C.Bool  -> BoolConstant        (read str)
      C.Int   -> IntConstant Decimal (read str)
      C.Float -> FloatConstant       (read str)
      _ -> error ("ConCat.GLSL.fromCompS: unexpected literal type: " ++ show ty))
fromCompS (CompS _ prim ins [b] _) = initBus b (app prim (bToE <$> ins))
fromCompS comp =
  error ("ConCat.GLSL.fromCompS: not supported: " ++ show comp)

initBus :: Bus -> Expr -> Statement
initBus (Bus pid ty) e = initDecl (glslTy ty) (varName pid) e

assign :: String -> Expr -> Statement
assign v e = ExpressionStatement (Just (Equal (Variable v) e))

initDecl :: TypeSpecifierNonArray -> String -> Expr -> Statement
initDecl ty var e =
 DeclarationStatement (
  InitDeclaration (
      TypeDeclarator (
          FullType Nothing (TypeSpec Nothing (TypeSpecNoPrecision ty Nothing))))
  [InitDecl var Nothing (Just e)])


glslTy :: C.Ty -> TypeSpecifierNonArray
glslTy C.Int   = Int
glslTy C.Bool  = Bool
glslTy C.Float = Float
glslTy ty = error ("ConCat.GLSL.glslTy: unsupported type: " ++ show ty)

varName :: PinId -> String
varName (PinId n) = "v" ++ show n

app :: String -> [Expr] -> Expr
app "¬"      [e]     = UnaryNot e
app "∧"      [e1,e2] = And e1 e2
app "∨"      [e1,e2] = Or e1 e2
app "<"      [e1,e2] = Lt e1 e2
app ">"      [e1,e2] = Gt e1 e2
app "≤"      [e1,e2] = Lte e1 e2
app "≥"      [e1,e2] = Gte e1 e2
app "≡"      [e1,e2] = Equ e1 e2
app "≢"      [e1,e2] = Neq e1 e2
app "negate" [e]     = UnaryNegate e
app "+"      [e1,e2] = Add e1 e2
app "-"      [e1,e2] = Sub e1 e2
app "×"      [e1,e2] = Mul e1 e2
-- app "div" [e1,e2] = Div e1 e2
-- app "mod" [e1,e2] = Mod e1 e2
app fun args =
  error ("ConCat.GLSL.app: not supported: " ++ show (fun,args))
  
bToE :: Bus -> Expr
bToE (Bus pid _ty) = Variable (varName pid)

unsnoc :: [a] -> ([a],a)
unsnoc as = (mid,o) where (mid,[o]) = splitAt (length as - 1) as

-- Extract input, middle, output components
splitComps :: [CompS] -> (CompS,[CompS],CompS)
splitComps (i@(CompS 0 "In" [] _ _) : (unsnoc -> (mid,o))) = (i,mid,o)
splitComps comps = error ("ConCat.GLSL.splitComps: Oops: " ++ show comps)

-- For experiments
parse :: P a -> String -> Either ParseError a
parse p = runParser p S "GLSL"

selectField :: String -> String -> Expr
selectField var field = FieldSelection (Variable var) field

defXY :: Bus -> Bus -> [Statement]
defXY (Bus x C.Float) (Bus y C.Float) =
  [ initDecl Float (varName v) (selectField "_point" field)
  | v <- [x,y] | field <- ["x","y"]]
defXY bx by = error ("ConCat.GLSL.defXY: oops: " ++ show (bx,by))
