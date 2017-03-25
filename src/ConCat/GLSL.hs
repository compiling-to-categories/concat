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

import Data.Ord (comparing)
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

type Im = Float :* Float :> Bool

type OkIm a b = (a ~ (Float :* Float), b ~ Bool)

genGlsl :: String -> Im -> IO ()
genGlsl name0 circ =
  do createDirectoryIfMissing False outDir
     writeFile (outDir++"/"++name++".frag")
       (unlines prelude ++ prettyShow statements)
 where
   (name,statements) = fromCirc name0 circ
   outDir = "out"

-- TEMP hack: wire in parameters
prelude :: [String]
prelude =
  [ "uniform float _time;"
  , "varying vec2  _point;"
  , "main () { gl_FragColor = effect(_point.x,_point.y)}"
  , "effect (float x, float y)"
  ]

fromCirc :: String -> Im -> (String,Compound)
fromCirc name0 circ =
  (name, Compound (concat (fromCompS . unCompS <$> (i : mid ++ [o]))))
 where
   (name,compDepths,_report) = mkGraph name0 (unitize circ)
   (i,mid,o) = splitComps (sortBy (comparing C.compNum) (M.keys compDepths))
   unCompS (CompS _ fun ins outs _) = (fun,ins,outs)

#if 0

mkGraph :: Name -> UU -> GraphInfo
type GraphInfo = (Name,CompDepths,Report)
type CompDepths = Map CompS Depth

#endif

#if 0
data ExternalDeclaration =
    -- function declarations should be at top level (page 28)
    FunctionDeclaration FunctionPrototype
  | FunctionDefinition FunctionPrototype Compound
  | Declaration Declaration
  deriving (Show, Eq)

data FunctionPrototype = FuncProt FullType String [ParameterDeclaration]

data FullType = FullType (Maybe TypeQualifier) TypeSpecifier

data TypeSpecifier = TypeSpec (Maybe PrecisionQualifier) TypeSpecifierNoPrecision

data TypeSpecifierNoPrecision = TypeSpecNoPrecision TypeSpecifierNonArray (Maybe (Maybe Expr)) -- constant expression
#endif

fromCompS :: (String,[Bus],[Bus]) -> [Statement]
fromCompS ("In",[],[x,y]) = defXY x y
fromCompS ("Out",[b],[]) = [Return (Just (bToE b))]
fromCompS (prim,ins,[Bus pid ty]) =
  [DeclarationStatement (
    InitDeclaration (TypeDeclarator
                     (FullType Nothing
                      (TypeSpec Nothing
                       (TypeSpecNoPrecision (glslTy ty) Nothing))))
      [InitDecl (varName pid) Nothing (Just (prim `app` ins))])]
fromCompS comp =
  error ("ConCat.GLSL.fromCompS: not supported: " ++ show comp)


glslTy :: C.Ty -> TypeSpecifierNonArray
glslTy C.Int   = Int
glslTy C.Bool  = Bool
glslTy C.Float = Float
glslTy ty = error ("ConCat.GLSL.glslTy: unsupported type: " ++ show ty)

varName :: PinId -> String
varName (PinId n) = "v" ++ show n

pattern BE :: Expr -> Bus
pattern BE e <- (bToE -> e)

pattern BEs :: [Expr] -> [Bus]
pattern BEs es <- (map bToE -> es)

app :: String -> [Bus] -> Expr
app "+" (BEs [e1,e2]) = Add e1 e2
app ">" (BEs [e1,e2]) = Gt  e1 e2
app fun args =
  error ("ConCat.GLSL.app: not supported: " ++ show (fun,args))
  
bToE :: Bus -> Expr
bToE (Bus pid _ty) = Variable (varName pid)

-- Extract input, middle, output components
splitComps :: [CompS] -> (CompS,[CompS],CompS)
splitComps comps | compName i == "In" && compName o == "Out"
                 = (i,mid,o)
 where
   -- In and Out are added last.
   -- TODO: more robust implementation, say via partition.
   (mid,[i,o]) = splitAt (length comps - 2) comps
splitComps comps = error ("ConCat.GLSL.splitComps: Oops: " ++ show comps)

-- For experiments
parse :: P a -> String -> Either ParseError a
parse p = runParser p S "GLSL"

selectField :: String -> String -> Expr
selectField var field = FieldSelection (Variable var) field

initDecl :: TypeSpecifierNonArray -> String -> Expr -> Statement
initDecl ty var e =
 DeclarationStatement (
  InitDeclaration (
      TypeDeclarator (
          FullType Nothing (TypeSpec Nothing (TypeSpecNoPrecision ty Nothing))))
  [InitDecl var Nothing (Just e)])

defXY :: Bus -> Bus -> [Statement]
defXY (Bus x C.Float) (Bus y C.Float) =
  [ initDecl Float (varName v) (selectField "_point" field)
  | v <- [x,y] | field <- ["x","y"]]
defXY bx by = error ("ConCat.GLSL.defXY: oops: " ++ show (bx,by))
