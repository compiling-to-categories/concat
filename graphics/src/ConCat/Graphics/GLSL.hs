{-# LANGUAGE OverloadedStrings #-}
-- {-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-orphans #-} -- TEMP

-- | Generate GLSL code from a circuit graph

module ConCat.Graphics.GLSL
  ( genHtml,runHtml, Widgets -- ,Widget(..),Widgets(..)
  , unitW, timeW, sliderW, pairW
  ) where

-- import Control.Applicative (liftA2)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import Text.Printf (printf)
import System.Directory (createDirectoryIfMissing)
import qualified System.Info as SI
-- import qualified Debug.Trace as DT

import qualified Data.Aeson as J
import Data.Aeson (ToJSON(..),object,(.=))
import Data.Aeson.Encode.Pretty (encodePretty',Config(..),defConfig,keyOrder)
import qualified Data.Text as T
import qualified Data.ByteString.Lazy.Char8 as BS

import Text.ParserCombinators.Parsec (runParser,ParseError)
import Text.PrettyPrint.HughesPJClass -- (Pretty,prettyShow)
import Language.GLSL.Syntax
import Language.GLSL.Pretty ()
import Language.GLSL.Parser

import ConCat.Misc ((:*),R)
import qualified ConCat.AltCat as A
import ConCat.Circuit
  (Bus(..),GenBuses,busTy,(:>),simpleComp,mkGraph,CompS(..),systemSuccess)
import qualified ConCat.Circuit as C
import ConCat.Graphics.Image (ImageC)

effectHtml :: GenBuses a => Widgets a -> (a :> ImageC) -> String
effectHtml widgets effect = unlines $
  [ "<!DOCTYPE html>" , "<html>" , "<head>"
  , "<meta charset='utf-8'/>"
  , "<link rel=stylesheet href=https://code.jquery.com/ui/1.12.1/themes/ui-lightness/jquery-ui.css>"
  , "<script src=https://code.jquery.com/jquery-1.12.4.js></script>"
  , "<script src=https://code.jquery.com/ui/1.12.1/jquery-ui.js></script>"
  , "<script src=script.js></script>"
  , "<link rel=stylesheet href=style.css>"
  , "</head>"
  , "<body onload='go(uniforms,effect)'>"
  , "<div id=ui></div>"
  , "<canvas id=effect></canvas>"
  , "</body>" , "</html>"
  , "<script>"
  , shaderDefs (glsl widgets effect)
  , "</script>" ]

shaderDefs :: Shader a -> String
shaderDefs (Shader uniforms def) =
  "var uniforms = " ++ BS.unpack (encodePretty' prettyConfig uniforms) ++ ";\n" ++
  "var effect = `\n" ++ prettyShow def ++ "`;"

genHtml :: GenBuses a => String -> Widgets a -> (a :> ImageC) -> IO ()
genHtml name widgets effect =
  do createDirectoryIfMissing False outDir
     let o = outFile name
     writeFile o (effectHtml widgets effect)
     putStrLn ("Wrote " ++ o)

runHtml :: GenBuses a => String -> Widgets a -> (a :> ImageC) -> IO ()
runHtml name widgets effect =
  do genHtml name widgets effect
     systemSuccess $ printf "%s %s" open (outFile name)

outDir :: String
outDir = "out/shaders"

outFile :: String -> String
outFile name = outDir++"/"++name++".html"

open :: String
open = case SI.os of
         "darwin" -> "open"
         "linux"  -> "display" -- was "xdg-open"
         _        -> error "unknown open for OS"

-- TODO: open is also defined in Circuit. Get it from there, or move elsewhere.
-- Move the createDirectoryIfMissing logic there as well.
-- Also the writeFile and putStrLn.

-- Generate JavaScript code for a JSON shader object.
glsl :: GenBuses a => Widgets a -> (a :> ImageC) -> Shader a
glsl widgets = compsShader widgets
             . fmap simpleComp
             . mkGraph
             -- . DT.traceShowId
             . A.uncurry
             -- . DT.traceShowId

-- TODO: Abstract fmap simpleComp . mkGraph, which also appears in Show (a :> b)
-- and SMT.

compsShader :: Widgets a -> [CompS] -> Shader a
-- compsShader comps | trace ("compsShader " ++ show comps) False = undefined
compsShader widgets comps
  | (CompS _ "In" [] inputs,mid, (CompS _ "Out" rgba _)) <- splitComps comps
  , let (bindings, assignments) = accumComps (uses comps) mid
        (uniforms,varyings) = splitAt' 2 inputs
  -- , DT.trace ("compsShader: " ++ show (bindings, assignments, rgba)) True
  = Shader (zipWith busUVar uniforms (flattenWidgets widgets))
      (funDef Vec4 "effect" (paramDecl <$> varyings)
              (map (uncurry initBus) assignments
               ++ [Return (Just (app (error "compsShader: app ty oops") "vec4" (simpleE bindings <$> rgba)))]))
compsShader _ comps =
  error ("ConCat.GLSL.compsShader: unexpected subgraph comp " ++ show comps)

simpleE :: M.Map Bus Expr -> Bus -> Expr
simpleE bindings b = fromMaybe (bToE b) (M.lookup b bindings)

-- Count uses of each output
uses :: [CompS] -> M.Map Bus Int
uses = M.unionsWith (+) . map uses1

-- Uses map for a single component
uses1 :: CompS -> M.Map Bus Int
uses1 (CompS _ _ ins _) = M.unionsWith (+) (flip M.singleton 1 <$> ins)
-- uses1 comp = error ("ConCat.GLSL.uses1: unexpected subgraph comp " ++ show comp)

nestExpressions :: Bool
nestExpressions = True -- False

-- Given usage counts, generate delayed bindings and assignments
accumComps :: M.Map Bus Int -> [CompS] -> (M.Map Bus Expr, [(Bus,Expr)])
-- accumComps counts | DT.trace ("accumComps: counts = " ++ show counts) False = undefined
accumComps counts = go M.empty
 where
   -- Generate assignments for outputs used more than once,
   -- and accumulate a map of the others.
   go :: M.Map Bus Expr -> [CompS] -> (M.Map Bus Expr, [(Bus,Expr)])
   -- go saved comps | DT.trace ("accumComps/go " ++ show saved ++ " " ++ show comps) False = undefined
   go saved [] = (saved, [])
   go saved (c@(CompS _ _ _ [o]) : comps)
     | Just n <- M.lookup o counts, (n > 1 || not nestExpressions) =
         let (saved',assignments') = go saved comps in
           (saved', (o,e) : assignments')
     | otherwise = go (M.insert o e saved) comps
    where
      e = compExpr saved c
   go _saved [CompS _ "Out" _ _ ] = error "accumComps: Out"
                                   -- (_saved,[])
   go _ c = error ("ConCat.GLSL.accumComps: oops: " ++ show c)

compExpr :: M.Map Bus Expr -> CompS -> Expr
compExpr _ (CompS _ str [] [Bus _ _ ty]) = constExpr ty str
compExpr saved (CompS _ prim ins [Bus _ _ ty]) = app ty prim (inExpr <$> ins)
 where
   inExpr :: Bus -> Expr
   inExpr b | Just e <- M.lookup b saved = e
            | otherwise = bToE b
compExpr _ comp = error ("ConCat.GLSL.compExpr: unexpected subgraph comp " ++ show comp)

constExpr :: C.Ty -> String -> Expr
constExpr C.Bool    = BoolConstant        . read
constExpr C.Int     = IntConstant Decimal . read
constExpr C.Integer = integerConstant     . read
constExpr C.Float   = FloatConstant       . read
constExpr C.Double  = FloatConstant       . read
constExpr ty = error ("ConCat.GLSL.constExpr: unexpected literal type: " ++ show ty)

-- TODO: Vector

-- Cheat: treat Integer as Int
integerConstant :: Integer -> Expr
integerConstant = IntConstant Decimal . fromInteger

busType :: Bus -> TypeSpecifierNonArray
busType = glslTy . busTy

initBus :: Bus -> Expr -> Statement
initBus b e = DeclarationStatement (decl Nothing (busType b) (varName b) (Just e))

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

app :: C.Ty -> String -> [Expr] -> Expr
app ty nm es =
  case nm of
    "not"    -> app1 UnaryNot
    "&&"     -> app2 And
    "||"     -> app2 Or
    "<"      -> app2 Lt
    ">"      -> app2 Gt
    "<="     -> app2 Lte
    ">="     -> app2 Gte
    "=="     -> app2 Equ
    "/="     -> app2 Neq
    "negate" -> app1 UnaryNegate
    "+"      -> app2 Add
    "-"      -> app2 Sub
    "−"      -> app2 Sub
    "*"      -> app2 Mul
    "/"      -> app2 Div
    "mod"    -> app2 Mod
    "xor"    -> app2 Neq
    "if"     -> app3 Selection
    "fromIntegral" -> funcall (castFun (glslTy ty)) es
    _ | Just fun <- M.lookup nm knownFuncs -> funcall fun es
      | otherwise -> error ("ConCat.GLSL.app: not supported: " ++ show (nm,es))
 where
   err str = error ("app " ++ nm ++ ": expecting " ++ str
                    ++ " but got " ++ show es)
   app1 op | [e] <- es = op e
           | otherwise = err "one argument"
   app2 op | [e1,e2] <- es = op e1 e2
           | otherwise = err "two arguments"
   app3 op | [e1,e2,e3] <- es = op e1 e2 e3
           | otherwise = err "three arguments"
   castFun Float = "float"
   castFun t = error ("ConCat.GLSL.app: fromIntegral on type " ++ show t)

knownFuncs :: M.Map String String
knownFuncs = M.fromList $
  [("ceiling","ceil")]
  ++ ((\ s -> (s,s)) <$> ["exp","log","cos","sin","floor","vec4"])

bToE :: Bus -> Expr
bToE = Variable . varName

-- Extract input, middle, output components.
splitComps :: [CompS] -> (CompS,[CompS],CompS)
splitComps (i@(CompS _ "In" [] _)
            : (unsnoc -> (mid,o@(CompS _ "Out" _ [])))) = (i,mid,o)
splitComps comps = error ("ConCat.GLSL.splitComps: Oops: " ++ show comps)

unsnoc :: [a] -> ([a],a)
-- unsnoc as = (mid,o) where (mid,[o]) = splitAt (length as - 1) as
unsnoc as = (mid,o) where (mid,[o]) = splitAt' 1 as

-- Like splitAt but where count is from the end
splitAt' :: Int -> [a] -> ([a], [a])
splitAt' n as = splitAt (length as - n) as

--------------------------------------------------
-- * GLSL syntax utilities

-- For experiments. Makes it easy to see syntax representations.
_parse :: P a -> String -> Either ParseError a
_parse p = runParser p S "GLSL"

decl :: Maybe TypeQualifier -> TypeSpecifierNonArray -> String -> Maybe Expr -> Declaration
decl mbTq ty var mbe =
  InitDeclaration (
      TypeDeclarator (
          FullType mbTq (TypeSpec Nothing (TypeSpecNoPrecision ty Nothing))))
   [InitDecl var Nothing mbe]

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

--------------------------------------------------
-- * Shader representation for conversion to JSON and String

data Widget = Time | Slider String (R,R) R

instance Show Widget where
  show Time = "Time"
  show (Slider lab bounds start) =
    printf "Slider %s %s %s" lab (show bounds) (show start)

instance ToJSON Widget where
  toJSON Time = object ["type" .= T.pack "time"]
  toJSON (Slider label (lo,hi) start) =
    object [ "type"  .= T.pack "slider"
           , "label" .= label
           , "min"   .= lo
           , "max"   .= hi
           , "value" .= start
           ]

prettyConfig :: Config
prettyConfig = defConfig { confCompare = keyOrder keys }
 where
   keys = ["uniforms","definition","type","name","widget","label","min","max","value"]

-- | Uniform variable
data UVar = UVar TypeSpecifierNonArray String Widget deriving Show

busUVar :: Bus -> Widget -> UVar
busUVar b = UVar (busType b) (varName b)

-- | Fragment shader with uniform parameters and code.
data Shader a = Shader [UVar] ExternalDeclaration deriving Show

-- Orphan
instance ToJSON C.Ty where toJSON = showJSON

showJSON :: Show a => a -> J.Value
showJSON = J.String . T.pack . show

prettyJSON :: Pretty a => a -> J.Value
prettyJSON = J.String . T.pack . prettyShow

-- Orphans
instance ToJSON TypeSpecifierNonArray where toJSON = prettyJSON
instance ToJSON ExternalDeclaration   where toJSON = prettyJSON

instance ToJSON UVar where
  toJSON (UVar ty name widget) =
    object ["type" .= ty, "name" .= name, "widget" .= widget]

instance ToJSON (Shader a) where
  toJSON (Shader vars def) = object ["uniforms" .= vars, "definition" .= def]

-- Input descriptions for uniform parameters
data Widgets :: * -> * where
  UnitW :: Widgets ()
  PrimW :: Widget -> Widgets a
  PairW :: Widgets a -> Widgets b -> Widgets (a :* b)

deriving instance Show (Widgets a)

unitW :: Widgets ()
unitW = UnitW

timeW :: Widgets R
timeW = PrimW Time

sliderW :: String -> (R,R) -> R -> Widgets R
sliderW = (fmap.fmap.fmap) PrimW Slider

pairW :: Widgets a -> Widgets b -> Widgets (a :* b)
pairW = PairW

flattenWidgets :: Widgets a -> [Widget]
flattenWidgets UnitW       = []
flattenWidgets (PrimW wid) = [wid]
flattenWidgets (PairW a b) = flattenWidgets a ++ flattenWidgets b

-- TODO: rework flattenWidgets for efficiency, taking an accumulation argument,
-- (equivalently) generating a difference list, or generating a Seq.
