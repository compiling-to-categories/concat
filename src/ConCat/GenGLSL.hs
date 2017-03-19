{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- TEMP

-- | 

module ConCat.GenGLSL where

import Language.GLSL.Syntax

import ConCat.Circuit           -- TODO: trim import list


#if 0
data CompS = CompS CompNum PrimName [Input] [Output] Reuses deriving Show

data Bus = Bus PinId Width

type Input  = Bus
type Output = Bus
#endif

fromCompS :: CompS -> Statement
fromCompS (CompS n prim ins [out] _) =
  DeclarationStatement (InitDeclaration (TypeDeclarator _) [InitDecl ("x"++show n)])

