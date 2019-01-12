module Check (typecheck) where

import qualified Ast
import qualified Annot

type TypeErr = String

typecheck :: Ast.Program -> Either TypeErr Annot.Program
typecheck = undefined
