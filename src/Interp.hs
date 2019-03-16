module Interp (interpret) where

import Annot
import Pretty

type InterpErr = String

interpret :: Program -> Either InterpErr ()
interpret p = Left ("not yet implemented\n" ++ "Annotated ast:\n" ++ pretty p)
