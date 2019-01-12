module Interp (interpret) where

import Annot

type InterpErr = String

interpret :: Program -> Either InterpErr ()
interpret _ = Left "not yet implemented"
