module Interp
    ( interpret
    ) where

import Annot

type InterpErr = String


interpret :: Program -> Either InterpErr ()
interpret p = Left "not yet implemented"
