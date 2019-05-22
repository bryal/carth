module Misc where

ice :: String -> a
ice = error . ("Internal Compiler Error: " ++)
