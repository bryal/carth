{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, LambdaCase #-}

module Misc
    ( ice
    , nyi
    , mapFst
    , mapSnd
    , precalate
    , FreeVars(..)
    , prettyPrint
    , pretty
    , Pretty(..)
    , prettyBracketPair
    , showChar''
    , showChar'
    )
where

import Data.Set (Set)
import Data.List (intercalate)

ice :: String -> a
ice = error . ("Internal Compiler Error: " ++)

nyi :: String -> a
nyi = error . ("Not yet implemented: " ++)

mapFst :: (a1 -> a2) -> (a1, b) -> (a2, b)
mapFst f (a, b) = (f a, b)

mapSnd :: (b1 -> b2) -> (a, b1) -> (a, b2)
mapSnd f (a, b) = (a, f b)

-- | Like `intercalate`, but concatenate a list with a prefix before each
--   element, instead of an separator between each pair of elements.
precalate :: [a] -> [[a]] -> [a]
precalate prefix xs = prefix ++ intercalate prefix xs

class Ord b => FreeVars a b where
    freeVars :: a -> Set b

-- Pretty printing
prettyPrint :: Pretty a => a -> IO ()
prettyPrint = putStrLn . pretty

pretty :: Pretty a => a -> String
pretty = pretty' 0

-- Pretty print starting at some indentation depth
class Pretty a where
    pretty' :: Int -> a -> String

instance Pretty String where
    pretty' _ = id

prettyBracketPair :: (Pretty a, Pretty b) => Int -> (a, b) -> String
prettyBracketPair d (a, b) = concat
    ["[", pretty' (d + 1) a, "\n", replicate (d + 1) ' ', pretty' (d + 1) b, "]"]

showChar'' :: Char -> String
showChar'' = \case
    '\0' -> "\\0"
    '\a' -> "\\a"
    '\b' -> "\\b"
    '\t' -> "\\t"
    '\n' -> "\\n"
    '\v' -> "\\v"
    '\f' -> "\\f"
    '\r' -> "\\r"
    '\\' -> "\\\\"
    '\"' -> "\\\""
    c -> [c]

showChar' :: Char -> String
showChar' c = "'" ++ showChar'' c ++ "'"
