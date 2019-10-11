{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, LambdaCase #-}

module Misc
    ( ice
    , nyi
    , precalate
    , prettyPrint
    , pretty
    , Pretty(..)
    , prettyBracketPair
    , indent
    , showChar''
    , showChar'
    , both
    )
where

import Data.List (intercalate)

ice :: String -> a
ice = error . ("Internal Compiler Error: " ++)

nyi :: String -> a
nyi = error . ("Not yet implemented: " ++)

-- | Like `intercalate`, but concatenate a list with a prefix before each
--   element, instead of an separator between each pair of elements.
precalate :: [a] -> [[a]] -> [a]
precalate prefix xs = prefix ++ intercalate prefix xs

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
    ["[", pretty' (d + 1) a, "\n", indent (d + 1), pretty' (d + 1) b, "]"]

indent :: Int -> String
indent = flip replicate ' '

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

both :: (a -> b) -> (a, a) -> (b, b)
both f (a0, a1) = (f a0, f a1)
