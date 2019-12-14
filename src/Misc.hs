{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, LambdaCase, RankNTypes #-}

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
    , augment
    , insertWith'
    , if'
    )
where

import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Composition
import Control.Monad.Reader
import Control.Lens (Lens', locally)
import LLVM.AST.Type (Type)
import LLVM.AST (Name, Module)
import LLVM.Pretty ()
import qualified Data.Text.Prettyprint.Doc as Prettyprint

ice :: String -> a
ice = error . ("Internal Compiler Error: " ++)

nyi :: String -> a
nyi = error . ("Not yet implemented: " ++)

-- | Like `intercalate`, but concatenate a list with a prefix before each
--   element, instead of an separator between each pair of elements.
precalate :: [a] -> [[a]] -> [a]
precalate prefix = \case
    [] -> []
    xs -> prefix ++ intercalate prefix xs

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

instance Pretty Type where
    pretty' _ = show . Prettyprint.pretty
instance Pretty Name where
    pretty' _ = show . Prettyprint.pretty
instance Pretty Module where
    pretty' _ = show . Prettyprint.pretty

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

augment
    :: (MonadReader e m, Ord k) => Lens' e (Map k v) -> Map k v -> m a -> m a
augment l = locally l . Map.union

insertWith' :: Ord k => (v -> v) -> k -> v -> Map k v -> Map k v
insertWith' f = Map.insertWith (f .* flip const)

if' :: Bool -> a -> a -> a
if' p c a = if p then c else a
