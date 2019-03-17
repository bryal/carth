{-# LANGUAGE LambdaCase #-}

module Pretty where

import NonEmpty
import Ast
import qualified Annot
import Data.List (intercalate)
import qualified Data.Set as Set
import qualified Data.Map as Map

-- Pretty printing

prettyPrint :: Pretty a => a -> IO ()
prettyPrint = putStrLn . pretty

pretty :: Pretty a => a -> String
pretty = pretty' 0

-- Pretty print starting at some indentation depth
class Pretty a where
  pretty' :: Int -> a -> String

-- Instance Ast
--------------------------------------------------------------------------------

instance Pretty Program where
  pretty' d (Program main defs) =
    let allDefs = (Id "main", main) : defs
        prettyDef (Id name, val) =
          concat [ replicate d ' ', "(define ", name, "\n"
                 , replicate (d + 2) ' ', pretty' (d + 2) val, ")" ]
    in unlines (map prettyDef allDefs)

instance Pretty Expr where
  pretty' d = \case
    Unit -> "unit"
    Int n -> show n
    Double x -> show x
    Str s -> '"' : (s >>= showChar'') ++ "\""
    Bool b -> if b then "true" else "false"
    Var (Id v) -> v
    App f x ->
      concat [ "(", pretty' (d + 1) f, "\n"
             , replicate (d + 1) ' ',  pretty' (d + 1) x, ")" ]
    If pred cons alt ->
      concat [ "(if ", pretty' (d + 4) pred, "\n"
             , replicate (d + 4) ' ', pretty' (d + 4) cons, "\n"
             , replicate (d + 2) ' ', pretty' (d + 2) alt, ")" ]
    Fun (Id param) body ->
      concat [ "(fun [", param, "]", "\n"
             , replicate (d + 2) ' ', pretty' (d + 2) body, ")" ]
    Let binds body ->
      concat [ "(let ["
             , intercalate1 ("\n" ++ replicate (d + 6) ' ')
                            (map1 (prettyBracketPair (d + 6)) binds)
             , "]\n"
             , replicate (d + 2) ' ' ++ pretty' (d + 2) body, ")" ]
    Match e cs ->
      concat [ "(match ", pretty' (d + 7) e
             , "\n", replicate (d + 2) ' '
             , intercalate1 ("\n" ++ replicate (d + 2) ' ')
                            (map1 (prettyBracketPair (d + 2)) cs)
             , ")"]
    FunMatch cs ->
      concat [ "(fun-match"
             , "\n", replicate (d + 2) ' '
             , intercalate1 ("\n" ++ replicate (d + 2) ' ')
                            (map1 (prettyBracketPair (d + 2)) cs)
             , ")"]
    Constructor c -> c
    Char c -> showChar' c

instance Pretty Id where
  pretty' _ (Id s) = s

instance Pretty Pat where
  pretty' _ = \case
    PConstructor c -> c
    PConstruction c ps ->
      concat ["(", c, " ", intercalate " " (nonEmptyToList (map1 pretty ps)), ")"]
    PVar (Id v) -> v

-- Instance Annot
--------------------------------------------------------------------------------

instance Pretty Annot.Program where
  pretty' d (Annot.Program main defs) =
    let allDefs = (Id "main", (Annot.mainScheme, main)) : Map.toList defs
        prettyDef (Id name, (scm, val)) =
          concat [ replicate d ' ', "(define ", name, " ; ", pretty scm, "\n"
                 , replicate (d + 2) ' ', pretty' (d + 2) val, ")" ]
    in unlines (map prettyDef allDefs)

instance Pretty Annot.Expr where
  pretty' d = \case
    Annot.Unit -> "unit"
    Annot.Int n -> show n
    Annot.Double x -> show x
    Annot.Str s -> '"' : (s >>= showChar'') ++ "\""
    Annot.Bool b -> if b then "true" else "false"
    Annot.Var (Id v) -> v
    Annot.App f x ->
      concat [ "(", pretty' (d + 1) f, "\n"
             , replicate (d + 1) ' ',  pretty' (d + 1) x, ")" ]
    Annot.If pred cons alt ->
      concat [ "(if ", pretty' (d + 4) pred, "\n"
             , replicate (d + 4) ' ', pretty' (d + 4) cons, "\n"
             , replicate (d + 2) ' ', pretty' (d + 2) alt, ")" ]
    Annot.Fun (Id param) body ->
      concat [ "(fun [", param, "]", "\n"
             , replicate (d + 2) ' ', pretty' (d + 2) body, ")" ]
    Annot.Let binds body ->
      concat [ "(let ["
             , intercalate ("\n" ++ replicate (d + 6) ' ')
                           (map (prettyBinding (d + 6)) (Map.toList binds))
             , "]\n"
             , replicate (d + 2) ' ' ++ pretty' (d + 2) body, ")" ]
    Annot.Match e cs ->
      concat [ "(match ", pretty' (d + 7) e
             , "\n", replicate (d + 2) ' '
             , intercalate1 ("\n" ++ replicate (d + 2) ' ')
                            (map1 (prettyBracketPair (d + 2)) cs)
             , ")"]
    Annot.FunMatch cs ->
      concat [ "(fun-match"
             , "\n", replicate (d + 2) ' '
             , intercalate1 ("\n" ++ replicate (d + 2) ' ')
                            (map1 (prettyBracketPair (d + 2)) cs)
             , ")"]
    Annot.Constructor c -> c
    Annot.Char c -> showChar' c
    where prettyBinding d (name, (scm, body)) =
            prettyBracketPair d (name, body) ++ " ; " ++ pretty scm

instance Pretty Annot.Scheme where
  pretty' _ (Annot.Forall ps b) =
    concat ["forall ", intercalate " " (Set.toList ps), ". ", pretty b]

instance Pretty Annot.Type where
  pretty' _ = \case
    Annot.TVar tv -> tv
    Annot.TConst c -> c
    Annot.TFun a b -> concat ["(-> ", pretty a, " ", pretty b, ")"]

-- Misc
--------------------------------------------------------------------------------

prettyBracketPair :: (Pretty a, Pretty b) => Int -> (a, b) -> String
prettyBracketPair d (a, b) =
  concat [ "[", pretty' (d + 1) a, "\n"
         , replicate (d + 1) ' ', pretty' (d + 1) b, "]" ]

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
