{-# LANGUAGE LambdaCase #-}

module Pretty (pretty, Pretty(..)) where

import Prelude hiding (showChar)
import Data.List
import Data.Bifunctor
import qualified Data.Set as Set
import Data.Set (Set)

import Misc
import SrcPos
import qualified Parsed
import qualified Inferred


-- Pretty print starting at some indentation depth
class Pretty a where
    pretty' :: Int -> a -> String

pretty :: Pretty a => a -> String
pretty = pretty' 0

spcPretty :: Pretty a => [a] -> String
spcPretty = unwords . map pretty


instance Pretty a => Pretty (WithPos a) where
    pretty' d = pretty' d . unpos


instance Pretty Parsed.Program where
    pretty' = prettyProg
instance Pretty Parsed.Extern where
    pretty' = prettyExtern
instance Pretty Parsed.ConstructorDefs where
    pretty' = prettyConstructorDefs
instance Pretty Parsed.TypeDef where
    pretty' = prettyTypeDef
instance Pretty Parsed.Expr' where
    pretty' = prettyExpr'
instance Pretty Parsed.Pat where
    pretty' _ = prettyPat
instance Pretty Parsed.Const where
    pretty' _ = prettyConst
instance Pretty Parsed.Scheme where
    pretty' _ (Parsed.Forall _ ps t) = prettyScheme ps t
instance Pretty Parsed.Type where
    pretty' _ = prettyType
instance Pretty Parsed.TPrim where
    pretty' _ = prettyTPrim
instance Pretty Parsed.TVar where
    pretty' _ = prettyTVar
instance Pretty (Parsed.Id a) where
    pretty' _ = Parsed.idstr

prettyProg :: Int -> Parsed.Program -> String
prettyProg d (Parsed.Program defs tdefs externs) =
    let
        prettyDef = \case
            (name, (Just scm, body)) -> concat
                [ indent d ++ "(define: " ++ pretty name ++ "\n"
                , indent (d + 4) ++ pretty' (d + 4) scm ++ "\n"
                , indent (d + 2) ++ pretty' (d + 2) body ++ ")"
                ]
            (name, (Nothing, body)) -> concat
                [ indent d ++ "(define " ++ pretty name ++ "\n"
                , indent (d + 2) ++ pretty' (d + 2) body ++ ")"
                ]
    in unlines (map prettyDef defs ++ map pretty tdefs ++ map pretty externs)

prettyExtern :: Int -> Parsed.Extern -> String
prettyExtern _ (Parsed.Extern name t) =
    concat ["(extern ", Parsed.idstr name, " ", pretty t, ")"]

prettyTypeDef :: Int -> Parsed.TypeDef -> String
prettyTypeDef d (Parsed.TypeDef name params constrs) = concat
    [ "(type "
    , if null params
        then pretty name
        else "(" ++ pretty name ++ " " ++ spcPretty params ++ ")"
    , "\n" ++ indent (d + 2) ++ pretty' (d + 2) constrs ++ ")"
    ]

prettyConstructorDefs :: Int -> Parsed.ConstructorDefs -> String
prettyConstructorDefs d (Parsed.ConstructorDefs cs) = intercalate
    ("\n" ++ indent d)
    (map prettyConstrDef cs)
  where
    prettyConstrDef = \case
        (c, []) -> pretty c
        (c, ts) -> concat ["(", pretty c, " ", spcPretty ts, ")"]

prettyExpr' :: Int -> Parsed.Expr' -> String
prettyExpr' d = \case
    Parsed.Lit l -> pretty l
    Parsed.Var v -> Parsed.idstr v
    Parsed.App f x -> concat
        [ "(" ++ pretty' (d + 1) f ++ "\n"
        , indent (d + 1) ++ pretty' (d + 1) x ++ ")"
        ]
    Parsed.If pred' cons alt -> concat
        [ "(if " ++ pretty' (d + 4) pred' ++ "\n"
        , indent (d + 4) ++ pretty' (d + 4) cons ++ "\n"
        , indent (d + 2) ++ pretty' (d + 2) alt ++ ")"
        ]
    Parsed.Fun param body -> concat
        [ "(fun ("
        , prettyPat param
        , ")\n"
        , indent (d + 2)
        , pretty' (d + 2) body
        , ")"
        ]
    Parsed.Let binds body -> concat
        [ "(let ["
        , intercalate ("\n" ++ indent (d + 6)) (map (prettyDef (d + 6)) binds)
        , "]\n"
        , indent (d + 2) ++ pretty' (d + 2) body ++ ")"
        ]
      where
        prettyDef d' = \case
            (name, (Just scm, dbody)) -> concat
                [ "[: " ++ pretty' (d' + 3) name ++ "\n"
                , indent (d' + 3) ++ pretty' (d' + 3) scm ++ "\n"
                , indent (d' + 1) ++ pretty' (d' + 1) dbody ++ "]"
                ]
            (name, (Nothing, dbody)) -> concat
                [ "[" ++ pretty' (d' + 1) name ++ "\n"
                , indent (d' + 1) ++ pretty' (d' + 1) dbody ++ "]"
                ]
    Parsed.TypeAscr e t ->
        concat ["(: ", pretty' (d + 3) e, "\n", pretty' (d + 3) t, ")"]
    Parsed.Match e cs -> concat
        [ "(match " ++ pretty' (d + 7) e
        , precalate
            ("\n" ++ indent (d + 2))
            (map (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    Parsed.FunMatch cs -> concat
        [ "(fun-match"
        , precalate
            ("\n" ++ indent (d + 2))
            (map (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    Parsed.Ctor c -> pretty c
    Parsed.Box e -> concat ["(box ", pretty' (d + 5) e, ")"]
    Parsed.Deref e -> concat ["(deref ", pretty' (d + 7) e, ")"]

prettyBracketPair :: (Pretty a, Pretty b) => Int -> (a, b) -> String
prettyBracketPair d (a, b) = concat
    ["[", pretty' (d + 1) a, "\n", indent (d + 1), pretty' (d + 1) b, "]"]

prettyPat :: Parsed.Pat -> String
prettyPat = \case
    Parsed.PConstruction _ (Parsed.Id (WithPos _ c)) ps ->
        if null ps then c else concat ["(", c, " ", spcPretty ps, ")"]
    Parsed.PInt _ n -> show n
    Parsed.PBool _ b -> if b then "true" else "false"
    Parsed.PStr _ s -> prettyStr s
    Parsed.PVar v -> Parsed.idstr v
    Parsed.PBox _ p -> "(Box " ++ prettyPat p ++ ")"

prettyConst :: Parsed.Const -> String
prettyConst = \case
    Parsed.Unit -> "unit"
    Parsed.Int n -> show n
    Parsed.Double x -> show x
    Parsed.Str s -> prettyStr s
    Parsed.Bool b -> if b then "true" else "false"

prettyStr :: String -> String
prettyStr s = '"' : (s >>= showChar) ++ "\""
  where
    showChar = \case
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

prettyScheme :: (Pretty p, Pretty t) => Set p -> t -> String
prettyScheme ps t =
    concat ["(forall [" ++ spcPretty (Set.toList ps) ++ "] ", pretty t ++ ")"]

prettyType :: Parsed.Type -> String
prettyType = \case
    Parsed.TVar tv -> pretty tv
    Parsed.TPrim c -> pretty c
    Parsed.TFun a b -> prettyTFun a b
    Parsed.TBox t -> prettyTBox t
    Parsed.TConst tc -> prettyTConst tc

prettyTConst :: Pretty t => (String, [t]) -> String
prettyTConst (c, ts) = case ts of
    [] -> c
    _ -> concat ["(", c, " ", spcPretty ts, ")"]

prettyTBox :: Pretty t => t -> String
prettyTBox t = "(Box " ++ pretty t ++ ")"

prettyTFun :: Parsed.Type -> Parsed.Type -> String
prettyTFun a b =
    let
        (bParams, bBody) = f b
        f = \case
            Parsed.TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in concat ["(Fun ", pretty a, " ", spcPretty (bParams ++ [bBody]), ")"]

prettyTPrim :: Parsed.TPrim -> String
prettyTPrim = \case
    Parsed.TUnit -> "Unit"
    Parsed.TNat8 -> "Nat8"
    Parsed.TNat16 -> "Nat16"
    Parsed.TNat32 -> "Nat32"
    Parsed.TNat -> "Nat"
    Parsed.TInt8 -> "Int8"
    Parsed.TInt16 -> "Int16"
    Parsed.TInt32 -> "Int32"
    Parsed.TInt -> "Int"
    Parsed.TDouble -> "Double"
    Parsed.TBool -> "Bool"

prettyTVar :: Parsed.TVar -> String
prettyTVar = \case
    Parsed.TVExplicit v -> Parsed.idstr v
    Parsed.TVImplicit n -> "#" ++ show n


instance Pretty Inferred.Scheme where
    pretty' _ (Inferred.Forall ps t) = prettyScheme ps t
instance Pretty Inferred.Type where
    pretty' _ = prettyAnType

prettyAnType :: Inferred.Type -> String
prettyAnType = \case
    Inferred.TVar tv -> pretty tv
    Inferred.TPrim c -> pretty c
    Inferred.TFun a b -> prettyAnTFun a b
    Inferred.TBox t -> prettyTBox t
    Inferred.TConst tc -> prettyTConst tc

prettyAnTFun :: Inferred.Type -> Inferred.Type -> String
prettyAnTFun a b =
    let
        (bParams, bBody) = f b
        f = \case
            Inferred.TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in concat ["(Fun ", pretty a, " ", spcPretty (bParams ++ [bBody]), ")"]
