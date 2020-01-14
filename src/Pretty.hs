{-# LANGUAGE LambdaCase #-}

module Pretty (pretty, Pretty(..)) where

import Prelude hiding (showChar)
import Data.List
import Data.Bifunctor
import qualified Data.Set as Set
import Data.Set (Set)

import Misc
import SrcPos
import qualified Ast
import qualified AnnotAst as An


-- Pretty print starting at some indentation depth
class Pretty a where
    pretty' :: Int -> a -> String

pretty :: Pretty a => a -> String
pretty = pretty' 0

spcPretty :: Pretty a => [a] -> String
spcPretty = unwords . map pretty


instance Pretty a => Pretty (WithPos a) where
    pretty' d = pretty' d . unpos


instance Pretty Ast.Program where
    pretty' = prettyProg
instance Pretty Ast.Extern where
    pretty' = prettyExtern
instance Pretty Ast.ConstructorDefs where
    pretty' = prettyConstructorDefs
instance Pretty Ast.TypeDef where
    pretty' = prettyTypeDef
instance Pretty Ast.Expr' where
    pretty' = prettyExpr'
instance Pretty Ast.Pat where
    pretty' _ = prettyPat
instance Pretty Ast.Const where
    pretty' _ = prettyConst
instance Pretty Ast.Scheme where
    pretty' _ (Ast.Forall _ ps t) = prettyScheme ps t
instance Pretty Ast.Type where
    pretty' _ = prettyType
instance Pretty Ast.TPrim where
    pretty' _ = prettyTPrim
instance Pretty Ast.TVar where
    pretty' _ = prettyTVar
instance Pretty (Ast.Id a) where
    pretty' _ = Ast.idstr

prettyProg :: Int -> Ast.Program -> String
prettyProg d (Ast.Program defs tdefs externs) =
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

prettyExtern :: Int -> Ast.Extern -> String
prettyExtern _ (Ast.Extern name t) =
    concat ["(extern ", Ast.idstr name, " ", pretty t, ")"]

prettyTypeDef :: Int -> Ast.TypeDef -> String
prettyTypeDef d (Ast.TypeDef name params constrs) = concat
    [ "(type "
    , if null params
        then pretty name
        else "(" ++ pretty name ++ " " ++ spcPretty params ++ ")"
    , "\n" ++ indent (d + 2) ++ pretty' (d + 2) constrs ++ ")"
    ]

prettyConstructorDefs :: Int -> Ast.ConstructorDefs -> String
prettyConstructorDefs d (Ast.ConstructorDefs cs) = intercalate
    ("\n" ++ indent d)
    (map prettyConstrDef cs)
  where
    prettyConstrDef = \case
        (c, []) -> pretty c
        (c, ts) -> concat ["(", pretty c, " ", spcPretty ts, ")"]

prettyExpr' :: Int -> Ast.Expr' -> String
prettyExpr' d = \case
    Ast.Lit l -> pretty l
    Ast.Var v -> Ast.idstr v
    Ast.App f x -> concat
        [ "(" ++ pretty' (d + 1) f ++ "\n"
        , indent (d + 1) ++ pretty' (d + 1) x ++ ")"
        ]
    Ast.If pred' cons alt -> concat
        [ "(if " ++ pretty' (d + 4) pred' ++ "\n"
        , indent (d + 4) ++ pretty' (d + 4) cons ++ "\n"
        , indent (d + 2) ++ pretty' (d + 2) alt ++ ")"
        ]
    Ast.Fun param body -> concat
        [ "(fun ("
        , prettyPat param
        , ")\n"
        , indent (d + 2)
        , pretty' (d + 2) body
        , ")"
        ]
    Ast.Let binds body -> concat
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
    Ast.TypeAscr e t ->
        concat ["(: ", pretty' (d + 3) e, "\n", pretty' (d + 3) t, ")"]
    Ast.Match e cs -> concat
        [ "(match " ++ pretty' (d + 7) e
        , precalate
            ("\n" ++ indent (d + 2))
            (map (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    Ast.FunMatch cs -> concat
        [ "(fun-match"
        , precalate
            ("\n" ++ indent (d + 2))
            (map (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    Ast.Ctor c -> pretty c
    Ast.Box e -> concat ["(box ", pretty' (d + 5) e, ")"]
    Ast.Deref e -> concat ["(deref ", pretty' (d + 7) e, ")"]

prettyBracketPair :: (Pretty a, Pretty b) => Int -> (a, b) -> String
prettyBracketPair d (a, b) = concat
    ["[", pretty' (d + 1) a, "\n", indent (d + 1), pretty' (d + 1) b, "]"]

prettyPat :: Ast.Pat -> String
prettyPat = \case
    Ast.PConstruction _ (Ast.Id (WithPos _ c)) ps ->
        if null ps then c else concat ["(", c, " ", spcPretty ps, ")"]
    Ast.PInt _ n -> show n
    Ast.PBool _ b -> if b then "true" else "false"
    Ast.PStr _ s -> prettyStr s
    Ast.PVar v -> Ast.idstr v
    Ast.PBox _ p -> "(Box " ++ prettyPat p ++ ")"

prettyConst :: Ast.Const -> String
prettyConst = \case
    Ast.Unit -> "unit"
    Ast.Int n -> show n
    Ast.Double x -> show x
    Ast.Str s -> prettyStr s
    Ast.Bool b -> if b then "true" else "false"

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

prettyType :: Ast.Type -> String
prettyType = \case
    Ast.TVar tv -> pretty tv
    Ast.TPrim c -> pretty c
    Ast.TFun a b -> prettyTFun a b
    Ast.TBox t -> prettyTBox t
    Ast.TConst tc -> prettyTConst tc

prettyTConst :: Pretty t => (String, [t]) -> String
prettyTConst (c, ts) = case ts of
    [] -> c
    _ -> concat ["(", c, " ", spcPretty ts, ")"]

prettyTBox :: Pretty t => t -> String
prettyTBox t = "(Box " ++ pretty t ++ ")"

prettyTFun :: Ast.Type -> Ast.Type -> String
prettyTFun a b =
    let
        (bParams, bBody) = f b
        f = \case
            Ast.TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in concat ["(Fun ", pretty a, " ", spcPretty (bParams ++ [bBody]), ")"]

prettyTPrim :: Ast.TPrim -> String
prettyTPrim = \case
    Ast.TUnit -> "Unit"
    Ast.TNat8 -> "Nat8"
    Ast.TNat16 -> "Nat16"
    Ast.TNat32 -> "Nat32"
    Ast.TNat -> "Nat"
    Ast.TInt8 -> "Int8"
    Ast.TInt16 -> "Int16"
    Ast.TInt32 -> "Int32"
    Ast.TInt -> "Int"
    Ast.TDouble -> "Double"
    Ast.TBool -> "Bool"

prettyTVar :: Ast.TVar -> String
prettyTVar = \case
    Ast.TVExplicit v -> Ast.idstr v
    Ast.TVImplicit n -> "#" ++ show n


instance Pretty An.Scheme where
    pretty' _ (An.Forall ps t) = prettyScheme ps t
instance Pretty An.Type where
    pretty' _ = prettyAnType

prettyAnType :: An.Type -> String
prettyAnType = \case
    An.TVar tv -> pretty tv
    An.TPrim c -> pretty c
    An.TFun a b -> prettyAnTFun a b
    An.TBox t -> prettyTBox t
    An.TConst tc -> prettyTConst tc

prettyAnTFun :: An.Type -> An.Type -> String
prettyAnTFun a b =
    let
        (bParams, bBody) = f b
        f = \case
            An.TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in concat ["(Fun ", pretty a, " ", spcPretty (bParams ++ [bBody]), ")"]
