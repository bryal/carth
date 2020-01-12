{-# LANGUAGE LambdaCase #-}

module PrettyAst () where

import Data.List
import Data.Bifunctor
import qualified Data.Set as Set

import Misc
import SrcPos
import Ast


instance Pretty Program where
    pretty' = prettyProg
instance Pretty Extern where
    pretty' = prettyExtern
instance Pretty ConstructorDefs where
    pretty' = prettyConstructorDefs
instance Pretty TypeDef where
    pretty' = prettyTypeDef
instance Pretty Expr' where
    pretty' = prettyExpr'
instance Pretty Pat where
    pretty' _ = prettyPat
instance Pretty Const where
    pretty' _ = prettyConst
instance Pretty Scheme where
    pretty' _ = prettyScheme
instance Pretty Type where
    pretty' _ = prettyType
instance Pretty TPrim where
    pretty' _ = prettyTPrim
instance Pretty TVar where
    pretty' _ = prettyTVar
instance Pretty (Id a) where
    pretty' _ = idstr


prettyProg :: Int -> Program -> String
prettyProg d (Program defs tdefs externs) =
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

prettyExtern :: Int -> Extern -> String
prettyExtern _ (Extern name t) =
    concat ["(extern ", idstr name, " ", pretty t, ")"]

prettyTypeDef :: Int -> TypeDef -> String
prettyTypeDef d (TypeDef name params constrs) = concat
    [ "(type "
    , if null params
        then pretty name
        else "(" ++ pretty name ++ " " ++ spcPretty params ++ ")"
    , "\n" ++ indent (d + 2) ++ pretty' (d + 2) constrs ++ ")"
    ]

prettyConstructorDefs :: Int -> ConstructorDefs -> String
prettyConstructorDefs d (ConstructorDefs cs) = intercalate
    ("\n" ++ indent d)
    (map prettyConstrDef cs)
  where
    prettyConstrDef = \case
        (c, []) -> pretty c
        (c, ts) -> concat ["(", pretty c, " ", spcPretty ts, ")"]

prettyExpr' :: Int -> Expr' -> String
prettyExpr' d = \case
    Lit l -> pretty l
    Var v -> idstr v
    App f x -> concat
        [ "(" ++ pretty' (d + 1) f ++ "\n"
        , indent (d + 1) ++ pretty' (d + 1) x ++ ")"
        ]
    If pred' cons alt -> concat
        [ "(if " ++ pretty' (d + 4) pred' ++ "\n"
        , indent (d + 4) ++ pretty' (d + 4) cons ++ "\n"
        , indent (d + 2) ++ pretty' (d + 2) alt ++ ")"
        ]
    Fun param body -> concat
        [ "(fun ("
        , prettyPat param
        , ")\n"
        , indent (d + 2)
        , pretty' (d + 2) body
        , ")"
        ]
    Let binds body -> concat
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
    TypeAscr e t ->
        concat ["(: ", pretty' (d + 3) e, "\n", pretty' (d + 3) t, ")"]
    Match e cs -> concat
        [ "(match " ++ pretty' (d + 7) e
        , precalate
            ("\n" ++ indent (d + 2))
            (map (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    FunMatch cs -> concat
        [ "(fun-match"
        , precalate
            ("\n" ++ indent (d + 2))
            (map (prettyBracketPair (d + 2)) cs)
        , ")"
        ]
    Ctor c -> pretty c
    Box e -> concat ["(box ", pretty' (d + 5) e, ")"]
    Deref e -> concat ["(deref ", pretty' (d + 7) e, ")"]

prettyBracketPair :: (Pretty a, Pretty b) => Int -> (a, b) -> String
prettyBracketPair d (a, b) = concat
    ["[", pretty' (d + 1) a, "\n", indent (d + 1), pretty' (d + 1) b, "]"]

prettyPat :: Pat -> String
prettyPat = \case
    PConstruction _ (Id (WithPos _ c)) ps ->
        if null ps then c else concat ["(", c, " ", spcPretty ps, ")"]
    PInt _ n -> show n
    PBool _ b -> if b then "true" else "false"
    PStr _ s -> prettyStr s
    PVar v -> idstr v
    PBox _ p -> "(Box " ++ prettyPat p ++ ")"

prettyConst :: Const -> String
prettyConst = \case
    Unit -> "unit"
    Int n -> show n
    Double x -> show x
    Str s -> prettyStr s
    Bool b -> if b then "true" else "false"

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

prettyScheme :: Scheme -> String
prettyScheme (Forall ps t) =
    concat ["(forall [" ++ spcPretty (Set.toList ps) ++ "] ", pretty t ++ ")"]

prettyType :: Type -> String
prettyType = \case
    Ast.TVar tv -> pretty tv
    Ast.TPrim c -> pretty c
    Ast.TFun a b -> prettyTFun a b
    Ast.TBox t -> "(Box " ++ pretty t ++ ")"
    Ast.TConst (c, ts) -> case ts of
        [] -> c
        _ -> concat ["(", c, " ", spcPretty ts, ")"]

prettyTFun :: Type -> Type -> String
prettyTFun a b =
    let
        (bParams, bBody) = f b
        f = \case
            TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in concat ["(Fun ", pretty a, " ", spcPretty (bParams ++ [bBody]), ")"]

prettyTPrim :: TPrim -> String
prettyTPrim = \case
    TUnit -> "Unit"
    TNat8 -> "Nat8"
    TNat16 -> "Nat16"
    TNat32 -> "Nat32"
    TNat -> "Nat"
    TInt8 -> "Int8"
    TInt16 -> "Int16"
    TInt32 -> "Int32"
    TInt -> "Int"
    TDouble -> "Double"
    TBool -> "Bool"

prettyTVar :: TVar -> String
prettyTVar = \case
    TVExplicit v -> idstr v
    TVImplicit n -> "#" ++ show n

spcPretty :: Pretty a => [a] -> String
spcPretty = unwords . map pretty
