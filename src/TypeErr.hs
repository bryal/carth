{-# LANGUAGE LambdaCase, FlexibleContexts #-}

module TypeErr (TypeErr(..), prettyErr) where

import Misc
import SrcPos
import Ast
import Parse

import qualified Text.Megaparsec as Mega
import Text.Megaparsec.Pos
import Data.Either

data TypeErr
    = MainNotDefined
    | InvalidUserTypeSig SrcPos Scheme Scheme
    | CtorArityMismatch SrcPos Id Int Int
    | ConflictingPatVarDefs SrcPos String
    | UndefCtor SrcPos String
    | UndefVar SrcPos String
    | InfType SrcPos TVar Type
    | UnificationFailed SrcPos Type Type Type Type
    | ConflictingTypeDef Id
    | ConflictingCtorDef Id

type Message = String

prettyErr :: TypeErr -> Source -> String
prettyErr = \case
    MainNotDefined -> const "Error: main not defined"
    InvalidUserTypeSig p s1 s2 ->
        posd p ns_scheme
            $ ("Invalid user type signature " ++ pretty s1)
            ++ (", expected " ++ pretty s2)
    CtorArityMismatch p c arity nArgs ->
        posd p ns_patCtion
            $ ("Arity mismatch for constructor `" ++ pretty c)
            ++ ("` in pattern.\nExpected " ++ show arity)
            ++ (", found " ++ show nArgs)
    ConflictingPatVarDefs p v ->
        posd p var
            $ "Conflicting definitions for variable `"
            ++ v
            ++ "` in pattern."
    UndefCtor p c ->
        posd p eConstructor $ "Undefined constructor `" ++ c ++ "`"
    UndefVar p v -> posd p var $ "Undefined variable `" ++ v ++ "`"
    InfType p a t ->
        posd p ns_expr $ "Infinite type: " ++ pretty a ++ " ~ " ++ pretty t
    UnificationFailed p t1 t2 t'1 t'2 ->
        posd p ns_expr
            $ ("Couldn't match type " ++ pretty t'2 ++ " with " ++ pretty t'1)
            ++ (".\nExpected type: " ++ pretty t1)
            ++ (".\nFound type: " ++ pretty t2 ++ ".")
    ConflictingTypeDef (WithPos p x) ->
        posd p ns_big $ "Conflicting definitions for type `" ++ x ++ "`."
    ConflictingCtorDef (WithPos p x) ->
        posd p ns_big $ "Conflicting definitions for constructor `" ++ x ++ "`."

posd :: SrcPos -> Parser a -> Message -> Source -> String
posd (SrcPos pos@(SourcePos _ lineN colN)) parser msg src =
    let
        (lineN', colN') = (unPos lineN, unPos colN)
        lines' = lines src
        line = if (lineN' <= length lines')
            then lines' !! (lineN' - 1)
            else ice "line num in SourcePos is greater than num of lines in src"
        rest = if (colN' <= length line)
            then drop (colN' - 1) line
            else
                ice
                    "col num in SourcePos is greater than num of cols in src line"
        lineNS = show lineN'
        pad = length lineNS + 1
        s = fromRight
            (ice "posd parse error")
            (parse' (fmap fst (Mega.match parser)) "" rest)
    in unlines
        [ sourcePosPretty pos ++ ": Error:"
        , indent pad ++ "|"
        , lineNS ++ " | " ++ line
        -- Find the span (end-pos) of the item in the source by applying the same
        -- parser that gave the item, starting at its SourcePos
        , indent pad ++ "|" ++ indent (colN') ++ replicate (length s) '^'
        , msg
        ]
