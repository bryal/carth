{-# LANGUAGE LambdaCase, FlexibleContexts #-}

module TypeErr (TypeErr(..), prettyErr) where

import Misc
import SrcPos
import Ast
import qualified Parse

import qualified Text.Megaparsec as Mega
import Text.Megaparsec.Pos
import Data.Functor
import Control.Applicative

data TypeErr
    = MainNotDefined
    | InvalidUserTypeSig SrcPos Scheme Scheme
    | CtorArityMismatch SrcPos Id Int Int
    | ConflictingPatVarDefs SrcPos String
    | UndefCtor SrcPos String
    | UndefVar SrcPos String
    | InfType SrcPos Type Type TVar Type
    | UnificationFailed SrcPos Type Type Type Type
    | ConflictingTypeDef Id
    | ConflictingCtorDef Id
    | RedundantCase SrcPos
    | InexhaustivePats SrcPos String
    deriving Show

type Message = String

prettyErr :: TypeErr -> Parse.Source -> String
prettyErr = \case
    MainNotDefined -> const "Error: main not defined"
    InvalidUserTypeSig p s1 s2 ->
        posd p scheme
            $ ("Invalid user type signature " ++ pretty s1)
            ++ (", expected " ++ pretty s2)
    CtorArityMismatch p c arity nArgs ->
        posd p pat
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
    InfType p t1 t2 a t ->
        posd p defOrExpr
            $ "Infinite type: "
            ++ (pretty a ++ " ~ " ++ pretty t)
            ++ ("\nExpected type: " ++ pretty t1)
            ++ ("\nFound type: " ++ pretty t2)
    UnificationFailed p t1 t2 t'1 t'2 ->
        posd p defOrExpr
            $ ("Couldn't match type " ++ pretty t'2 ++ " with " ++ pretty t'1)
            ++ (".\nExpected type: " ++ pretty t1)
            ++ (".\nFound type: " ++ pretty t2 ++ ".")
    ConflictingTypeDef (WithPos p x) ->
        posd p big $ "Conflicting definitions for type `" ++ x ++ "`."
    ConflictingCtorDef (WithPos p x) ->
        posd p big $ "Conflicting definitions for constructor `" ++ x ++ "`."
    RedundantCase p -> posd p pat $ "Redundant case in pattern match."
    InexhaustivePats p patStr ->
        posd p defOrExpr
            $ "Inexhaustive patterns: "
            ++ patStr
            ++ " not covered."
  where
    -- | Used to handle that the position of the generated nested lambdas of a
    --   definition of the form `(define (foo a b ...) ...)` is set to the
    --   top-level position.
    defOrExpr =
        (Parse.ns_parens . Parse.def =<< Parse.getSrcPos)
            <||> Parse.ns_expr
            <||> wholeLine
    scheme = Parse.ns_scheme <||> wholeLine
    pat = Parse.ns_pat <||> wholeLine
    var = Parse.var <||> wholeLine
    eConstructor = Parse.eConstructor <||> wholeLine
    big = Parse.ns_big
    wholeLine = many Mega.anySingle
    (<||>) pa pb = (Mega.try pa $> ()) <|> (pb $> ())

posd :: SrcPos -> Parse.Parser a -> Message -> Parse.Source -> String
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
        s = either
            (\e -> ice ("posd: msg=|" ++ msg ++ "|,err=|" ++ show e ++ "|"))
            id
            (Parse.parse' (fmap fst (Mega.match parser)) "" rest)
    in unlines
        [ sourcePosPretty pos ++ ": Error:"
        , indent pad ++ "|"
        , lineNS ++ " | " ++ line
        -- Find the span (end-pos) of the item in the source by applying the same
        -- parser that gave the item, starting at its SourcePos
        , indent pad ++ "|" ++ indent (colN') ++ replicate (length s) '^'
        , msg
        ]
