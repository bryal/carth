{-# LANGUAGE LambdaCase, FlexibleContexts #-}

module TypeErr (TypeErr(..), printErr) where

import Misc
import SrcPos
import Ast
import Parse

import qualified Text.Megaparsec as Mega
import Text.Megaparsec.Pos
import Control.Monad
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

printErr :: TypeErr -> IO ()
printErr = \case
    MainNotDefined -> putStrLn "Error: main not defined"
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
            ++ pretty v
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

posd :: SrcPos -> Parser a -> String -> IO ()
posd (SrcPos pos@(SourcePos file lineN colN)) parser msg = do
    let (lineN', colN') = (unPos lineN, unPos colN)
    src <- readFile file
    let lines' = lines src
    when (lineN' > length lines')
        $ ice "line num in SourcePos is greater than num of lines in src"
    let line = lines' !! (lineN' - 1)
    when (colN' > length line)
        $ ice "col num in SourcePos is greater than num of cols in src line"
    let lineNS = show lineN'
    let pad = length lineNS + 1
    putStrLn (sourcePosPretty pos ++ ": Error:")
    putStrLn (indent pad ++ "|")
    putStrLn (lineNS ++ " | " ++ line)
    -- Find the span (end-pos) of the item in the source by applying the same
    -- parser that gave the item, starting at its SourcePos
    let rest = drop (colN' - 1) line
    let
        s = fromRight
            (ice "posd parse error")
            (parse' (fmap fst (Mega.match parser)) "" rest)
    putStrLn (indent pad ++ "|" ++ indent (colN') ++ replicate (length s) '^')
    putStrLn msg
    putStrLn ""
