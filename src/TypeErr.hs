{-# LANGUAGE LambdaCase, FlexibleContexts, DataKinds #-}

module TypeErr (TypeErr(..), printErr) where

import Text.Megaparsec (SourcePos(..), unPos)

import Misc
import SrcPos
import qualified Ast
import AnnotAst
import Pretty
import Parse


data TypeErr
    = StartNotDefined
    | InvalidUserTypeSig SrcPos Scheme Scheme
    | CtorArityMismatch SrcPos String Int Int
    | ConflictingPatVarDefs SrcPos String
    | UndefCtor SrcPos String
    | UndefVar SrcPos String
    | InfType SrcPos Type Type TVar Type
    | UnificationFailed SrcPos Type Type Type Type
    | ConflictingTypeDef SrcPos String
    | ConflictingCtorDef SrcPos String
    | RedundantCase SrcPos
    | InexhaustivePats SrcPos String
    | ExternNotMonomorphic (Ast.Id 'Ast.Small) TVar
    | FoundHole SrcPos
    | RecTypeDef String SrcPos
    | UndefType SrcPos String
    | UnboundTVar SrcPos
    | WrongStartType SrcPos Ast.Scheme
    | RecursiveVarDef (WithPos String)
    | TypeInstArityMismatch SrcPos String Int Int
    | ConflictingVarDef SrcPos String
    deriving Show

type Message = String

printErr :: TypeErr -> IO ()
printErr = \case
    StartNotDefined -> putStrLn "Error: start not defined"
    InvalidUserTypeSig p s1 s2 ->
        posd p
            $ ("Invalid user type signature " ++ pretty s1)
            ++ (", expected " ++ pretty s2)
    CtorArityMismatch p c arity nArgs ->
        posd p
            $ ("Arity mismatch for constructor `" ++ c)
            ++ ("` in pattern.\nExpected " ++ show arity)
            ++ (", found " ++ show nArgs)
    ConflictingPatVarDefs p v ->
        posd p
            $ "Conflicting definitions for variable `"
            ++ v
            ++ "` in pattern."
    UndefCtor p c -> posd p $ "Undefined constructor `" ++ c ++ "`"
    UndefVar p v -> posd p $ "Undefined variable `" ++ v ++ "`"
    InfType p t1 t2 a t ->
        posd p
            $ "Infinite type: "
            ++ (pretty a ++ " ~ " ++ pretty t)
            ++ ("\nExpected type: " ++ pretty t1)
            ++ ("\nFound type: " ++ pretty t2)
    UnificationFailed p t1 t2 t'1 t'2 ->
        posd p
            $ ("Couldn't match type " ++ pretty t'2 ++ " with " ++ pretty t'1)
            ++ (".\nExpected type: " ++ pretty t1)
            ++ (".\nFound type: " ++ pretty t2 ++ ".")
    ConflictingTypeDef p x ->
        posd p $ "Conflicting definitions for type `" ++ x ++ "`."
    ConflictingCtorDef p x ->
        posd p $ "Conflicting definitions for constructor `" ++ x ++ "`."
    RedundantCase p -> posd p $ "Redundant case in pattern match."
    InexhaustivePats p patStr ->
        posd p $ "Inexhaustive patterns: " ++ patStr ++ " not covered."
    ExternNotMonomorphic name tv -> case tv of
        TVExplicit (Ast.Id (WithPos p tv')) ->
            posd p
                $ ("Extern " ++ pretty name ++ " is not monomorphic. ")
                ++ ("Type variable " ++ tv' ++ " encountered in type signature")
        TVImplicit _ -> ice "TVImplicit in prettyErr ExternNotMonomorphic"
    FoundHole p -> posd p $ "Found hole"
    RecTypeDef x p ->
        posd p
            $ ("Type `" ++ x ++ "` ")
            ++ "has infinite size due to recursion without indirection.\n"
            ++ "Insert a pointer at some point to make it representable."
    UndefType p x -> posd p $ "Undefined type `" ++ x ++ "`."
    UnboundTVar p ->
        posd p
            $ "Could not fully infer type of expression.\n"
            ++ "Type annotations needed."
    WrongStartType p s ->
        posd p
            $ "Incorrect type of `start`.\n"
            ++ ("Expected: " ++ pretty startType)
            ++ ("\nFound: " ++ pretty s)
    RecursiveVarDef (WithPos p x) ->
        posd p
            $ ("Non-function variable definition `" ++ x ++ "` is recursive.")
    TypeInstArityMismatch p t expected found ->
        posd p
            $ ("Arity mismatch for instantiation of type `" ++ t)
            ++ ("`.\nExpected " ++ show expected)
            ++ (", found " ++ show found)
    ConflictingVarDef p x ->
        posd p $ "Conflicting definitions for variable `" ++ x ++ "`."

posd :: SrcPos -> Message -> IO ()
posd (SrcPos pos@(SourcePos f lineN colN)) msg = do
    src <- readFile f
    let (lineN', colN') = (unPos lineN, unPos colN)
        lines' = lines src
        line = if (lineN' <= length lines')
            then lines' !! (lineN' - 1)
            else ice "line num in SourcePos is greater than num of lines in src"
        rest = if (colN' <= length line)
            then drop (colN' - 1) line
            else
                ice
                $ "col num in SourcePos is greater than "
                ++ "num of cols in src line"
        lineNS = show lineN'
        pad = length lineNS + 1
        s = either
            (\e -> ice ("posd: msg=|" ++ msg ++ "|,err=|" ++ show e ++ "|"))
            id
            (parseTokenTreeOrRest rest)
    putStrLn $ unlines
        [ sourcePosPretty pos ++ ": Error:"
        , indent pad ++ "|"
        , lineNS ++ " | " ++ line
        -- Find the span (end-pos) of the item in the source by applying the same
        -- parser that gave the item, starting at its SourcePos
        , indent pad ++ "|" ++ indent (colN') ++ replicate (length s) '^'
        , msg
        ]
