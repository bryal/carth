{-# LANGUAGE LambdaCase, FlexibleContexts, DataKinds #-}

module Err (module Err, TypeErr(..), GenErr(..)) where

import Text.Megaparsec (match)

import Misc
import SrcPos
import TypeAst
import qualified Parsed
import Inferred
import Pretty
import Lex
import Gen


type Message = String

printParseErr :: (SrcPos, String) -> IO ()
printParseErr (p, msg) = posd p msg

printTypeErr :: TypeErr -> IO ()
printTypeErr = \case
    MainNotDefined -> putStrLn "Error: main not defined"
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
        posd p $ "Conflicting definitions for variable `" ++ v ++ "` in pattern."
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
    ConflictingTypeDef p x -> posd p $ "Conflicting definitions for type `" ++ x ++ "`."
    ConflictingCtorDef p x ->
        posd p $ "Conflicting definitions for constructor `" ++ x ++ "`."
    RedundantCase p -> posd p $ "Redundant case in pattern match."
    InexhaustivePats p patStr ->
        posd p $ "Inexhaustive patterns: " ++ patStr ++ " not covered."
    ExternNotMonomorphic name tv -> case tv of
        TVExplicit (Parsed.Id (WithPos p tv')) ->
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
    WrongMainType p s ->
        posd p
            $ "Incorrect type of `main`.\n"
            ++ ("Expected: " ++ pretty (mainType :: Type))
            ++ ("\nFound: " ++ pretty s)
    RecursiveVarDef (WithPos p x) ->
        posd p $ ("Non-function variable definition `" ++ x ++ "` is recursive.")
    TypeInstArityMismatch p t expected found ->
        posd p
            $ ("Arity mismatch for instantiation of type `" ++ t)
            ++ ("`.\nExpected " ++ show expected)
            ++ (", found " ++ show found)
    ConflictingVarDef p x ->
        posd p $ "Conflicting definitions for variable `" ++ x ++ "`."

printGenErr :: GenErr -> IO ()
printGenErr = \case
    TransmuteErr p (t, sizet) (u, sizeu) ->
        posd p
            $ "Cannot transmute between types of different sizes."
            ++ ("\nSource type: " ++ pretty t)
            ++ (" (" ++ show sizet ++ " bytes)")
            ++ ("\nTarget type: " ++ pretty u)
            ++ (" (" ++ show sizeu ++ " bytes)")
    CastErr p t u -> posd p $ "Cannot cast " ++ pretty t ++ " to " ++ pretty u
    NoBuiltinVirtualInstance p x t ->
        posd p
            $ ("Builtin virtual function " ++ x)
            ++ (" cannot be instantiated to type " ++ pretty t)

posd :: SrcPos -> Message -> IO ()
posd (pos@(SrcPos f lineN colN)) msg = do
    src <- readFile f
    let (lineN', colN') = (fromIntegral lineN, fromIntegral colN)
        lines' = lines src
        line = if (lineN' <= length lines')
            then lines' !! (lineN' - 1)
            else ice "line num in SourcePos is greater than num of lines in src"
        rest = if (colN' <= length line)
            then drop (colN' - 1) line
            else
                ice $ "col num in SourcePos is greater than " ++ "num of cols in src line"
        lineNS = show lineN'
        pad = length lineNS + 1
        s = either (const rest) fst (parse' (match tokentree) "" rest)
    putStrLn $ unlines
        [ prettySrcPos pos ++ ": Error:"
        , indent pad ++ "|"
        , lineNS ++ " | " ++ line
        -- Find the span (end-pos) of the item in the source by applying the same
        -- parser that gave the item, starting at its SourcePos
        , indent pad ++ "|" ++ indent (colN') ++ replicate (length s) '^'
        , msg
        ]
