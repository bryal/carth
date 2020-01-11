{-# LANGUAGE LambdaCase, FlexibleContexts, DataKinds #-}

module TypeErr (TypeErr(..), printErr) where

import Misc
import SrcPos
import Ast
import qualified Parse

import qualified Text.Megaparsec as Mega
import Text.Megaparsec.Pos
import Data.Functor
import Control.Applicative

data TypeErr
    = StartNotDefined
    | InvalidUserTypeSig SrcPos Scheme Scheme
    | CtorArityMismatch SrcPos (Id Big) Int Int
    | ConflictingPatVarDefs SrcPos String
    | UndefCtor SrcPos String
    | UndefVar SrcPos String
    | InfType SrcPos Type Type TVar Type
    | UnificationFailed SrcPos Type Type Type Type
    | ConflictingTypeDef (Id Big)
    | ConflictingCtorDef (Id Big)
    | RedundantCase SrcPos
    | InexhaustivePats SrcPos String
    | ExternNotMonomorphic (Id Small) TVar
    | FoundHole SrcPos
    | RecTypeDef String SrcPos
    | UndefType SrcPos String
    | UnboundTVar SrcPos
    | WrongStartType (WithPos Scheme)
    | RecursiveVarDef (WithPos String)
    | TypeInstArityMismatch SrcPos String Int Int
    deriving Show

type Message = String

printErr :: TypeErr -> IO ()
printErr = \case
    StartNotDefined -> putStrLn "Error: start not defined"
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
    ConflictingTypeDef (Id (WithPos p x)) ->
        posd p big $ "Conflicting definitions for type `" ++ x ++ "`."
    ConflictingCtorDef (Id (WithPos p x)) ->
        posd p big $ "Conflicting definitions for constructor `" ++ x ++ "`."
    RedundantCase p -> posd p pat $ "Redundant case in pattern match."
    InexhaustivePats p patStr ->
        posd p defOrExpr
            $ "Inexhaustive patterns: "
            ++ patStr
            ++ " not covered."
    ExternNotMonomorphic name tv -> case tv of
        TVExplicit (Id (WithPos p tv')) ->
            posd p tvar
                $ ("Extern " ++ pretty name ++ " is not monomorphic. ")
                ++ ("Type variable " ++ tv' ++ " encountered in type signature")
        TVImplicit _ -> ice "TVImplicit in prettyErr ExternNotMonomorphic"
    FoundHole p -> posd p var $ "Found hole"
    RecTypeDef x p ->
        posd p big
            $ ("Type `" ++ x ++ "` ")
            ++ "has infinite size due to recursion without indirection.\n"
            ++ "Insert a pointer at some point to make it representable."
    UndefType p x -> posd p big $ "Undefined type `" ++ x ++ "`."
    UnboundTVar p ->
        posd p defOrExpr
            $ "Could not fully infer type of expression.\n"
            ++ "Type annotations needed."
    WrongStartType (WithPos p s) ->
        posd p scheme
            $ "Incorrect type of `start`.\n"
            ++ ("Expected: " ++ pretty startType)
            ++ ("\nFound: " ++ pretty s)
    RecursiveVarDef (WithPos p x) ->
        posd p var
            $ ("Non-function variable definition `" ++ x ++ "` is recursive.")
    TypeInstArityMismatch p t expected found ->
        posd p tokenTree
            $ ("Arity mismatch for instantiation of type `" ++ pretty t)
            ++ ("`.\nExpected " ++ show expected)
            ++ (", found " ++ show found)
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
    var = Parse.ns_small' <||> wholeLine
    tvar = var
    eConstructor = Parse.eConstructor <||> wholeLine
    big = Parse.ns_big
    wholeLine = many Mega.anySingle
    tokenTree = Parse.ns_tokenTree
    (<||>) pa pb = (Mega.try pa $> ()) <|> (pb $> ())

posd :: SrcPos -> Parse.Parser a -> Message -> IO ()
posd (SrcPos pos@(SourcePos f lineN colN)) parser msg = do
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
                    "col num in SourcePos is greater than num of cols in src line"
        lineNS = show lineN'
        pad = length lineNS + 1
        s = either
            (\e -> ice ("posd: msg=|" ++ msg ++ "|,err=|" ++ show e ++ "|"))
            id
            (Parse.parse' (fmap fst (Mega.match parser)) "" rest)
    putStrLn $ unlines
        [ sourcePosPretty pos ++ ": Error:"
        , indent pad ++ "|"
        , lineNS ++ " | " ++ line
        -- Find the span (end-pos) of the item in the source by applying the same
        -- parser that gave the item, starting at its SourcePos
        , indent pad ++ "|" ++ indent (colN') ++ replicate (length s) '^'
        , msg
        ]
