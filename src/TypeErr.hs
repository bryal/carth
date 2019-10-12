{-# LANGUAGE LambdaCase, FlexibleContexts #-}

module TypeErr (TypeErr(..)) where

import Misc
import SrcPos
import Ast

data TypeErr
    = MainNotDefined
    | InvalidUserTypeSig SrcPos Scheme Scheme
    | CtorArityMismatch SrcPos Id Int Int
    | ConflictingPatVarDefs SrcPos String
    | UndefCtor SrcPos String
    | UndefVar SrcPos String
    | InfType SrcPos TVar Type
    | UnificationFailed SrcPos Type Type Type Type

instance Pretty TypeErr where
    pretty' _ = prettyErr

prettyErr :: TypeErr -> String
prettyErr = \case
    MainNotDefined -> "Error: main not defined"
    InvalidUserTypeSig p s1 s2 ->
        f p
            $ ("Invalid user type signature " ++ pretty s1)
            ++ (", expected " ++ pretty s2)
    CtorArityMismatch p c arity nArgs ->
        f p
            $ ("Arity mismatch for constructor `" ++ pretty c)
            ++ ("` in pattern.\nExpected " ++ show arity)
            ++ (", found " ++ show nArgs)
    ConflictingPatVarDefs p v ->
        f p
            $ "Conflicting definitions for variable `"
            ++ pretty v
            ++ "` in pattern."
    UndefCtor p c -> f p $ "Undefined constructor `" ++ c ++ "`"
    UndefVar p v -> f p $ "Undefined variable `" ++ v ++ "`"
    InfType p a t -> f p $ "Infinite type: " ++ pretty a ++ " ~ " ++ pretty t
    UnificationFailed p t1 t2 t'1 t'2 ->
        f p
            $ ("Couldn't match type " ++ pretty t'2 ++ " with " ++ pretty t'1)
            ++ (".\nExpected type: " ++ pretty t1)
            ++ (".\nFound type: " ++ pretty t2 ++ ".")
    where f (SrcPos p) msg = sourcePosPretty p ++ ": Error: " ++ msg
