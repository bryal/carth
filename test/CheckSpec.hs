{-# LANGUAGE LambdaCase #-}

module CheckSpec where

import Test.Hspec

import qualified Ast
import qualified DesugaredAst as Des
import Parse
import Check
import TypeErr

pStartNotDefined = "(define foo unit)"
pInvalidUserTypeSig = concat
    [ "(define: (invalid-user-type-signature x)"
    , "    (forall (a b c) (Fun a a))"
    , "  x)"
    ]
pCtorArityMismatch = concat
    [ "(type Integ (Integ Int))"
    , "(define arity-mismatch-for-constructor"
    , "  (match (Integ 1)"
    , "    (case (Integ foo bar) foo)))"
    ]
pConflictingPatVarDefs = concat
    [ "(type IntPair (IntPair Int Int))"
    , "(define conflicting-defs-in-pat"
    , "  (match (IntPair 1 2)"
    , "    (case (IntPair a a) a)))"
    ]
pUndefCtor = "(define undef-ctor ThisCtorIsUndefined)"
pUndefVar = "(define undef-var this-var-is-undefined)"
pInfType = "(define (infinite-type x) (infinite-type x infinite-type))"
pUnificationFailed =
    "(type Integ (Integ Int)) (define type-mismatch (Integ true))"
pConflictingTypeDef = "(type Foo) (type Foo)"
pConflictingCtorDef_a = "(type Foo Bar Bar)"
pConflictingCtorDef_b = "(type Baz Baz) (type Quux Baz)"
pRedundantCase = concat
    [ "(define foo"
    , "  (fun-match"
    , "    (case true 0)"
    , "    (case true 1)"
    , "    (case false 2)))"
    ]
pInexhaustivePats = "(define foo (fun-match (case true 0)))"
pExternNotMonomorphic = "(extern foo (Fun a Int))"
pFoundHole = "(define foo _)"
pRecTypeDef = "(type Foo (Foo Foo))"
pUndefType_a = "(type Foo (Foo Bar))"
pUndefType_b = "(define: (foo x) (Fun Int Foo) (foo x))"
pUnboundTVar = unlines
    [ "(define (seq a b) b)"
    , "(define (undef a) (undef a))"
    , "(define (foo a) (seq (undef unit) 123))"
    ]
pWrongStartType = "(define: start Int (undefined unit))"
pRecursiveVarDef = "(define: foo Int (+ foo 1))"
pTypeInstArityMismatch = "(type (Foo a) (Foo a)) (type Bar (Bar Foo))"
pConflictingVarDef_a = "(define foo +) (define foo -)"
pConflictingVarDef_b = "(define foo (let ((a 1) (a 2)) a))"

spec :: Spec
spec = do
    let startDef = "(define (start _) unit)"
    describe "typecheck" $ do
        it "detects when start is not defined"
            $ shouldSatisfy (typecheck' pStartNotDefined)
            $ \case
                Right (Left StartNotDefined) -> True
                _ -> False
        it "detects invalid user type signatures"
            $ shouldSatisfy (typecheck' pInvalidUserTypeSig)
            $ \case
                Right (Left (InvalidUserTypeSig{})) -> True
                _ -> False
        it "detects arity mismatch in constructor"
            $ shouldSatisfy (typecheck' pCtorArityMismatch)
            $ \case
                Right (Left (CtorArityMismatch{})) -> True
                _ -> False
        it "detects conflicting pattern variable defs"
            $ shouldSatisfy (typecheck' pConflictingPatVarDefs)
            $ \case
                Right (Left (ConflictingPatVarDefs{})) -> True
                _ -> False
        it "detects undefined constructors"
            $ shouldSatisfy (typecheck' pUndefCtor)
            $ \case
                Right (Left (UndefCtor{})) -> True
                _ -> False
        it "detects undefined variables"
            $ shouldSatisfy (typecheck' pUndefVar)
            $ \case
                Right (Left (UndefVar{})) -> True
                _ -> False
        it "detects infinite types"
            $ shouldSatisfy (typecheck' pInfType)
            $ \case
                Right (Left (InfType{})) -> True
                _ -> False
        it "detects type unification failure"
            $ shouldSatisfy (typecheck' pUnificationFailed)
            $ \case
                Right (Left (UnificationFailed{})) -> True
                _ -> False
        it "detects conflicting type definitions"
            $ shouldSatisfy (typecheck' pConflictingTypeDef)
            $ \case
                Right (Left (ConflictingTypeDef{})) -> True
                _ -> False
        it "detects conflicting constructor definitions, withing"
            $ shouldSatisfy (typecheck' pConflictingCtorDef_a)
            $ \case
                Right (Left (ConflictingCtorDef{})) -> True
                _ -> False
        it "detects conflicting constructor definitions, between"
            $ shouldSatisfy (typecheck' pConflictingCtorDef_b)
            $ \case
                Right (Left (ConflictingCtorDef{})) -> True
                _ -> False
        it "detects redundant cases in patterns"
            $ shouldSatisfy (typecheck' pRedundantCase)
            $ \case
                Right (Left (RedundantCase{})) -> True
                _ -> False
        it "detects inexhaustive patterns"
            $ shouldSatisfy (typecheck' pInexhaustivePats)
            $ \case
                Right (Left (InexhaustivePats{})) -> True
                _ -> False
        it "detects non-monomorphic externs"
            $ shouldSatisfy (typecheck' pExternNotMonomorphic)
            $ \case
                Right (Left (ExternNotMonomorphic{})) -> True
                _ -> False
        it "finds holes" $ shouldSatisfy (typecheck' pFoundHole) $ \case
            Right (Left (FoundHole{})) -> True
            _ -> False
        it "detects type definitions recursive without indirection"
            $ shouldSatisfy (typecheck' pRecTypeDef)
            $ \case
                Right (Left (RecTypeDef{})) -> True
                _ -> False
        it "detects references to undefined types, in type defs"
            $ shouldSatisfy (typecheck' pUndefType_a)
            $ \case
                Right (Left (UndefType{})) -> True
                _ -> False
        it "detects references to undefined types, in var defs"
            $ shouldSatisfy (typecheck' pUndefType_b)
            $ \case
                Right (Left (UndefType{})) -> True
                _ -> False
        it "detects unbound type vars in var def bodies"
            $ shouldSatisfy (typecheck' pUnboundTVar)
            $ \case
                Right (Left (UnboundTVar{})) -> True
                _ -> False
        it "detects when the type of `start` is wrong"
            $ shouldSatisfy (typecheck' pWrongStartType)
            $ \case
                Right (Left (WrongStartType{})) -> True
                _ -> False
        it "detects recursive var defs"
            $ shouldSatisfy (typecheck' pRecursiveVarDef)
            $ \case
                Right (Left (RecursiveVarDef{})) -> True
                _ -> False
        it "detects arity mismatch of datatype instantiations"
            $ shouldSatisfy (typecheck' pTypeInstArityMismatch)
            $ \case
                Right (Left (TypeInstArityMismatch{})) -> True
                _ -> False
        it "detects conflicting var defs, at top-level"
            $ shouldSatisfy (typecheck' pConflictingVarDef_a)
            $ \case
                Right (Left (ConflictingVarDef{})) -> True
                _ -> False
        it "detects conflicting var defs, in let-form"
            $ shouldSatisfy (typecheck' pConflictingVarDef_b)
            $ \case
                Right (Left (ConflictingVarDef{})) -> True
                _ -> False

typecheck' :: String -> Either String (Either TypeErr Des.Program)
typecheck' =
    fmap (\(_, ds, tds, es) -> typecheck (Ast.Program ds tds es))
        . parse' toplevels "TEST"
