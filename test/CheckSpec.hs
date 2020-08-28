{-# LANGUAGE LambdaCase #-}

module CheckSpec where

import Test.Hspec

import qualified Parsed
import qualified Checked
import Parse
import Check
import Err

pMainNotDefined = "(define foo Unit)"
pInvalidUserTypeSig = concat
    ["(define: (invalid-user-type-signature x)", "    (forall (a b c) (Fun a a))", "  x)"]
pCtorArityMismatch = concat
    [ "(data Integ (Integ Int))"
    , "(define arity-mismatch-for-constructor"
    , "  (match (Integ 1)"
    , "    (case (Integ foo bar) foo)))"
    ]
pConflictingPatVarDefs = concat
    [ "(data IntPair (IntPair Int Int))"
    , "(define conflicting-defs-in-pat"
    , "  (match (IntPair 1 2)"
    , "    (case (IntPair a a) a)))"
    ]
pUndefCtor = "(define undef-ctor ThisCtorIsUndefined)"
pUndefVar = "(define undef-var this-var-is-undefined)"
pInfType = "(define (infinite-type x) (infinite-type x infinite-type))"
pUnificationFailed = "(data Integ (Integ Int)) (define type-mismatch (Integ True))"
pConflictingTypeDef = "(data Foo) (data Foo)"
pConflictingCtorDef_a = "(data Foo Bar Bar)"
pConflictingCtorDef_b = "(data Baz Baz) (data Quux Baz)"
pRedundantCase = concat
    [ "(define foo"
    , "  (fmatch"
    , "    (case True 0)"
    , "    (case True 1)"
    , "    (case False 2)))"
    ]
pInexhaustivePats = "(define foo (fmatch (case True 0)))"
pExternNotMonomorphic = "(extern foo (Fun a Int))"
pFoundHole = "(define foo _)"
pRecTypeDef = "(data Foo (Foo Foo))"
pUndefType_a = "(data Foo (Foo Bar))"
pUndefType_b = "(extern foo (Fun Int Foo))"
pUndefType_c = "(define: (foo x) (Fun Int Foo) (foo x))"
pUnboundTVar = unlines
    [ "(define (seq a b) b)"
    , "(define (undef a) (undef a))"
    , "(define (foo a) (seq (undef Unit) 123))"
    ]
pWrongMainType = "(define: main Int (undefined Unit))"
pRecursiveVarDef = "(define: foo Int (+ foo 1))"
pTypeInstArityMismatch = "(data (Foo a) (Foo a)) (data Bar (Bar Foo))"
pConflictingVarDef_a = "(define foo +) (define foo -)"
pConflictingVarDef_b = "(define foo (letrec ((a 1) (a 2)) a))"

spec :: Spec
spec = do
    describe "typecheck" $ do
        it "detects when main is not defined"
            $ shouldSatisfy (typecheck' pMainNotDefined)
            $ \case
                  Right (Left MainNotDefined) -> True
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
        it "detects undefined variables" $ shouldSatisfy (typecheck' pUndefVar) $ \case
            Right (Left (UndefVar{})) -> True
            _ -> False
        it "detects infinite types" $ shouldSatisfy (typecheck' pInfType) $ \case
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
        it "detects references to undefined types, in extern decls"
            $ shouldSatisfy (typecheck' pUndefType_b)
            $ \case
                  Right (Left (UndefType{})) -> True
                  _ -> False
        it "detects references to undefined types, in var defs"
            $ shouldSatisfy (typecheck' pUndefType_c)
            $ \case
                  Right (Left (UndefType{})) -> True
                  _ -> False
        it "detects unbound type vars in var def bodies"
            $ shouldSatisfy (typecheck' pUnboundTVar)
            $ \case
                  Right (Left (UnboundTVar{})) -> True
                  _ -> False
        it "detects when the type of `main` is wrong"
            $ shouldSatisfy (typecheck' pWrongMainType)
            $ \case
                  Right (Left (WrongMainType{})) -> True
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

typecheck' :: String -> Either String (Either TypeErr Checked.Program)
typecheck' = fmap (\(_, ds, tds, es) -> typecheck (Parsed.Program ds tds es))
    . parse' toplevels "TEST"
