{-# LANGUAGE LambdaCase #-}

module CheckSpec where

import Test.Hspec

import AnnotAst
import Parse
import Check
import TypeErr

spec :: Spec
spec = do
    let mainDef = "(define (main _) unit)"
    let p0 = "(define (foo _) unit)"
    let p1 = unlines ["(define: (id x) (forall [] (Fun a a)) x)", mainDef]
    let p2 = unlines
            [ "(type Foo Bar (Baz Int))"
            , "(define foo (fun-match [(Bar x) x]))"
            , mainDef
            ]
    let p3 = unlines
            [ "(type (Pair a b) (Pair a b))"
            , "(define foo (fun-match [(Pair x x) x]))"
            , mainDef
            ]
    let p4 = unlines ["(define foo (fun-match [Foo 3]))", mainDef]
    let p5 = unlines ["(define foo x)", mainDef]
    let p6 = unlines ["(define foo (foo foo))", mainDef]
    let p7 = unlines ["(define: (foo _) (Fun Int Int) 3.1415)", mainDef]
    let p8 = unlines ["(type Foo Bar)", "(type Foo Baz)", mainDef]
    let p9 = unlines ["(type Foo1 Bar)", "(type Foo2 Bar)", mainDef]
    let p10 =
            unlines
                [ "(type Foo Bar)"
                , "(define foo (fun-match [Bar 1] [Bar 2]))"
                , mainDef
                ]
    let p11 =
            unlines
                [ "(type Foo Bar Baz)"
                , "(define foo (fun-match [Bar 1]))"
                , mainDef
                ]
    describe "typecheck" $ do
        it "detects when main is not defined"
            $ shouldSatisfy (typecheck' p0)
            $ \case
                Right (Left MainNotDefined) -> True
                _ -> False
        it "detects invalid user type signatures"
            $ shouldSatisfy (typecheck' p1)
            $ \case
                Right (Left (InvalidUserTypeSig _ _ _)) -> True
                _ -> False
        it "detects arity mismatch in constructor"
            $ shouldSatisfy (typecheck' p2)
            $ \case
                Right (Left (CtorArityMismatch _ _ _ _)) -> True
                _ -> False
        it "detects conflicting pattern variable defs"
            $ shouldSatisfy (typecheck' p3)
            $ \case
                Right (Left (ConflictingPatVarDefs _ _)) -> True
                _ -> False
        it "detects undefined constructors"
            $ shouldSatisfy (typecheck' p4)
            $ \case
                Right (Left (UndefCtor _ _)) -> True
                _ -> False
        it "detects undefined variables" $ shouldSatisfy (typecheck' p5) $ \case
            Right (Left (UndefVar _ _)) -> True
            _ -> False
        it "detects infinite types" $ shouldSatisfy (typecheck' p6) $ \case
            Right (Left (InfType _ _ _ _ _)) -> True
            _ -> False
        it "detects type unification failure"
            $ shouldSatisfy (typecheck' p7)
            $ \case
                Right (Left (UnificationFailed _ _ _ _ _)) -> True
                _ -> False
        it "detects conflicting type definitions"
            $ shouldSatisfy (typecheck' p8)
            $ \case
                Right (Left (ConflictingTypeDef _)) -> True
                _ -> False
        it "detects conflicting constructor definitions"
            $ shouldSatisfy (typecheck' p9)
            $ \case
                Right (Left (ConflictingCtorDef _)) -> True
                _ -> False
        it "detects redundant cases in patterns"
            $ shouldSatisfy (typecheck' p10)
            $ \case
                Right (Left (RedundantCase _)) -> True
                _ -> False
        it "detects inexhaustive patterns"
            $ shouldSatisfy (typecheck' p11)
            $ \case
                Right (Left (InexhaustivePats _ _)) -> True
                _ -> False

typecheck' :: String -> Either String (Either TypeErr Program)
typecheck' = fmap typecheck . parse "TEST"
