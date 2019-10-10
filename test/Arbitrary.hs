{-# LANGUAGE LambdaCase #-}

module Arbitrary where

import Control.Applicative (liftA3, liftA2)
import Control.Monad
import qualified Data.Map as Map
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Modifiers

import SrcPos
import Parse
import Ast
import NonEmpty

instance Arbitrary Program where
    arbitrary = arbitraryProgram
    shrink = shrinkProgram
instance Arbitrary TypeDef where
    arbitrary = arbitraryTypeDef
    shrink = shrinkTypeDef
instance Arbitrary ConstructorDefs where
    arbitrary = arbitraryConstructorDefs
    shrink (ConstructorDefs cs) = map ConstructorDefs (shrink cs)
instance Arbitrary Expr' where
    arbitrary = arbitraryExpr'
    shrink = shrinkExpr'
instance Arbitrary a => Arbitrary (WithPos a) where
    arbitrary = fmap (WithPos dummyPos) arbitrary
    shrink x = fmap (WithPos (getPos x)) (shrink (unpos x))
instance Arbitrary Const where
    arbitrary = arbitraryConst
instance Arbitrary Pat where
    arbitrary = arbitraryPat
    shrink = shrinkPat
instance Arbitrary Id where
    arbitrary = fmap Id arbitrarySmall
    shrink = shrinkNothing
instance Arbitrary Scheme where
    arbitrary = applyArbitrary2 Forall
instance Arbitrary Type where
    arbitrary = arbitraryType
instance Arbitrary TVar where
    arbitrary = fmap TVExplicit arbitrary
instance Arbitrary TPrim where
    arbitrary = elements [TUnit, TInt, TDouble, TChar, TStr, TBool ]
instance Arbitrary a => Arbitrary (NonEmpty a) where
    arbitrary = arbitraryNonEmpty
    shrink (x :| xs) = [x' :| xs' | (x', xs') <- shrink (x, xs)]

arbitraryProgram :: Gen Program
arbitraryProgram = do
    main <- arbitrary
    defs <- vectorOf' (0, 4) arbitrary
    tdefs <- vectorOf' (0, 4) arbitrary
    pure (Program main defs tdefs)

arbitraryTypeDef :: Gen TypeDef
arbitraryTypeDef =
    liftA3 TypeDef arbitraryBig (vectorOf' (0, 4) arbitrary) arbitrary

arbitraryConstructorDefs :: Gen ConstructorDefs
arbitraryConstructorDefs = fmap
    (ConstructorDefs . Map.fromList)
    (choose (0, 5) >>= flip vectorOf arbitraryConstructorDef)

arbitraryConstructorDef :: Gen (String, [Type])
arbitraryConstructorDef = liftA2 (,) arbitraryBig (vectorOf' (0, 5) arbitrary)

arbitraryExpr' :: Gen Expr'
arbitraryExpr' = frequency
    [ (5, fmap Lit arbitrary)
    , (5, fmap Var arbitrary)
    , (2, applyArbitrary2 App)
    , (1, applyArbitrary3 If)
    , (1, applyArbitrary2 Fun)
    , (1, applyArbitrary2 Let)
    , (1, applyArbitrary2 TypeAscr)
    , (1, applyArbitrary2 Match)
    , (1, fmap FunMatch arbitrary)
    , (5, fmap Constructor arbitraryBig)
    ]

arbitraryConst :: Gen Const
arbitraryConst = frequency
    [ (2, pure Unit)
    , (5, fmap Int arbitrary)
    , (5, fmap Double arbitrary)
    , (1, fmap (Str . getPrintableString) arbitrary)
    , (1, fmap Bool arbitrary)
    , (1, fmap Char arbitraryChar)
    ]

arbitraryChar :: Gen Char
arbitraryChar = oneof
    [ choose ('a', 'z')
    , choose ('A', 'Z')
    , choose ('0', '9')
    , elements ['+', '-', '?', '(', ']', '#']
    , elements ['\n', '\t', '\0', '\a']
    ]

arbitraryPat :: Gen Pat
arbitraryPat = frequency
    [ (4, fmap PConstructor arbitraryBig)
    , (1, liftM2 PConstruction arbitraryBig arbitrary)
    , (4, fmap PVar arbitrary)
    ]

arbitraryType :: Gen Type
arbitraryType = frequency
    [ (1, fmap TVar arbitrary)
    , (4, fmap TPrim arbitrary)
    , (1, applyArbitrary2 TFun)
    ]

arbitraryNonEmpty :: Arbitrary a => Gen (NonEmpty a)
arbitraryNonEmpty = liftM2
    (\a as -> a :| as)
    arbitrary
    (choose (0, 4) >>= flip vectorOf arbitrary)

arbitraryBig :: Gen String
arbitraryBig = do
    c <- liftM2 (:) (choose ('A', 'Z')) arbitraryRestIdent
    if elem c reserveds then arbitraryBig else pure c

arbitrarySmall :: Gen String
arbitrarySmall = do
    let first = frequency [(26, choose ('a', 'z')), (4, elements ['_', '?'])]
    firsts <- frequency
        [ (10, fmap pure first)
        , ( 1
          , liftM2 (\a b -> a : [b]) (elements ['-', '+']) (choose ('a', 'z'))
          )
        ]
    rest <- arbitraryRestIdent
    let id = firsts ++ rest
    if elem id reserveds then arbitrarySmall else pure id

arbitraryRestIdent :: Gen String
arbitraryRestIdent = vectorOf' (0, 8) c
  where
    c = frequency
        [ (26, choose ('a', 'z'))
        , (26, choose ('A', 'Z'))
        , (4, elements ['_', '-', '+', '?'])
        ]

vectorOf' :: (Int, Int) -> Gen a -> Gen [a]
vectorOf' r ga = flip vectorOf ga =<< choose r

shrinkProgram :: Program -> [Program]
shrinkProgram (Program main defs tdefs) =
    [ Program main' defs' tdefs'
    | (main', defs', tdefs') <- shrink (main, defs, tdefs)
    ]

shrinkTypeDef :: TypeDef -> [TypeDef]
shrinkTypeDef (TypeDef x tvs cs) = map (uncurry (TypeDef x)) (shrink (tvs, cs))

shrinkExpr' :: Expr' -> [Expr']
shrinkExpr' = \case
    App f x ->
        [Lit Unit, unpos f, unpos x]
            ++ [ App f' x' | (f', x') <- shrink (f, x) ]
    If p c a ->
        [Lit Unit, unpos p, unpos c, unpos a]
            ++ [ If p' c' a' | (p', c', a') <- shrink (p, c, a) ]
    Fun p b -> [Lit Unit, unpos b] ++ [ Fun p' b' | (p', b') <- shrink (p, b) ]
    Let bs x ->
        [Lit Unit, unpos x] ++ [ Let bs' x' | (bs', x') <- shrink (bs, x) ]
    Match e cs ->
        [Lit Unit, unpos e] ++ [ Match e' cs' | (e', cs') <- shrink (e, cs) ]
    FunMatch cs -> Lit Unit : map FunMatch (shrink cs)
    _ -> []

shrinkPat :: Pat -> [Pat]
shrinkPat = \case
    PConstruction c ps -> PConstructor c : map (PConstruction c) (shrink ps)
    _ -> []
