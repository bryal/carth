{-# LANGUAGE LambdaCase, TemplateHaskell, TupleSections #-}

-- | Implementation of the algorithm described in /ML pattern match compilation
--   and partial evaluation/ by Peter Sestoft. Close to 1:1, and includes the
--   additional checks for exhaustiveness and redundancy described in section
--   7.4.
module Match (toDecisionTree, Span, Con(..), Pat(..), MTypeDefs) where

import Prelude hiding (span)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.List (delete)
import Data.Functor
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Word
import Control.Lens (makeLenses, view, views)

import Misc hiding (augment)
import SrcPos
import TypeErr
import AnnotAst


data Con = Con
    { variant :: VariantIx
    , span :: Span
    , argTs :: [Type]
    }
    deriving Show

data Pat
    = PVar TypedVar
    | PWild
    | PCon Con [Pat]
    deriving Show

data Descr = Pos Con [Descr] | Neg (Set Con)
    deriving Show

data Answer = Yes | No | Maybe

type Ctx = [(Con, [Descr])]

type Work = [([Pat], [Access], [Descr])]

data DecisionTree'
    = Success (VarBindings, Expr)
    | IfEq Access Con DecisionTree' DecisionTree'
    deriving Show

type Rhs = (SrcPos, VarBindings, Expr)

type MTypeDefs = Map String [String]

type RedundantCases = [SrcPos]

data Env = Env { _tdefs :: MTypeDefs, _tpat :: Type, _exprPos :: SrcPos }
makeLenses ''Env

type Match = ReaderT Env (StateT RedundantCases (Except TypeErr))


instance Eq Con where
    (==) (Con c1 _ _) (Con c2 _ _) = c1 == c2

instance Ord Con where
    compare (Con c1 _ _) (Con c2 _ _) = compare c1 c2


toDecisionTree
    :: MTypeDefs
    -> SrcPos
    -> Type
    -> [(SrcPos, Pat, Expr)]
    -> Except TypeErr DecisionTree
toDecisionTree tds ePos tp cases =
    let
        rules = map (\(pos, p, e) -> (p, (pos, Map.empty, e))) cases
        redundantCases = map (\(pos, _, _) -> pos) cases
    in do
        let env = Env { _tdefs = tds, _tpat = tp, _exprPos = ePos }
        (d, redundantCases') <- runStateT
            (runReaderT (compile rules) env)
            redundantCases
        forM_ redundantCases' $ throwError . RedundantCase
        pure (switchify d)

compile :: [(Pat, Rhs)] -> Match DecisionTree'
compile = disjunct (Neg Set.empty)

disjunct :: Descr -> [(Pat, Rhs)] -> Match DecisionTree'
disjunct descr = \case
    [] -> do
        patStr <- view tpat >>= flip missingPat descr
        exprPos' <- view exprPos
        throwError $ InexhaustivePats exprPos' patStr
    (pat1, rhs1) : rulerest -> match Obj descr [] [] rhs1 rulerest pat1

missingPat :: Type -> Descr -> Match String
missingPat t descr = case t of
    TVar _ -> pure "_"
    TPrim _ -> pure "_"
    TConst (tx, _) -> do
        vs <- views tdefs (fromJust . Map.lookup tx)
        missingPat' vs descr
    TFun _ _ -> pure "_"
    TBox _ -> pure "_"

missingPat' :: [String] -> Descr -> Match String
missingPat' vs = \case
    Neg cs -> pure $ head $ Map.elems
        (Map.withoutKeys (allVariants vs) (Set.map variant cs))
    Pos con dargs ->
        let
            i = fromIntegral (variant con)
            s = if i < length vs
                then vs !! i
                else ice "variant >= type number of variants in missingPat'"
        in if null dargs
            then pure s
            else do
                ps <- zipWithM missingPat (argTs con) dargs
                pure ("(" ++ s ++ precalate " " ps ++ ")")

allVariants :: [String] -> Map VariantIx String
allVariants = Map.fromList . zip [0 ..]

match
    :: Access
    -> Descr
    -> Ctx
    -> Work
    -> Rhs
    -> [(Pat, Rhs)]
    -> Pat
    -> Match DecisionTree'
match obj descr ctx work rhs rules = \case
    PVar x -> conjunct (augment descr ctx) (addBind x obj rhs) rules work
    PWild -> conjunct (augment descr ctx) rhs rules work
    PCon pcon pargs ->
        let
            disjunct' :: Descr -> Match DecisionTree'
            disjunct' newDescr = disjunct (buildDescr newDescr ctx work) rules

            conjunct' :: Match DecisionTree'
            conjunct' = conjunct
                ((pcon, []) : ctx)
                rhs
                rules
                ((pargs, getoargs, getdargs) : work)

            getoargs :: [Access]
            getoargs =
                args (\i -> Sel i (span pcon) (As obj (span pcon) (argTs pcon)))

            getdargs :: [Descr]
            getdargs = case descr of
                Neg _ -> args (const (Neg Set.empty))
                Pos _ dargs -> dargs

            args :: (Word32 -> a) -> [a]
            args f = map f (take (arity pcon) [0 ..])
        in case staticMatch pcon descr of
            Yes -> conjunct'
            No -> disjunct' descr
            Maybe -> do
                yes <- conjunct'
                no <- disjunct' (addneg pcon descr)
                pure (IfEq obj pcon yes no)

conjunct :: Ctx -> Rhs -> [(Pat, Rhs)] -> Work -> Match DecisionTree'
conjunct ctx rhs@(casePos, binds, e) rules = \case
    [] -> caseReached casePos $> Success (binds, e)
    (work1 : workr) -> case work1 of
        ([], [], []) -> conjunct (norm ctx) rhs rules workr
        (pat1 : patr, obj1 : objr, descr1 : descrr) ->
            match obj1 descr1 ctx ((patr, objr, descrr) : workr) rhs rules pat1
        x -> ice $ "unexpected pattern in conjunct: " ++ show x

caseReached :: SrcPos -> Match ()
caseReached p = modify (delete p)

addBind :: TypedVar -> Access -> Rhs -> Rhs
addBind x obj (pos, binds, e) = (pos, Map.insert x obj binds, e)

arity :: Con -> Int
arity = length . argTs

buildDescr :: Descr -> Ctx -> Work -> Descr
buildDescr descr = curry $ \case
    ([], []) -> descr
    ((con, args) : rest, (_, _, dargs) : work) ->
        buildDescr (Pos con (reverse args ++ (descr : dargs))) rest work
    _ -> ice "unexpected pattern in buildDescr"

norm :: Ctx -> Ctx
norm = \case
    [] -> []
    ((con, args) : rest) -> augment (Pos con (reverse args)) rest

augment :: Descr -> Ctx -> Ctx
augment descr = \case
    [] -> []
    (con, args) : rest -> (con, descr : args) : rest

staticMatch :: Con -> Descr -> Answer
staticMatch pcon = \case
    Pos c _
        | pcon == c -> Yes
        | otherwise -> No
    Neg cs
        | Set.member pcon cs -> No
        | span pcon == 1 + fromIntegral (Set.size cs) -> Yes
    _ -> Maybe

addneg :: Con -> Descr -> Descr
addneg con = \case
    Neg nonset -> Neg (Set.insert con nonset)
    Pos _ _ -> ice "unexpected Pos in addneg"

switchify :: DecisionTree' -> DecisionTree
switchify = \case
    Success e -> DLeaf e
    d@(IfEq obj _ _ _) -> uncurry (DSwitch obj) (switchify' obj [] d)

switchify'
    :: Access
    -> [(VariantIx, DecisionTree)]
    -> DecisionTree'
    -> (Map VariantIx DecisionTree, DecisionTree)
switchify' obj rules = \case
    IfEq obj' con d0 d1 | obj == obj' ->
        switchify' obj ((variant con, switchify d0) : rules) d1
    rule -> (Map.fromList rules, switchify rule)
