{-# LANGUAGE LambdaCase #-}

-- | Implementation of the algorithm described in /ML pattern match compilation
--   and partial evaluation/ by Peter Sestoft. Close to 1:1, and includes the
--   additional checks for exhaustiveness and redundancy described in section
--   7.4.
module Match where

import Prelude hiding (span)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.List (delete)
import Data.Functor
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Except

import Misc hiding (augment)
import SrcPos
import AnnotAst


data Con = Con { variant :: VariantIx, arity :: Int, span :: Int }
    deriving Show

data Pat
    = PVar String
    | PCon Con [Pat]
    deriving Show

data Descr = Pos Con [Descr] | Neg (Set Con)
    deriving Show

data Answer = Yes | No | Maybe

type Ctx = [(Con, [Descr])]

type Work = [([Pat], [Access], [Descr])]

data Access = Obj | Sel Int Access
    deriving Show

data DecisionDag
    = Success Expr
    | IfEq Access Con DecisionDag DecisionDag
    deriving Show

type Rhs = (SrcPos, Expr)

type TypeDefs' = Map String [(String, [Type])]

type RedundantCases = [SrcPos]

type Match = ReaderT TypeDefs' (StateT RedundantCases (Except String))


instance Eq Con where
    (==) (Con c1 _ _) (Con c2 _ _) = c1 == c2

instance Ord Con where
    compare (Con c1 _ _) (Con c2 _ _) = compare c1 c2


compile
    :: TypeDefs' -> (Type, [(SrcPos, Pat, Expr)]) -> Either String DecisionDag
compile tds (t, cases) =
    let
        rules = (t, map (\(pos, p, e) -> (p, (pos, e))) cases)
        redundantCases = map (\(pos, _, _) -> pos) cases
    in runExcept $ do
        (d, redundantCases') <- runStateT
            (runReaderT (compile' rules) tds)
            redundantCases
        forM_ redundantCases' $ throwError . ("Redundant case: " ++) . show
        pure d

compile' :: (Type, [(Pat, Rhs)]) -> Match DecisionDag
compile' = disjunct (Neg Set.empty)


disjunct :: Descr -> (Type, [(Pat, Rhs)]) -> Match DecisionDag
disjunct descr = \case
    (tpat, []) -> do
        p <- missingPat tpat descr
        throwError $ "Inexhaustive patterns: " ++ p ++ " not covered"
    (tpat, (pat1, rhs1) : rulerest) ->
        match Obj descr [] [] rhs1 (tpat, rulerest) pat1

missingPat :: Type -> Descr -> Match String
missingPat t descr = case t of
    TVar _ -> pure "_"
    TPrim _ -> pure "_"
    TConst (tx, _) -> do
        vs <- asks (fromJust . Map.lookup tx)
        missingPat' vs descr
    TFun _ _ -> pure "_"

missingPat' :: [(String, [Type])] -> Descr -> Match String
missingPat' vs = \case
    Neg cs -> pure $ head $ Map.elems
        (Map.withoutKeys (allVariants vs) (Set.map variant cs))
    Pos con dargs ->
        let
            i = fromIntegral (variant con)
            (s, ts) = vs !! i
        in if null dargs
            then pure s
            else do
                ps <- zipWithM missingPat ts dargs
                pure ("(" ++ s ++ precalate " " ps ++ ")")

allVariants :: [(String, [Type])] -> Map VariantIx String
allVariants = Map.fromList . zip [0 ..] . map fst

match
    :: Access
    -> Descr
    -> Ctx
    -> Work
    -> Rhs
    -> (Type, [(Pat, Rhs)])
    -> Pat
    -> Match DecisionDag
match obj descr ctx work rhs rules = \case
    PVar _ -> conjunct (augment descr ctx) rhs rules work
    PCon pcon pargs ->
        let
            disjunct' :: Descr -> Match DecisionDag
            disjunct' newDescr = disjunct (buildDescr newDescr ctx work) rules

            conjunct' :: Match DecisionDag
            conjunct' = conjunct
                ((pcon, []) : ctx)
                rhs
                rules
                ((pargs, getoargs, getdargs) : work)

            getoargs :: [Access]
            getoargs = args (\i -> Sel (i + 1) obj)

            getdargs :: [Descr]
            getdargs = case descr of
                Neg _ -> args (const (Neg Set.empty))
                Pos _ dargs -> dargs

            args :: (Int -> a) -> [a]
            args f = map f ([0 .. arity pcon - 1])
        in case staticMatch pcon descr of
            Yes -> conjunct'
            No -> disjunct' descr
            Maybe ->
                liftA2 (IfEq obj pcon) conjunct' (disjunct' (addneg pcon descr))

conjunct :: Ctx -> Rhs -> (Type, [(Pat, Rhs)]) -> Work -> Match DecisionDag
conjunct ctx rhs@(casePos, e) rules = \case
    [] -> caseReached casePos $> Success e
    (work1 : workr) -> case work1 of
        ([], [], []) -> conjunct (norm ctx) rhs rules workr
        (pat1 : patr, obj1 : objr, descr1 : descrr) ->
            match obj1 descr1 ctx ((patr, objr, descrr) : workr) rhs rules pat1
        x -> ice $ "unexpected pattern in conjunct: " ++ show x

caseReached :: SrcPos -> Match ()
caseReached p = modify (delete p)

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
        | span pcon == 1 + Set.size cs -> Yes
    _ -> Maybe

addneg :: Con -> Descr -> Descr
addneg con = \case
    Neg nonset -> Neg (Set.insert con nonset)
    Pos _ _ -> ice "unexpected Pos in addneg"
