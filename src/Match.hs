{-# LANGUAGE LambdaCase #-}

-- | Instantiation of the algorithm described in /ML pattern match compilation
--   and partial evaluation/ by Peter Sestoft.
module Match where

import Prelude hiding (span)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Composition
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Except

import Misc hiding (augment)
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
    = Failure Type Descr
    | Success Expr
    | IfEq Access Con DecisionDag DecisionDag
    deriving Show


instance Eq Con where
    (==) (Con c1 _ _) (Con c2 _ _) = c1 == c2

instance Ord Con where
    compare (Con c1 _ _) (Con c2 _ _) = compare c1 c2


-- Exhaustiveness
--------------------------------------------------------------------------------

data DecisionExhaustive
    = SuccessE Expr
    | IfEqE Access Con DecisionExhaustive DecisionExhaustive
    deriving Show

type TypeDefs' = Map String [(String, [Type])]

type M = ReaderT TypeDefs' (Except String)

runM :: TypeDefs' -> M a -> Either String a
runM = runExcept .* flip runReaderT

exhaustive
    :: TypeDefs' -> (Type, [(Pat, Expr)]) -> Either String DecisionExhaustive
exhaustive tds = runM tds . exhaustive' . compile

exhaustive' :: DecisionDag -> M DecisionExhaustive
exhaustive' = \case
    Failure tpat descr ->
        throwError
            $ "Inexhaustive patterns: "
            ++ missingPat tpat descr
            ++ " not covered"
    Success e -> pure (SuccessE e)
    IfEq obj con d1 d2 ->
        liftA2 (IfEqE obj con) (exhaustive' d1) (exhaustive' d2)

missingPat :: Type -> Descr -> String
missingPat t descr = case t of
    TVar _ -> "_"
    TPrim _ -> "_"
    TConst (tx, _) ->
        let vs = fromJust (Map.lookup tx datatypes)
        in
            case descr of
                Neg cs -> head $ Map.elems $ Map.withoutKeys
                    (allVariants vs)
                    (Set.map variant cs)
                Pos con dargs ->
                    let
                        i = fromIntegral (variant con)
                        (s, ts) = vs !! i
                    in if null dargs
                        then s
                        else
                            "("
                            ++ s
                            ++ precalate " " (zipWith missingPat ts dargs)
                            ++ ")"
    TFun _ _ -> "_"

allVariants :: [(String, [Type])] -> Map VariantIx String
allVariants = Map.fromList . zip [0 ..] . map fst

-- Sestoft's algorithm, basically 1:1
--------------------------------------------------------------------------------

compile :: (Type, [(Pat, Expr)]) -> DecisionDag
compile = disjunct (Neg Set.empty)

disjunct :: Descr -> (Type, [(Pat, Expr)]) -> DecisionDag
disjunct descr = \case
    (tpat, []) -> Failure tpat descr
    (tpat, (pat1, rhs1) : rulerest) ->
        match Obj descr [] [] rhs1 (tpat, rulerest) pat1

match
    :: Access
    -> Descr
    -> Ctx
    -> Work
    -> Expr
    -> (Type, [(Pat, Expr)])
    -> Pat
    -> DecisionDag
match obj descr ctx work rhs rules = \case
    PVar _ -> conjunct (augment descr ctx) rhs rules work
    PCon pcon pargs ->
        let
            disjunct' :: Descr -> DecisionDag
            disjunct' newDescr = disjunct (buildDescr newDescr ctx work) rules

            conjunct' :: DecisionDag
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
            Maybe -> IfEq obj pcon conjunct' (disjunct' (addneg pcon descr))

conjunct :: Ctx -> Expr -> (Type, [(Pat, Expr)]) -> Work -> DecisionDag
conjunct ctx rhs rules = \case
    [] -> Success rhs
    (work1 : workr) -> case work1 of
        ([], [], []) -> conjunct (norm ctx) rhs rules workr
        (pat1 : patr, obj1 : objr, descr1 : descrr) ->
            match obj1 descr1 ctx ((patr, objr, descrr) : workr) rhs rules pat1
        x -> ice $ "unexpected pattern in conjunct: " ++ show x

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
