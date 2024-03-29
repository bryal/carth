{-# LANGUAGE TemplateHaskell #-}

-- | Implementation of the algorithm described in /ML pattern match compilation and partial
--   evaluation/ by Peter Sestoft. Close to 1:1, and includes the additional checks for
--   exhaustiveness and redundancy described in section 7.4.
module Front.Match (toDecisionTree, Span, Con(..), Access(..), MTypeDefs) where

import Prelude hiding (span)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.List (delete)
import Data.Functor
import Control.Arrow
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Word
import Lens.Micro.Platform (makeLenses, view, to)

import Misc hiding (augment)
import Pretty
import Front.SrcPos
import Front.Err
import qualified Front.Inferred as Inferred
import Front.Inferred (Pat (..), Pat'(..), Variant(..))
import Front.Checked


data Descr = Pos Con [Descr] | Neg (Set Con)
    deriving Show

data Answer = Yes | No | Maybe

type Ctx = [(Con, [Descr])]

data DecisionTree'
    = Success (VarBindings, Expr)
    | IfEq Access Con DecisionTree' DecisionTree'
    deriving Show

type Rhs = (SrcPos, VarBindings, Expr)

type MTypeDefs = Map String [String]

type RedundantCases = [SrcPos]

data Env = Env
    { _tdefs :: MTypeDefs
    , _tpats :: [Type]
    , _exprPos :: SrcPos
    }
makeLenses ''Env

type Match = ReaderT Env (StateT RedundantCases (ExceptT TypeErr Maybe))

type Work = [([Pat], [Access], [Descr])]

newtype FunPats = FunPats [Pat]
    deriving Show

toDecisionTree
    :: MTypeDefs
    -> SrcPos
    -> [Type]
    -> [(WithPos [Pat], Expr)]
    -> ExceptT TypeErr Maybe DecisionTree
toDecisionTree tds ePos tp cases =
    let rules = map (\(WithPos pos ps, e) -> (FunPats ps, (pos, Map.empty, e))) cases
        redundantCases = map (getPos . fst) cases
    in  do
            let env = Env { _tdefs = tds, _tpats = tp, _exprPos = ePos }
            (d, redundantCases') <- runStateT (runReaderT (compile rules) env) redundantCases
            forM_ redundantCases' $ throwError . RedundantCase
            pure (switchify d)
    where compile = disjunct (Neg Set.empty)

disjunct :: Descr -> [(FunPats, Rhs)] -> Match DecisionTree'
disjunct descr = \case
    [] -> do
        patStr <- view tpats >>= missingFunPats descr
        exprPos' <- view exprPos
        throwError $ InexhaustivePats exprPos' patStr
    (pat1, rhs1) : rulerest -> matchFunPats descr [] [] rhs1 rulerest pat1
  where
    missingFunPats :: Descr -> [Type] -> Match String
    -- This case should only occur when there are uninhabited types involved.
    missingFunPats (Neg _) _ = lift $ lift $ lift Nothing
    missingFunPats (Pos _ descrs) ts = do
        ps <- zipWithM missingPat ts descrs
        pure ("[" ++ unwords ps ++ "]")

    missingPat :: Type -> Descr -> Match String
    missingPat t descr = case t of
        TVar _ -> underscore
        TPrim _ -> underscore
        TConst ("Str", _) -> underscore
        TConst (tx, _) -> do
            vs <- view (tdefs . to (fromJust . Map.lookup tx))
            missingPat' vs descr
        TFun _ _ -> underscore
        TBox _ -> underscore
        where underscore = pure ("_:" ++ pretty t ++ "")

    missingPat' :: [String] -> Descr -> Match String
    missingPat' vs =
        let
            allVariants = Map.fromList (zip [0 ..] vs)
            variant' = \case
                Con (VariantIx v) _ _ -> v
                Con (VariantStr _) _ _ -> ice "variant' of Con VariantStr"
        in
            \case
                Neg cs -> lift $ lift $ lift $ listToMaybe $ Map.elems
                    (Map.withoutKeys allVariants (Set.map variant' cs))
                Pos (Con (VariantStr _) _ _) _ -> ice "missingPat' of Con VariantStr"
                Pos (Con (VariantIx v) _ argTs') dargs ->
                    let
                        i = fromIntegral v
                        s = if i < length vs
                            then vs !! i
                            else ice "variant >= type number of variants in missingPat'"
                    in
                        if null dargs
                            then pure s
                            else do
                                ps <- zipWithM missingPat argTs' dargs
                                pure ("(" ++ s ++ precalate " " ps ++ ")")

match :: Access -> Descr -> Ctx -> Work -> Rhs -> [(FunPats, Rhs)] -> Pat -> Match DecisionTree'
match obj descr ctx work rhs rules (Pat _ _ pat) = case pat of
    PVar (Inferred.TypedVar x tx) ->
        let x' = TypedVar x tx in conjunct (augment descr ctx) (addBind x' obj rhs) rules work
    PWild -> conjunct (augment descr ctx) rhs rules work
    PBox p -> match (ADeref obj) descr ctx work rhs rules p
    PCon pcon pargs ->
        let disjunct' :: Descr -> Match DecisionTree'
            disjunct' newDescr = disjunct (buildDescr newDescr ctx work) rules

            conjunct' :: Match DecisionTree'
            conjunct' = conjunct ((pcon, []) : ctx) rhs rules ((pargs, getoargs, getdargs) : work)

            getoargs :: [Access]
            getoargs = args pcon $ \i _ -> Sel (As obj (span pcon) (variantIx pcon)) i (span pcon)

            variantIx = variant >>> \case
                VariantIx ix -> ix
                VariantStr _ -> ice "match: variantIx: VariantStr"

            getdargs :: [Descr]
            getdargs = case descr of
                Neg _ -> args pcon (const (const (Neg Set.empty)))
                Pos _ dargs -> dargs
        in  case staticMatch pcon descr of
                Yes -> conjunct'
                No -> disjunct' descr
                Maybe -> do
                    yes <- conjunct'
                    no <- disjunct' (addneg pcon descr)
                    pure (IfEq obj pcon yes no)

matchFunPats :: Descr -> Ctx -> Work -> Rhs -> [(FunPats, Rhs)] -> FunPats -> Match DecisionTree'
matchFunPats descr ctx work rhs rules (FunPats pats) =
    let ts = map (\(Pat _ t _) -> t) pats
        con = Con { variant = VariantIx 0, span = 1, argTs = ts }
        getoargs = args con (\i _t -> TopSel i)
        getdargs = case descr of
            -- TODO: Does this case ever happen? If the descr refers to the function pattern list,
            --       then there's only one variant to speak of, and therefore Pos by default,
            --       right?
            Neg _ -> args con (const (const (Neg Set.empty)))
            Pos _ dargs -> dargs
    in  conjunct ((con, []) : ctx) rhs rules ((pats, getoargs, getdargs) : work)

args :: Con -> (Word32 -> Type -> a) -> [a]
args con f = zipWith f [0 ..] (argTs con)

conjunct :: Ctx -> Rhs -> [(FunPats, Rhs)] -> Work -> Match DecisionTree'
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

norm :: Ctx -> Ctx
norm = \case
    [] -> []
    ((con, args) : rest) -> augment (Pos con (reverse args)) rest

augment :: Descr -> Ctx -> Ctx
augment descr = \case
    [] -> []
    (con, args) : rest -> (con, descr : args) : rest

staticMatch :: Con -> Descr -> Answer
staticMatch = curry $ \case
    (pcon, Pos c _) | pcon == c -> Yes
                    | otherwise -> No
    (pcon, Neg cs) | Set.member pcon cs -> No
    (Con (VariantIx _) span' _, Neg cs) | span' == 1 + fromIntegral (Set.size cs) -> Yes
    _ -> Maybe

addneg :: Con -> Descr -> Descr
addneg con = \case
    Neg nonset -> Neg (Set.insert con nonset)
    Pos _ _ -> ice "unexpected Pos in addneg"

switchify :: DecisionTree' -> DecisionTree
switchify = \case
    Success e -> DLeaf e
    d@(IfEq obj (Con (VariantIx _) span _) _ _) ->
        uncurry (DSwitch span obj) (switchifyIx obj [] d)
    d@(IfEq obj (Con (VariantStr _) _ _) _ _) -> uncurry (DSwitchStr obj) (switchifyStr obj [] d)
  where
    switchifyIx obj rules = \case
        IfEq obj' con d0 d1 | obj == obj' -> case variant con of
            VariantIx v -> switchifyIx obj ((v, switchify d0) : rules) d1
            VariantStr _ -> ice "VariantStr in switchifyIx"
        rule -> (Map.fromList rules, switchify rule)
    switchifyStr obj rules = \case
        IfEq obj' con d0 d1 | obj == obj' -> case variant con of
            VariantStr v -> switchifyStr obj ((v, switchify d0) : rules) d1
            VariantIx _ -> ice "VariantIx in switchifyIx"
        rule -> (Map.fromList rules, switchify rule)

buildDescr :: Descr -> Ctx -> Work -> Descr
buildDescr descr = curry $ \case
    ([], []) -> descr
    ((con, args) : rest, (_, _, dargs) : work) ->
        buildDescr (Pos con (reverse args ++ (descr : dargs))) rest work
    _ -> ice "unexpected pattern in buildDescr"
