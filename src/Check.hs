{-# LANGUAGE LambdaCase, OverloadedStrings, TemplateHaskell, TupleSections
  , TypeSynonymInstances, FlexibleInstances #-}

module Check
    ( typecheck
    , unify''
    , Scheme(..)
    , scmParams
    , scmBody
    , CExpr
    , CProgram
    , Defs(..)
    )
where

import Control.Lens ((<<+=), assign, makeLenses, over, use, view)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Bifunctor
import Data.Composition
import Data.Graph (SCC(..), flattenSCC, stronglyConnComp)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List

import Misc
import NonEmpty
import Annot
import qualified Ast
import Ast (TVar(..), TConst(..), Type(..), Const(..), Def, Id(..))

data Scheme = Forall
    { _scmParams :: (Set TVar)
    , _scmBody :: Type
    } deriving (Show, Eq)
makeLenses ''Scheme

newtype Defs =
    Defs (Map String (Scheme, CExpr))

type CExpr = Expr Type Defs

type CProgram = Program Type Defs

type TypeErr = String

type Env = Map String Scheme

-- | Map of substitutions from type-variables to more specific types
type Subst = Map TVar Type

data St = St
    { _tvCount :: Int
    , _substs :: Subst
    }

makeLenses ''St

-- TODO: Try handling substitution maps in the state or a monad of its own
-- | Type checker monad
type Infer a = ReaderT Env (StateT St (Except TypeErr)) a

typecheck :: Ast.Program -> Either TypeErr CProgram
typecheck = runInfer . inferProgram

runInfer :: Infer CProgram -> Either TypeErr CProgram
runInfer m = runExcept $ do
    (p, st) <- runStateT (runReaderT m builtinSchemes) initSt
    let s = view substs st
    pure (substProgram s p)

builtinSchemes :: Map String Scheme
builtinSchemes = Map.fromList
    [("printInt", Forall Set.empty (TFun (TConst TInt) (TConst TUnit)))]

initSt :: St
initSt = St {_tvCount = 0, _substs = Map.empty}

fresh :: Infer Type
fresh = fmap (TVar . TVImplicit) (tvCount <<+= 1)

withLocals :: [(String, Scheme)] -> Infer a -> Infer a
withLocals = withLocals' . Map.fromList

withLocals' :: Map String Scheme -> Infer a -> Infer a
withLocals' = local . Map.union

withLocal :: (String, Scheme) -> Infer a -> Infer a
withLocal b = local (uncurry Map.insert b)

-- Inference
--------------------------------------------------------------------------------
inferProgram :: Ast.Program -> Infer CProgram
inferProgram (Ast.Program main defs) = do
    let allDefs = ("main", main) : defs
    Defs allDefs' <- inferDefs allDefs
    let (Forall _ mainT, main') = fromJust (Map.lookup "main" allDefs')
    let defs' = Map.delete "main" allDefs'
    unify Ast.mainType mainT
    pure (Program main' (Defs defs'))

inferDefs :: [Def] -> Infer Defs
inferDefs defs = do
    let ordered = orderDefs defs
    inferDefsComponents ordered

-- For unification to work properly with mutually recursive functions,
-- we need to create a dependency graph of non-recursive /
-- directly-recursive functions and groups of mutual functions. We do
-- this by creating a directed acyclic graph (DAG) of strongly
-- connected components (SCC), where a node is a definition and an
-- edge is a reference to another definition. For each SCC, we infer
-- types for all the definitions / the single definition before
-- generalizing.
orderDefs :: [Def] -> [SCC Def]
orderDefs = stronglyConnComp . graph
    where graph = map (\d@(n, _) -> (d, n, Set.toList (freeVars d)))

inferDefsComponents :: [SCC Def] -> Infer Defs
inferDefsComponents = \case
    [] -> pure (Defs Map.empty)
    (scc : sccs) -> do
        let (idents, bodies) = unzip (flattenSCC scc)
        let names = map (\(Id x) -> x) idents
        ts <- replicateM (length names) fresh
        bodies' <-
            withLocals (zip names (map (Forall Set.empty) ts))
            $ forM (zip bodies ts)
            $ \(body, t1) -> do
                  (t2, body') <- infer body
                  unify t1 t2
                  pure body'
        scms <- mapM generalize ts
        let annotDefs = Map.fromList (zip names (zip scms bodies'))
        Defs annotRest <- withLocals (zip names scms) (inferDefsComponents sccs)
        pure (Defs (Map.union annotRest annotDefs))

infer :: Ast.Expr -> Infer (Type, CExpr)
infer = \case
    Ast.Lit l -> pure (litType l, Lit l)
    Ast.Var x@(Id x') -> fmap (\t -> (t, Var (TypedVar x' t))) (lookupEnv x)
    Ast.App f a -> do
        (tf, f') <- infer f
        (ta, a') <- infer a
        tr <- fresh
        unify tf (TFun ta tr)
        pure (tr, App f' a')
    Ast.If p c a -> do
        (tp, p') <- infer p
        (tc, c') <- infer c
        (ta, a') <- infer a
        unify (TConst TBool) tp
        unify tc ta
        pure (tc, If p' c' a')
    Ast.Fun (Id p) b -> do
        tp <- fresh
        (tb, b') <- withLocal (p, Forall Set.empty tp) (infer b)
        pure (TFun tp tb, Fun (p, tp) (b', tb))
    Ast.Let defs b -> do
        Defs annotDefs <- inferDefs (nonEmptyToList defs)
        let defsScms = fmap (\(scm, _) -> scm) annotDefs
        withLocals' defsScms (infer b)
    Ast.TypeAscr x t -> do
        (tx, x') <- infer x
        unify t tx
        pure (t, x')
    Ast.Match _ _ -> undefined
    Ast.FunMatch _ -> undefined
    Ast.Constructor _ -> undefined

litType :: Const -> Type
litType = \case
    Unit -> TConst TUnit
    Int _ -> TConst TInt
    Double _ -> TConst TDouble
    Char _ -> TConst TChar
    Str _ -> TConst TStr
    Bool _ -> TConst TBool

lookupEnv :: Id -> Infer Type
lookupEnv (Id x) = asks (Map.lookup x) >>= \case
    Just scm -> instantiate scm
    Nothing -> throwError ("Unbound variable: " ++ show x)

-- Substitution
--------------------------------------------------------------------------------
substProgram :: Subst -> CProgram -> CProgram
substProgram s (Program main (Defs defs)) =
    Program (substExpr s main) (Defs (fmap (substDef s) defs))

substDef :: Subst -> (Scheme, CExpr) -> (Scheme, CExpr)
substDef s = bimap id (substExpr s)

substExpr :: Subst -> CExpr -> CExpr
substExpr s = \case
    Lit c -> Lit c
    Var (TypedVar x t) -> Var (TypedVar x (subst s t))
    App f a -> App (substExpr s f) (substExpr s a)
    If p c a -> If (substExpr s p) (substExpr s c) (substExpr s a)
    Fun (p, tp) (b, bt) -> Fun (p, subst s tp) (substExpr s b, subst s bt)
    Let (Defs defs) body ->
        Let (Defs (fmap (substDef s) defs)) (substExpr s body)

subst :: Subst -> Type -> Type
subst s t = case t of
    TVar tv -> fromMaybe t (Map.lookup tv s)
    TConst _ -> t
    TFun a b -> TFun (subst s a) (subst s b)

substEnv :: Subst -> Env -> Env
substEnv s env = fmap (over scmBody (subst s)) env

composeSubsts :: Subst -> Subst -> Subst
composeSubsts s1 s2 = Map.union (fmap (subst s1) s2) s1

-- Unification
--------------------------------------------------------------------------------
unify :: Type -> Type -> Infer ()
unify t1 t2 = do
    s1 <- use substs
    s2 <- unify' (subst s1 t1) (subst s1 t2)
    assign substs (composeSubsts s2 s1)

unify' :: Type -> Type -> Infer Subst
unify' = lift . lift .* unify''

unify'' :: Type -> Type -> Except TypeErr Subst
unify'' = curry $ \case
    (TConst a, TConst b) | a == b -> pure Map.empty
    (TVar a, TVar b) | a == b -> pure Map.empty
    (TVar a, t) | occursIn a t ->
        throwError (concat ["Infinite type: ", show a, ", ", show t])
    -- Consider explicit (user given) type variables dominant of implicit ones.
    -- In the end-result type signature we want the user's names to be preserved
    -- as far as possible.
    (a@(TVar (TVExplicit _)), b@(TVar (TVImplicit _))) -> unify'' b a
    -- If encountering two explicits, prefer the "lower" one. E.g. "a" between
    -- "a" and "b".
    (a@(TVar (TVExplicit sa)), b@(TVar (TVExplicit sb))) | sa > sb -> unify'' b a
    (TVar a, t) -> pure (Map.singleton a t)
    (t, TVar a) -> unify'' (TVar a) t
    (TFun t1 t2, TFun t1' t2') -> do
        s1 <- unify'' t1 t1'
        s2 <- unify'' (subst s1 t2) (subst s1 t2')
        pure (composeSubsts s2 s1)
    (t1, t2) ->
        throwError (concat ["Unification failed: ", show t1, ", ", show t2])

occursIn :: TVar -> Type -> Bool
occursIn a t = Set.member a (ftv t)

-- Instantiation and generalization
--------------------------------------------------------------------------------
instantiate :: Scheme -> Infer Type
instantiate (Forall params t) = do
    let params' = Set.toList params
    args <- mapM (const fresh) params'
    pure (subst (Map.fromList (zip params' args)) t)

generalize :: Type -> Infer Scheme
generalize t = do
    env <- ask
    s <- use substs
    let t' = subst s t
    pure (Forall (generalize' (substEnv s env) t') t')

generalize' :: Env -> Type -> Set TVar
generalize' env t = Set.difference (ftv t) (ftvEnv env)

-- Free type variables
--------------------------------------------------------------------------------
ftv :: Type -> Set TVar
ftv = \case
    TVar tv -> Set.singleton tv
    TConst _ -> Set.empty
    TFun t1 t2 -> Set.union (ftv t1) (ftv t2)

ftvEnv :: Env -> Set TVar
ftvEnv env = Set.unions (map (ftvScheme . snd) (Map.toList env))

ftvScheme :: Scheme -> Set TVar
ftvScheme (Forall tvs t) = Set.difference (ftv t) tvs

instance Pretty CProgram where
    pretty' = prettyProg

instance Pretty Defs where
    pretty' = prettyDefs

instance Pretty Scheme where
    pretty' _ = prettyScheme

prettyScheme :: Scheme -> String
prettyScheme (Forall ps b) = concat
    ["forall ", intercalate " " (map pretty (Set.toList ps)), ". ", pretty b]

prettyDefs :: Int -> Defs -> String
prettyDefs d (Defs binds) = intercalate
    ("\n" ++ replicate (d + 6) ' ')
    (map (prettyBinding (d + 6)) (Map.toList binds))
  where
    prettyBinding d (name, (scm, body)) =
        prettyBracketPair d (name, body) ++ " ; " ++ pretty scm

prettyProg :: Int -> CProgram -> String
prettyProg d (Annot.Program main (Check.Defs defs)) =
    let
        allDefs = ("main", (Check.Forall Set.empty Ast.mainType, main))
            : Map.toList defs
        prettyDef (name, (scm, val)) = concat
            [ replicate d ' '
            , "(define "
            , name
            , " ; "
            , pretty scm
            , "\n"
            , replicate (d + 2) ' '
            , pretty' (d + 2) val
            , ")"
            ]
    in unlines (map prettyDef allDefs)
