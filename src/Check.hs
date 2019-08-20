{-# LANGUAGE LambdaCase, OverloadedStrings, TemplateHaskell, TupleSections
  , TypeSynonymInstances, FlexibleInstances #-}

module Check (typecheck, unify'') where

import Control.Lens
    ((<<+=), assign, makeLenses, over, use, view, views, locally, mapped)
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

import Misc
import NonEmpty
import qualified Ast
import AnnotAst

type TypeErr = String

data Env = Env
    { _envDefs :: Map String Scheme
    , _envTypeDefs :: Map String Ast.TypeDef
    }
makeLenses ''Env

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

typecheck :: Ast.Program -> Either TypeErr Program
typecheck = runInfer . inferProgram

runInfer :: Infer Program -> Either TypeErr Program
runInfer m = runExcept $ do
    (p, st) <- runStateT (runReaderT m initEnv) initSt
    let s = view substs st
    pure (substProgram s p)

initEnv :: Env
initEnv = Env {_envDefs = builtinSchemes, _envTypeDefs = Map.empty}

builtinSchemes :: Map String Scheme
builtinSchemes = Map.fromList
    [("printInt", Forall Set.empty (TFun (TPrim TInt) (TPrim TUnit)))]

initSt :: St
initSt = St {_tvCount = 0, _substs = Map.empty}

fresh :: Infer Type
fresh = fmap (TVar . TVImplicit) (tvCount <<+= 1)

withTypes :: [Ast.TypeDef] -> Infer a -> Infer a
withTypes = locally envTypeDefs . Map.union . Map.fromList . map nameTypeDef
    where nameTypeDef td@(Ast.TypeDef x _ _) = (x, td)

withLocals :: [(String, Scheme)] -> Infer a -> Infer a
withLocals = withLocals' . Map.fromList

withLocals' :: Map String Scheme -> Infer a -> Infer a
withLocals' = locally envDefs . Map.union

withLocal :: (String, Scheme) -> Infer a -> Infer a
withLocal b = locally envDefs (uncurry Map.insert b)

-- Inference
--------------------------------------------------------------------------------
inferProgram :: Ast.Program -> Infer Program
inferProgram (Ast.Program main defs tdefs) = do
    let allDefs = ("main", main) : defs
    Defs allDefs' <- withTypes tdefs (inferDefs allDefs)
    let (Forall _ mainT, main') = fromJust (Map.lookup "main" allDefs')
    unify Ast.mainType mainT
    let defs' = Map.delete "main" allDefs'
    pure (Program main' (Defs defs'))

inferDefs :: [Ast.Def] -> Infer Defs
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
orderDefs :: [Ast.Def] -> [SCC Ast.Def]
orderDefs = stronglyConnComp . graph
    where graph = map (\d@(n, _) -> (d, n, Set.toList (freeVars d)))

inferDefsComponents :: [SCC Ast.Def] -> Infer Defs
inferDefsComponents = \case
    [] -> pure (Defs Map.empty)
    (scc : sccs) -> do
        let (idents, rhss) = unzip (flattenSCC scc)
        let (mayscms, bodies) = unzip rhss
        checkUserSchemes (catMaybes mayscms)
        let names = map (\(Ast.Id x) -> x) idents
        ts <- replicateM (length names) fresh
        let
            scms = map
                (\(mayscm, t) -> fromMaybe (Forall Set.empty t) mayscm)
                (zip mayscms ts)
        bodies' <-
            withLocals (zip names scms)
            $ forM (zip bodies (map (view scmBody) scms))
            $ \(body, t1) -> do
                  (t2, body') <- infer body
                  unify t1 t2
                  pure body'
        generalizeds <- mapM generalize ts
        let scms' = zipWith fromMaybe generalizeds mayscms
        let annotDefs = Map.fromList (zip names (zip scms' bodies'))
        Defs annotRest <- withLocals (zip names scms') (inferDefsComponents sccs)
        pure (Defs (Map.union annotRest annotDefs))

-- | Verify that user-provided type signature schemes are valid
checkUserSchemes :: [Scheme] -> Infer ()
checkUserSchemes scms = forM_ scms check
  where
    check s1@(Forall _ t) = generalize t >>= \s2 ->
        when (not (s1 == s2))
            $ throwError
            $ "Invalid user type signature "
            ++ pretty s1
            ++ ", expected "
            ++ pretty s2

infer :: Ast.Expr -> Infer (Type, Expr)
infer = \case
    Ast.Lit l -> pure (litType l, Lit l)
    Ast.Var x@(Ast.Id x') -> fmap (\t -> (t, Var (TypedVar x' t))) (lookupEnv x)
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
        unify (TPrim TBool) tp
        unify tc ta
        pure (tc, If p' c' a')
    Ast.Fun (Ast.Id p) b -> do
        tp <- fresh
        (tb, b') <- withLocal (p, Forall Set.empty tp) (infer b)
        pure (TFun tp tb, Fun (p, tp) (b', tb))
    Ast.Let defs b -> do
        Defs annotDefs <- inferDefs (toList1 defs)
        let defsScms = fmap (\(scm, _) -> scm) annotDefs
        (bt, b') <- withLocals' defsScms (infer b)
        pure (bt, Let (Defs annotDefs) b')
    Ast.TypeAscr x t -> do
        (tx, x') <- infer x
        unify t tx
        pure (t, x')
    Ast.Match _ _ -> undefined
    Ast.FunMatch _ -> undefined
    Ast.Constructor _ -> undefined

litType :: Const -> Type
litType = \case
    Unit -> TPrim TUnit
    Int _ -> TPrim TInt
    Double _ -> TPrim TDouble
    Char _ -> TPrim TChar
    Str _ -> TPrim TStr
    Bool _ -> TPrim TBool

lookupEnv :: Ast.Id -> Infer Type
lookupEnv (Ast.Id x) = views envDefs (Map.lookup x) >>= \case
    Just scm -> instantiate scm
    Nothing -> throwError ("Unbound variable: " ++ x)

-- Substitution
--------------------------------------------------------------------------------
substProgram :: Subst -> Program -> Program
substProgram s (Program main (Defs defs)) =
    Program (substExpr s main) (Defs (fmap (substDef s) defs))

substDef :: Subst -> (Scheme, Expr) -> (Scheme, Expr)
substDef s = bimap id (substExpr s)

substExpr :: Subst -> Expr -> Expr
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
    TPrim _ -> t
    TFun a b -> TFun (subst s a) (subst s b)
    TConst c ts -> TConst c (map (subst s) ts)

substEnv :: Subst -> Env -> Env
substEnv s = over (envDefs . mapped . scmBody) (subst s)

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
    (TPrim a, TPrim b) | a == b -> pure Map.empty
    (TVar a, TVar b) | a == b -> pure Map.empty
    (TVar a, t) | occursIn a t ->
        throwError (concat ["Infinite type: ", pretty a, ", ", pretty t])
    -- Do not allow "override" of explicit (user given) type variables.
    (a@(TVar (TVExplicit _)), b@(TVar (TVImplicit _))) -> unify'' b a
    (a@(TVar (TVExplicit _)), b) ->
        throwError $ "Unification failed: " ++ pretty a ++ ", " ++ pretty b
    (TVar a, t) -> pure (Map.singleton a t)
    (t, TVar a) -> unify'' (TVar a) t
    (TFun t1 t2, TFun t1' t2') -> do
        s1 <- unify'' t1 t1'
        s2 <- unify'' (subst s1 t2) (subst s1 t2')
        pure (composeSubsts s2 s1)
    (t1, t2) -> throwError
        (concat ["Unification failed: ", pretty t1, ", ", pretty t2])

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
    TPrim _ -> Set.empty
    TFun t1 t2 -> Set.union (ftv t1) (ftv t2)
    TConst _ ts -> Set.unions (map ftv ts)

ftvEnv :: Env -> Set TVar
ftvEnv = Set.unions . map (ftvScheme . snd) . Map.toList . view envDefs

ftvScheme :: Scheme -> Set TVar
ftvScheme (Forall tvs t) = Set.difference (ftv t) tvs
