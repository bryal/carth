{-# LANGUAGE LambdaCase, OverloadedStrings, TemplateHaskell,
  TupleSections #-}

module Check
    ( typecheck
    , unify''
    ) where

import Annot
       (Scheme(..), TVar, Type(..), typeBool, typeChar, typeDouble,
        typeInt, typeStr, typeUnit)
import qualified Annot
import Ast
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
import NonEmpty

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

typecheck :: Program -> Either TypeErr Annot.Program
typecheck = runInfer . inferProgram

runInfer :: Infer Annot.Program -> Either TypeErr Annot.Program
runInfer m =
    runExcept $ do
        (p, st) <- runStateT (runReaderT m builtinSchemes) initSt
        let s = view substs st
        pure (substProgram s p)

builtinSchemes :: Map String Scheme
builtinSchemes =
    Map.fromList
        [ ("printInt", Forall Set.empty (TFun typeInt typeUnit))
        , ("+", Forall Set.empty (TFun typeInt (TFun typeInt typeInt)))
        ]

initSt :: St
initSt = St {_tvCount = 0, _substs = Map.empty}

fresh :: Infer Type
fresh = fmap (TVar . ("#" ++) . show) (tvCount <<+= 1)

withLocals :: [(String, Scheme)] -> Infer a -> Infer a
withLocals = withLocals' . Map.fromList

withLocals' :: Map String Scheme -> Infer a -> Infer a
withLocals' = local . Map.union

withLocal :: (String, Scheme) -> Infer a -> Infer a
withLocal b = local (uncurry Map.insert b)

-- Inference
--------------------------------------------------------------------------------
inferProgram :: Program -> Infer Annot.Program
inferProgram (Program main defs) = do
    let allDefs = ("main", main) : defs
    allDefs' <- inferDefs allDefs
    let (Forall _ mainT, main') = fromJust (Map.lookup "main" allDefs')
    let defs' = Map.delete "main" allDefs'
    unify Annot.mainType mainT
    pure (Annot.Program main' defs')

inferDefs :: [Def] -> Infer Annot.Defs
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
orderDefs defs = stronglyConnComp graph
  where
    graph = map (\def@(name, _) -> (def, name, fvDef def)) defs

inferDefsComponents :: [SCC Def] -> Infer Annot.Defs
inferDefsComponents =
    \case
        [] -> pure Map.empty
        (scc:sccs) -> do
            let (idents, bodies) = unzip (flattenSCC scc)
            let names = map (\(Id x) -> x) idents
            ts <- replicateM (length names) fresh
            bodies' <-
                withLocals (zip names (map (Forall Set.empty) ts)) $
                forM (zip bodies ts) $ \(body, t1) -> do
                    (t2, body') <- infer body
                    unify t1 t2
                    pure body'
            scms <- mapM generalize ts
            let annotDefs = Map.fromList (zip names (zip scms bodies'))
            annotRest <- withLocals (zip names scms) (inferDefsComponents sccs)
            pure (Map.union annotRest annotDefs)

infer :: Expr -> Infer (Type, Annot.Expr)
infer =
    \case
        Lit l -> pure (litType l, Annot.Lit l)
        Var x@(Id x') -> fmap (\t -> (t, Annot.Var x' t)) (lookupEnv x)
        App f a -> do
            (tf, f') <- infer f
            (ta, a') <- infer a
            tr <- fresh
            unify tf (TFun ta tr)
            pure (tr, Annot.App f' a')
        If p c a -> do
            (tp, p') <- infer p
            (tc, c') <- infer c
            (ta, a') <- infer a
            unify typeBool tp
            unify tc ta
            pure (tc, Annot.If p' c' a')
        Fun (Id p) b -> do
            tp <- fresh
            (tb, b') <- withLocal (p, Forall Set.empty tp) (infer b)
            pure (TFun tp tb, Annot.Fun (p, tp) b')
        Let defs b -> do
            annotDefs <- inferDefs (nonEmptyToList defs)
            let defsScms = fmap (\(scm, _) -> scm) annotDefs
            withLocals' defsScms (infer b)
        Match _ _ -> undefined
        FunMatch _ -> undefined
        Constructor _ -> undefined

litType :: Const -> Type
litType =
    \case
        Unit -> typeUnit
        Int _ -> typeInt
        Double _ -> typeDouble
        Char _ -> typeChar
        Str _ -> typeStr
        Bool _ -> typeBool

lookupEnv :: Id -> Infer Type
lookupEnv (Id x) =
    asks (Map.lookup x) >>= \case
        Just scm -> instantiate scm
        Nothing -> throwError ("Unbound variable: " ++ show x)

-- Substitution
--------------------------------------------------------------------------------
substProgram :: Subst -> Annot.Program -> Annot.Program
substProgram s (Annot.Program main defs) =
    Annot.Program (substExpr s main) (fmap (substDef s) defs)

substDef :: Subst -> (Scheme, Annot.Expr) -> (Scheme, Annot.Expr)
substDef s = bimap id (substExpr s)

substExpr :: Subst -> Annot.Expr -> Annot.Expr
substExpr s =
    \case
        Annot.Lit c -> Annot.Lit c
        Annot.Var x t -> Annot.Var x (subst s t)
        Annot.App f a -> Annot.App (substExpr s f) (substExpr s a)
        Annot.If p c a ->
            Annot.If (substExpr s p) (substExpr s c) (substExpr s a)
        Annot.Fun (p, tp) b -> Annot.Fun (p, subst s tp) (substExpr s b)
        Annot.Let defs body ->
            Annot.Let (fmap (substDef s) defs) (substExpr s body)

subst :: Subst -> Type -> Type
subst s t =
    case t of
        TVar tv -> fromMaybe t (Map.lookup tv s)
        TConst _ -> t
        TFun a b -> TFun (subst s a) (subst s b)

substEnv :: Subst -> Env -> Env
substEnv s env = fmap (over Annot.scmBody (subst s)) env

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
unify'' =
    curry $ \case
        (TConst a, TConst b)
            | a == b -> pure Map.empty
        (TVar a, TVar b)
            | a == b -> pure Map.empty
        (TVar a, t)
            | occursIn a t ->
                throwError (concat ["Infinite type: ", a, ", ", show t])
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
ftv =
    \case
        TVar tv -> Set.singleton tv
        TConst _ -> Set.empty
        TFun t1 t2 -> Set.union (ftv t1) (ftv t2)

ftvEnv :: Env -> Set TVar
ftvEnv env = Set.unions (map (ftvScheme . snd) (Map.toList env))

ftvScheme :: Scheme -> Set TVar
ftvScheme (Forall tvs t) = Set.difference (ftv t) tvs

-- Free variables
--------------------------------------------------------------------------------
fvDef :: Def -> [Id]
fvDef (name, body) = Set.toList (Set.delete name (fv body))

fv :: Expr -> Set Id
fv =
    \case
        Lit _ -> nil
        Var x -> Set.singleton x
        App f a -> Set.unions (map fv [f, a])
        If p c a -> Set.unions (map fv [p, c, a])
        Fun p b -> Set.delete p (fv b)
        Let bs e ->
            let fvE = fv e
                fvBs =
                    foldl
                        (\acc b -> Set.union acc (fv b))
                        Set.empty
                        (fmap snd bs)
                bvBs = Set.fromList (map fst (nonEmptyToList bs))
            in Set.difference (Set.union fvE fvBs) bvBs
        Match e cs ->
            Set.union (fv e) (Set.difference (fvClauses cs) (bvClauses cs))
        FunMatch cs -> Set.difference (fvClauses cs) (bvClauses cs)
        Constructor _ -> nil
  where
    fvClauses = foldl (\acc c -> Set.union acc (fv (snd c))) Set.empty
    bvClauses = Set.unions . map (patVars . fst) . nonEmptyToList
    patVars =
        \case
            PConstructor _ -> nil
            PConstruction _ ps -> Set.unions (map patVars (nonEmptyToList ps))
            PVar var -> Set.singleton var
    nil = Set.empty
