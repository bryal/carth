{-# LANGUAGE LambdaCase, OverloadedStrings, TemplateHaskell, TupleSections #-}

module Check (typecheck) where

import NonEmpty
import Ast
import Pretty
import Annot ( TVar, Type (..), Scheme (..)
             , typeUnit, typeInt, typeDouble, typeStr, typeBool, typeChar )
import qualified Annot
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Graph (stronglyConnComp, flattenSCC, SCC (..))
-- import Data.List
import Data.Maybe
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Lens

type TypeErr = String

type Env = Map Id Scheme

data St = St { _tvCount :: Int }
makeLenses ''St

-- TODO: Try handling substitution maps in the state or a monad of its own
-- | Type checker monad
type Infer a = ReaderT Env (StateT St (Except TypeErr)) a

-- | Map of substitutions from type-variables to more specific types
type Subst = Map TVar Type

typecheck :: Program -> Either TypeErr Annot.Program
typecheck = runInfer . inferProgram

runInfer :: Infer Annot.Program -> Either TypeErr Annot.Program
runInfer i = runExcept (evalStateT (runReaderT i Map.empty) initSt)

initSt :: St
initSt = St { _tvCount = 0 }

fresh :: Infer Type
fresh = fmap (TVar . ("#"++) . show) (tvCount <<+= 1)

withLocals :: [(Id, Scheme)] -> Infer a -> Infer a
withLocals bs = local (Map.union (Map.fromList bs))

withLocal :: (Id, Scheme) -> Infer a -> Infer a
withLocal b = local (uncurry Map.insert b)

-- Inference
--------------------------------------------------------------------------------

inferProgram :: Program -> Infer Annot.Program
inferProgram (Program main defs) = do
  let allDefs = ("main", main) : defs
  (_, scms) <- inferDefs allDefs
  let s = unlines (map (\((Id id), scm) -> id ++ " : " ++ pretty scm) scms)
  error ("Inferred top-level type schemes:\n" ++ s)

inferDefs :: [Def] -> Infer (Subst, [(Id, Scheme)])
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
  where graph = map (\def@(name, _) -> (def, name, fvDef def)) defs

inferDefsComponents :: [SCC Def] -> Infer (Subst, [(Id, Scheme)])
inferDefsComponents = \case
  [] -> pure (nullSubst, [])
  (scc:sccs) -> do
    let defs = flattenSCC scc
    let names = map fst defs
    ts <- replicateM (length defs) fresh
    let defsTs = zip names (map (Forall Set.empty) ts)
    let bodies = map snd defs
    s <- withLocals defsTs $
      flip3 foldM (zip bodies ts) nullSubst $ \s1 (body, t) -> do
        (s2, t') <- local (substEnv s1) (infer body)
        let s2' = composeSubsts s2 s1
        s3 <- unify (subst s2' t) t'
        pure (composeSubsts s3 s2')
    local (substEnv s) $ do
      env' <- ask
      let scms = map (generalize env') (map (subst s) ts)
      let defsScms = zip names scms
      (s', scmsRest) <- withLocals defsScms (inferDefsComponents sccs)
      pure (composeSubsts s' s, (defsScms ++ scmsRest))

flip3 :: (a -> b -> c -> d) -> (c -> b -> a -> d)
flip3 f = \c b a -> f a b c

infer :: Expr -> Infer (Subst, Type)
infer = \case
  Unit   -> litT typeUnit; Int _ -> litT typeInt; Double _ -> litT typeDouble
  Char _ -> litT typeChar; Str _ -> litT typeStr; Bool _   -> litT typeBool
  Var x -> fmap (nullSubst,) (lookupEnv x)
  App f a -> do
    (s1, tf) <- infer f
    (s2, ta) <- local (substEnv s1) (infer a)
    tr <- fresh
    s3 <- unify (subst s2 tf) (TFun ta tr)
    pure (foldr1 composeSubsts [s3, s2, s1], subst s3 tr)
  If p c a -> do
    (s1, tp) <- infer p
    (s2, tc) <- local (substEnv s1) (infer c)
    let s2' = composeSubsts s2 s1
    (s3, ta) <- local (substEnv s2') (infer a)
    let s3' = composeSubsts s3 s2'
    s4 <- unify typeBool (subst s3' tp)
    let s4' = composeSubsts s4 s3'
    s5 <- unify (subst s4' tc) (subst s4 ta)
    pure (composeSubsts s5 s4', (subst s5 tc))
  Fun p b -> do
    tp <- fresh
    (s, tb) <- withLocal (p, Forall Set.empty tp) (infer b)
    pure (s, TFun (subst s tp) tb)
  Let defs b -> do
    (s1, defsScms) <- inferDefs (nonEmptyToList defs)
    (s2, tb) <- local (substEnv s1) (withLocals defsScms (infer b))
    pure (composeSubsts s2 s1, tb)
  Match _a _cs -> undefined
  FunMatch _cs -> undefined
  Constructor _c -> undefined
  where litT t = pure (nullSubst, t)

lookupEnv :: Id -> Infer Type
lookupEnv x = asks (Map.lookup x) >>= \case
  Just scm -> instantiate scm
  Nothing  -> throwError ("Unbound variable: " ++ show x)

-- Substitution
--------------------------------------------------------------------------------

subst :: Subst -> Type -> Type
subst s t = case t of
  TVar tv -> fromMaybe t (Map.lookup tv s)
  TConst _ -> t
  TFun a b -> TFun (subst s a) (subst s b)

substEnv :: Subst -> Env -> Env
substEnv s env = fmap (over Annot.scmBody (subst s)) env

composeSubsts :: Subst -> Subst -> Subst
composeSubsts s1 s2 = Map.union (fmap (subst s1) s2) s1

nullSubst :: Subst
nullSubst = Map.empty

-- Unification
--------------------------------------------------------------------------------

unify ::  Type -> Type -> Infer Subst
unify = curry $ \case
  (TConst a,   TConst b) | a == b -> pure nullSubst
  (TVar a,     TVar b) | a == b   -> pure nullSubst
  (TVar a,     t) | occursIn a t  ->
    throwError (concat ["Infinite type: ", a, ", ", show t ])
  (TVar a,     t)                 -> pure (Map.singleton a t)
  (t,          TVar a)            -> unify (TVar a) t
  (TFun t1 t2, TFun t1' t2')      -> do
    s1 <- unify t1 t1'
    s2 <- unify (subst s1 t2) (subst s1 t2')
    pure (composeSubsts s2 s1)
  (t1,         t2)                ->
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

generalize :: Env -> Type -> Scheme
generalize env t = Forall (generalize' env t) t

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

-- Free variables
--------------------------------------------------------------------------------

fvDef :: Def -> [Id]
fvDef (name, body) = Set.toList (Set.delete name (fv body))

fv :: Expr -> Set Id
fv = \case
  Unit   -> nil; Int _  -> nil; Double _ -> nil;
  Bool _ -> nil; Char _ -> nil; Str _    -> nil
  Var x -> Set.singleton x
  App f a -> Set.unions (map fv [f, a])
  If p c a -> Set.unions (map fv [p, c, a])
  Fun p b -> Set.delete p (fv b)
  Let bs e ->
    let fvE = fv e
        fvBs = foldl (\acc b -> Set.union acc (fv b)) Set.empty (fmap snd bs)
        bvBs = Set.fromList (map fst (nonEmptyToList bs))
      in Set.difference (Set.union fvE fvBs) bvBs
  Match e cs -> Set.union (fv e) (Set.difference (fvClauses cs) (bvClauses cs))
  FunMatch cs -> Set.difference (fvClauses cs) (bvClauses cs)
  Constructor _ -> nil
  where fvClauses = foldl (\acc c -> Set.union acc (fv (snd c))) Set.empty
        bvClauses = Set.unions . map (patVars . fst) . nonEmptyToList
        patVars = \case
          PConstructor _ -> nil
          PConstruction _ ps -> Set.unions (map patVars (nonEmptyToList ps))
          PVar var -> Set.singleton var
        nil = Set.empty
