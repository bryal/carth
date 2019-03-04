{-# LANGUAGE LambdaCase, OverloadedStrings, TemplateHaskell #-}

module Check (typecheck) where

import NonEmpty
import Ast
import Annot ( Type (..), Scheme (..)
             , typeUnit, typeInt, typeDouble, typeStr, typeBool, typeChar )
-- import qualified Annot
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Graph (stronglyConnComp, flattenSCC, SCC (..))
-- import Data.List
import Data.Maybe
import Control.Monad.Except
import Control.Monad.RWS.Strict
import Control.Lens

type TypeErr = String

type Env = Map Id Scheme

data St = St { _tvCount :: Int }
makeLenses ''St

type Constraint = (Type, Type)

type Infer a = RWST Env [Constraint] St (Except TypeErr) a

typecheck :: Program -> Either TypeErr ()
typecheck = runInfer . inferProgram

runInfer :: Infer () -> Either TypeErr ()
runInfer i = do
  (pgm, _, cs) <- runExcept (runRWST i Map.empty initSt)
  solveConstraints cs
  pure pgm

initSt :: St
initSt = St { _tvCount = 0 }

inferProgram :: Program -> Infer ()
inferProgram (Program main defs) = do
  let allDefs = ("main", main) : defs
  scms <- inferDefs allDefs
  let _mainScm = head scms
  pure ()

inferDefs :: [Def] -> Infer [Scheme]
inferDefs defs = do
  let ordered = orderDefs defs
  inferDefsComponents ordered

inferDefsComponents :: [SCC Def] -> Infer [Scheme]
inferDefsComponents = \case
  [] -> pure []
  (scc:sccs) -> do
    let defs = flattenSCC scc
    let names = map fst defs
    ts <- replicateM (length defs) fresh
    let defsTs = zip names (map (Forall Set.empty) ts)
    withLocals defsTs $
      forM (zip defs ts) $ \((_, body), t) -> do
        t' <- infer body
        unify t t'
    env <- ask
    let scms = map (generalize env) ts
    let defsScms = zip names scms
    scmsRest <- withLocals defsScms (inferDefsComponents sccs)
    pure (scms ++ scmsRest)

infer :: Expr -> Infer Type
infer = \case
  Unit -> pure typeUnit
  Int _ -> pure typeInt
  Double _ -> pure typeDouble
  Char _ -> pure typeChar
  Str _ -> pure typeStr
  Bool _ -> pure typeBool
  Var x -> asks (Map.lookup x) >>= \case
    Just scm -> instantiate scm
    Nothing -> throwError ("unbound variable " ++ show x)
  App f a -> do
    tf <- infer f
    ta <- infer a
    tr <- fresh
    unify tf (TFun ta tr)
    pure tr
  If p c a -> do
    tp <- infer p
    tc <- infer c
    ta <- infer a
    unify typeBool tp
    unify tc ta
    pure tc
  Fun p b -> do
    tp <- fresh
    tb <- withLocal (p, Forall Set.empty tp) (infer b)
    pure (TFun tp tb)
  Let defs b -> do
    let defs' = nonEmptyToList defs
    scms <- inferDefs defs'
    let defsScms = zip (map fst defs') scms
    tb <- withLocals defsScms (infer b)
    pure tb
  Match _a _cs -> undefined
  FunMatch _cs -> undefined
  Constructor _c -> undefined

unify :: Type -> Type -> Infer ()
unify t1 t2 = tell [(t1, t2)]

instantiate :: Scheme -> Infer Type
instantiate (Forall params t) = do
  let params' = Set.toList params
  args <- mapM (const fresh) params'
  pure (subst (Map.fromList (zip params' args)) t)

generalize :: Env -> Type -> Scheme
generalize env t = Forall (ftv env t) t

subst :: Map String Type -> Type -> Type
subst s t = case t of
  TVar tv -> fromMaybe t (Map.lookup tv s)
  TConst _ -> t
  TFun a b -> TFun (subst s a) (subst s b)

ftv :: Env -> Type -> Set String
ftv env t = Set.difference (ftvType t) ftvEnv
  where
    ftvType = \case
      TVar tv -> Set.singleton tv
      TConst _ -> Set.empty
      TFun a b -> Set.union (ftvType a) (ftvType b)
    ftvEnv = Set.unions (map (ftvScheme . snd) (Map.toList env))
    ftvScheme (Forall tvs t') = Set.difference (ftvType t') tvs

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

-- Free vars of a definition
fvDef :: Def -> [Id]
fvDef (name, body) = Set.toList (Set.delete name (fvExp body))

-- Free vars of an expression
fvExp :: Expr -> Set Id
fvExp = \case
  Unit -> nil; Int _ -> nil; Double _ -> nil; Str _ -> nil; Bool _ -> nil; Constructor _ -> nil; Char _ -> nil
  Var x -> Set.singleton x
  App f a -> Set.unions (map fvExp [f, a])
  If p c a -> Set.unions (map fvExp [p, c, a])
  Fun p b -> Set.delete p (fvExp b)
  Let bs e ->
    let fvE = fvExp e
        fvBs = foldl (\acc b -> Set.union acc (fvExp b)) Set.empty (fmap snd bs)
        bvBs = Set.fromList (map fst (nonEmptyToList bs))
      in Set.difference (Set.union fvE fvBs) bvBs
  Match e cs -> Set.union (fvExp e) (Set.difference (fvClauses cs) (bvClauses cs))
  FunMatch cs -> Set.difference (fvClauses cs) (bvClauses cs)
  where fvClauses = foldl (\acc c -> Set.union acc (fvExp (snd c))) Set.empty
        bvClauses = Set.unions . map (patVars . fst) . nonEmptyToList
        patVars = \case
          PConstructor _ -> nil
          PConstruction _ ps -> Set.unions (map patVars (nonEmptyToList ps))
          PVar var -> Set.singleton var
        nil = Set.empty

fresh :: Infer Type
fresh = fmap (TVar . ("#"++) . show) (tvCount <<+= 1)

solveConstraints :: [Constraint] -> Either TypeErr ()
solveConstraints cs = error (show cs)

withLocals :: [(Id, Scheme)] -> Infer a -> Infer a
withLocals bs = local (Map.union (Map.fromList bs))

withLocal :: (Id, Scheme) -> Infer a -> Infer a
withLocal b = local (uncurry Map.insert b)
