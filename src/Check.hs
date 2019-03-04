{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module Check (typecheck) where

import NonEmpty
import Ast
import Annot (Type, Scheme (..))
import qualified Annot
import qualified Data.Map.Strict as Map
-- import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Graph (stronglyConnComp, flattenSCC, SCC (..))
-- import Data.List
import Data.Maybe
import Control.Monad.Except
import Control.Monad.RWS.Strict

type TypeErr = String

data Env = Env

data St = St

data Constraint

type Infer a = RWST Env [Constraint] St (Except TypeErr) a

typecheck :: Program -> Either TypeErr Annot.Program
typecheck = runInfer . inferProgram

runInfer :: Infer Annot.Program -> Either TypeErr Annot.Program
runInfer i = do
  (pgm, _, cs) <- runExcept (runRWST i Env St)
  solveConstraints cs
  pure pgm

inferProgram :: Program -> Infer Annot.Program
inferProgram (Program main defs) = do
  let allDefs = ("main", main) : defs
  allDefs' <- inferDefs allDefs
  let main' = fromMaybe (error "ICE: main not in map of inferred defs")
                        (Map.lookup "main" allDefs')
  let defs' = Map.delete "main" allDefs'
  pure (Annot.Program main' defs')

inferDefs :: [Def] -> Infer Annot.Defs
inferDefs defs = do
  let ordered = orderDefs defs
  inferDefsComponents ordered

inferDefsComponents :: [SCC Def] -> Infer Annot.Defs
inferDefsComponents = \case
  [] -> pure Map.empty
  (scc:sccs) -> do
    let defs = flattenSCC scc
    let names = map fst defs
    ts <- replicateM (length defs) fresh
    let defsTs = zip names (map (Scheme []) ts)
    withLocals defsTs $
      forM (zip defs ts) $ \((_, body), t) -> do
        t' <- inferExpr body
        unify t t'
    env <- ask
    let defsScms = zip names (map (generalize env) ts)
    withLocals defsScms (inferDefsComponents sccs)

inferExpr :: Expr -> Infer Type
inferExpr = undefined

unify :: Type -> Type -> Infer ()
unify = undefined

generalize :: Env -> Type -> Scheme
generalize = undefined

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
fresh = undefined

solveConstraints :: [Constraint] -> Either TypeErr ()
solveConstraints = undefined

withLocals :: [(Id, Scheme)] -> Infer a -> Infer a
withLocals = undefined
