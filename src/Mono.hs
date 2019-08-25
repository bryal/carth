{-# LANGUAGE TemplateHaskell, LambdaCase, TupleSections
           , TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}

-- | Monomorphization
module Mono (monomorphize) where

import Control.Applicative (liftA2, liftA3)
import Control.Lens (makeLenses, over, views)
import Control.Monad.Reader
import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe

import Misc
import qualified AnnotAst
import AnnotAst (TVar(..), Scheme(..))
import MonoAst

data Env = Env
    { _defs :: Map String (Scheme, AnnotAst.Expr)
    , _tvBinds :: Map TVar Type
    }

makeLenses ''Env

type Insts = Map String (Map Type Expr)

-- | The monomorphization monad
type Mono = ReaderT Env (State Insts)

monomorphize :: AnnotAst.Program -> Program
monomorphize (AnnotAst.Program main ds) = (uncurry (flip Program))
    (evalState (runReaderT (monoLet ds main) initEnv) Map.empty)

initEnv :: Env
initEnv = Env {_defs = Map.empty, _tvBinds = Map.empty}

mono :: AnnotAst.Expr -> Mono Expr
mono = \case
    AnnotAst.Lit c -> pure (Lit c)
    AnnotAst.Var (AnnotAst.TypedVar x t) -> do
        t' <- monotype t
        addInst x t'
        pure (Var (TypedVar x t'))
    AnnotAst.App f a -> liftA2 App (mono f) (mono a)
    AnnotAst.If p c a -> liftA3 If (mono p) (mono c) (mono a)
    AnnotAst.Fun (p, tp) (b, bt) -> do
        tp' <- monotype tp
        b' <- mono b
        bt' <- monotype bt
        pure (Fun (TypedVar p tp') (b', bt'))
    AnnotAst.Let ds b -> fmap (uncurry Let) (monoLet ds b)
    AnnotAst.Match _ _ -> nyi "mono Match"
    AnnotAst.Constructor _ -> nyi "mono Constructor"

monoLet :: AnnotAst.Defs -> AnnotAst.Expr -> Mono (Defs, Expr)
monoLet (AnnotAst.Defs ds) body = do
    let ks = Map.keys ds
    parentInsts <- gets (lookups ks)
    let newEmptyInsts = (fmap (const Map.empty) ds)
    modify (Map.union newEmptyInsts)
    body' <- local (over defs (Map.union ds)) (mono body)
    dsInsts <- gets (lookups ks)
    modify (Map.union (Map.fromList parentInsts))
    let
        ds' = Map.fromList $ do
            (name, dInsts) <- dsInsts
            (t, body) <- Map.toList dInsts
            pure (TypedVar name t, body)
    pure (Defs ds', body')

addInst :: String -> Type -> Mono ()
addInst x t1 = do
    insts <- get
    case Map.lookup x insts of
        Nothing -> pure () -- If x is not in insts, it's a function parameter. Ignore.
        Just xInsts -> unless (Map.member t1 xInsts) $ do
            (Forall _ t2, body) <- views
                defs
                (lookup' (ice (x ++ " not in defs")) x)
            body' <- local (over tvBinds (Map.union (bindTvs t2 t1))) (mono body)
            insertInst x t1 body'

bindTvs :: AnnotAst.Type -> Type -> Map TVar Type
bindTvs = curry $ \case
    (AnnotAst.TVar v, t) -> Map.singleton v t
    (AnnotAst.TFun p0 r0, TFun p1 r1) ->
        Map.union (bindTvs p0 p1) (bindTvs r0 r1)
    (AnnotAst.TPrim a, TPrim b) | a == b -> Map.empty
    (a, b) -> ice $ "bindTvs: " ++ show a ++ ", " ++ show b

monotype :: AnnotAst.Type -> Mono Type
monotype = \case
    AnnotAst.TVar v ->
        views tvBinds (lookup' (ice (show v ++ " not in tvBinds")) v)
    AnnotAst.TPrim c -> pure (TPrim c)
    AnnotAst.TFun a b -> liftA2 TFun (monotype a) (monotype b)
    AnnotAst.TConst c ts -> fmap (TConst c) (mapM monotype ts)

insertInst :: String -> Type -> Expr -> Mono ()
insertInst x t b = modify (Map.adjust (Map.insert t b) x)

lookup' :: Ord k => v -> k -> Map k v -> v
lookup' = Map.findWithDefault

lookups :: Ord k => [k] -> Map k v -> [(k, v)]
lookups ks m = catMaybes (map (\k -> fmap (k, ) (Map.lookup k m)) ks)
