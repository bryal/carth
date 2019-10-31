{-# LANGUAGE TemplateHaskell, LambdaCase, TupleSections
           , TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}

-- | Monomorphization
module Mono (monomorphize) where

import Control.Applicative (liftA2, liftA3)
import Control.Lens (makeLenses, views, use, uses, modifying)
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Bitraversable

import Misc
import qualified AnnotAst as An
import AnnotAst (TVar(..), Scheme(..))
import MonoAst

data Env = Env
    { _defs :: Map String (Scheme, An.Expr)
    , _tvBinds :: Map TVar Type
    }
makeLenses ''Env

data Insts = Insts
    { _defInsts :: Map String (Map Type Expr)
    , _tdefInsts :: Set TConst
    }
makeLenses ''Insts

-- | The monomorphization monad
type Mono = StateT Insts (Reader Env)

monomorphize :: An.Program -> Program
monomorphize (An.Program main defs tdefs externs) =
    let
        initInsts = Insts Map.empty Set.empty
        run m = runReader (runStateT m initInsts) initEnv
        ((externs', (defs', main')), Insts _ tdefInsts') = run $ liftA2
            (,)
            (mapM (bimapM pure monotype) (Map.toList externs))
            (monoLet defs main)
        tdefs' = instTypeDefs tdefs tdefInsts'
    in Program main' defs' tdefs' externs'

initEnv :: Env
initEnv = Env { _defs = Map.empty, _tvBinds = Map.empty }

mono :: An.Expr -> Mono Expr
mono = \case
    An.Lit c -> pure (Lit c)
    An.Var (An.TypedVar x t) -> do
        t' <- monotype t
        addDefInst x t'
        pure (Var (TypedVar x t'))
    An.App f a -> liftA2 App (mono f) (mono a)
    An.If p c a -> liftA3 If (mono p) (mono c) (mono a)
    An.Fun p b -> monoFun p b
    An.Let ds b -> fmap (uncurry Let) (monoLet ds b)
    An.Match e cs tbody -> monoMatch e cs tbody
    An.Ction c -> monoCtion c

monoFun :: (String, An.Type) -> (An.Expr, An.Type) -> Mono Expr
monoFun (p, tp) (b, bt) = do
    parentInst <- uses defInsts (Map.lookup p)
    modifying defInsts (Map.delete p)
    tp' <- monotype tp
    b' <- mono b
    bt' <- monotype bt
    maybe (pure ()) (modifying defInsts . Map.insert p) parentInst
    pure (Fun (TypedVar p tp') (b', bt'))

monoLet :: An.Defs -> An.Expr -> Mono (Defs, Expr)
monoLet (An.Defs ds) body = do
    let ks = Map.keys ds
    parentInsts <- uses defInsts (lookups ks)
    let newEmptyInsts = (fmap (const Map.empty) ds)
    modifying defInsts (Map.union newEmptyInsts)
    body' <- augment defs ds (mono body)
    dsInsts <- uses defInsts (lookups ks)
    modifying defInsts (Map.union (Map.fromList parentInsts))
    let ds' = Map.fromList $ do
            (name, dInsts) <- dsInsts
            (t, body) <- Map.toList dInsts
            pure (TypedVar name t, body)
    pure (Defs ds', body')

monoMatch :: An.Expr -> An.DecisionTree -> An.Type -> Mono Expr
monoMatch e dt tbody =
    liftA3 Match (mono e) (monoDecisionTree dt) (monotype tbody)

monoDecisionTree :: An.DecisionTree -> Mono DecisionTree
monoDecisionTree = \case
    An.DSwitch obj cs def -> do
        obj' <- monoAccess obj
        cs' <- mapM monoDecisionTree cs
        def' <- monoDecisionTree def
        pure (DSwitch obj' cs' def')
    An.DLeaf (bs, e) -> do
        let bs' = Map.toList bs
        let ks = map (\((An.TypedVar x _), _) -> x) bs'
        parentInsts <- uses defInsts (lookups ks)
        modifying defInsts (deletes ks)
        bs'' <- mapM
            (bimapM
                (\(An.TypedVar x t) -> fmap (TypedVar x) (monotype t))
                monoAccess
            )
            bs'
        e' <- mono e
        modifying defInsts (Map.union (Map.fromList parentInsts))
        pure (DLeaf (bs'', e'))

monoAccess :: An.Access -> Mono Access
monoAccess = \case
    An.Obj -> pure Obj
    An.As a ts -> liftA2 As (monoAccess a) (mapM monotype ts)
    An.Sel i a -> fmap (Sel i) (monoAccess a)

monoCtion :: An.Ction -> Mono Expr
monoCtion (i, (tdefName, tdefArgs), as) = do
    tdefArgs' <- mapM monotype tdefArgs
    let tdefInst = (tdefName, tdefArgs')
    modifying tdefInsts (Set.insert tdefInst)
    as' <- mapM mono as
    pure (Ction (i, tdefInst, as'))

addDefInst :: String -> Type -> Mono ()
addDefInst x t1 = do
    use defInsts <&> Map.lookup x >>= \case
        -- If x is not in insts, it's a function parameter. Ignore.
        Nothing -> pure ()
        Just xInsts -> unless (Map.member t1 xInsts) $ do
            (Forall _ t2, body) <- views
                defs
                (lookup' (ice (x ++ " not in defs")) x)
            body' <- augment tvBinds (bindTvs t2 t1) (mono body)
            insertInst x t1 body'

bindTvs :: An.Type -> Type -> Map TVar Type
bindTvs a b = case (a, b) of
    (An.TVar v, t) -> Map.singleton v t
    (An.TFun p0 r0, TFun p1 r1) -> Map.union (bindTvs p0 p1) (bindTvs r0 r1)
    (An.TPtr t0, TPtr t1) -> bindTvs t0 t1
    (An.TPrim _, TPrim _) -> Map.empty
    (An.TConst (_, ts0), TConst (_, ts1)) ->
        Map.unions (zipWith bindTvs ts0 ts1)
    (An.TPrim _, _) -> err
    (An.TFun _ _, _) -> err
    (An.TPtr _, _) -> err
    (An.TConst _, _) -> err
    where err = ice $ "bindTvs: " ++ show a ++ ", " ++ show b

monotype :: An.Type -> Mono Type
monotype = \case
    An.TVar v -> views tvBinds (lookup' (ice (show v ++ " not in tvBinds")) v)
    An.TPrim c -> pure (TPrim c)
    An.TFun a b -> liftA2 TFun (monotype a) (monotype b)
    An.TPtr t -> fmap TPtr (monotype t)
    An.TConst (c, ts) -> do
        ts' <- mapM monotype ts
        let tdefInst = (c, ts')
        modifying tdefInsts (Set.insert tdefInst)
        pure (TConst tdefInst)

insertInst :: String -> Type -> Expr -> Mono ()
insertInst x t b = modifying defInsts (Map.adjust (Map.insert t b) x)

-- insts :: Set TConst
instTypeDefs :: An.TypeDefs -> Mono TypeDefs
instTypeDefs tdefs = do
    insts <- uses tdefInsts Set.toList
    instTypeDefs' tdefs insts

instTypeDefs' :: An.TypeDefs -> [TConst] -> Mono TypeDefs
instTypeDefs' tdefs = \case
    [] -> pure []
    inst : insts -> do
        oldTdefInsts <- use tdefInsts
        tdef' <- instTypeDef tdefs inst
        newTdefInsts <- use tdefInsts
        let newInsts = Set.difference newTdefInsts oldTdefInsts
        tdefs' <- instTypeDefs' tdefs (Set.toList newInsts ++ insts)
        pure (tdef' : tdefs')
instTypeDef :: An.TypeDefs -> TConst -> Mono (TConst, [VariantTypes])
instTypeDef tdefs (x, ts) = do
    let (tvs, vs) = lookup' (ice "lookup' failed in instTypeDef") x tdefs
    vs' <- augment tvBinds (Map.fromList (zip tvs ts)) (mapM (mapM monotype) vs)
    pure ((x, ts), vs')

lookup' :: Ord k => v -> k -> Map k v -> v
lookup' = Map.findWithDefault

lookups :: Ord k => [k] -> Map k v -> [(k, v)]
lookups ks m = catMaybes (map (\k -> fmap (k, ) (Map.lookup k m)) ks)

deletes :: (Foldable t, Ord k) => t k -> Map k v -> Map k v
deletes = flip (foldr Map.delete)
