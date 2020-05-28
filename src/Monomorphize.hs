{-# LANGUAGE TemplateHaskell, LambdaCase, TupleSections
           , TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses
           , FlexibleContexts #-}

-- | Monomorphization
module Monomorphize (monomorphize, builtinExterns) where

import Control.Applicative (liftA2, liftA3)
import Lens.Micro.Platform (makeLenses, view, use, modifying, to)
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor
import Data.Bifunctor
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Bitraversable

import Misc
import SrcPos
import qualified Checked
import Checked (noPos, TVar(..), Scheme(..))
import Monomorphic

data Env = Env
    { _envDefs :: Map String (Scheme, Checked.Expr)
    , _tvBinds :: Map TVar Type
    }
makeLenses ''Env

data Insts = Insts
    { _defInsts :: Map String (Map Type ([Type], Expr'))
    , _tdefInsts :: Set TConst
    }
makeLenses ''Insts

-- | The monomorphization monad
type Mono = StateT Insts (Reader Env)

monomorphize :: Checked.Program -> Program
monomorphize (Checked.Program (Topo defs) tdefs externs) = evalMono $ do
    externs' <- mapM
        (\(x, (t, p)) -> fmap (\t' -> (x, t', p)) (monotype t))
        (Map.toList externs)
    let callMain =
            noPos (Checked.Var (Checked.TypedVar "main" Checked.mainType))
    defs' <- foldr
        (\d1 md2s -> fmap (uncurry (++)) (monoLet' d1 md2s))
        (mono callMain $> [])
        defs
    tdefs' <- instTypeDefs tdefs
    pure (Program (Topo defs') tdefs' externs')

builtinExterns :: Map String Type
builtinExterns = evalMono (mapM monotype Checked.builtinExterns)

evalMono :: Mono a -> a
evalMono ma = runReader (evalStateT ma initInsts) initEnv

-- We must manually add instantiations for types that occur in generated code
-- and is not "detected" by the monomorphization pass, or the types won't be
-- defined.
initInsts :: Insts
initInsts = Insts Map.empty (Set.fromList [("Str", []), tUnit, ("Bool", [])])

initEnv :: Env
initEnv = Env { _envDefs = Map.empty, _tvBinds = Map.empty }

mono :: Checked.Expr -> Mono Expr
mono (Checked.Expr pos ex) = fmap (Expr pos) $ case ex of
    Checked.Lit c -> pure (Lit c)
    Checked.Var (Checked.TypedVar x t) -> do
        t' <- monotype t
        addDefInst x t'
        pure (Var (TypedVar x t'))
    Checked.App f a rt -> liftA3 App (mono f) (mono a) (monotype rt)
    Checked.If p c a -> liftA3 If (mono p) (mono c) (mono a)
    Checked.Fun (p, b) -> monoFun p b
    Checked.Let d e -> monoLet pos d e
    Checked.Match e cs tbody -> monoMatch e cs tbody
    Checked.Ction v span' inst as -> monoCtion v span' inst as
    Checked.Sizeof t -> fmap Sizeof (monotype t)
    Checked.Deref x -> fmap Deref (mono x)
    Checked.Store x p -> liftA2 Store (mono x) (mono p)
    Checked.Absurd t -> fmap Absurd (monotype t)
    Checked.Transmute xpos x t u ->
        liftA3 (Transmute xpos) (mono x) (monotype t) (monotype u)

monoFun :: (String, Checked.Type) -> (Checked.Expr, Checked.Type) -> Mono Expr'
monoFun (p, tp) (b, bt) = do
    parentInst <- use (defInsts . to (Map.lookup p))
    modifying defInsts (Map.delete p)
    tp' <- monotype tp
    b' <- mono b
    bt' <- monotype bt
    maybe (pure ()) (modifying defInsts . Map.insert p) parentInst
    pure (Fun (TypedVar p tp', (b', bt')))

monoLet :: Maybe SrcPos -> Checked.Def -> Checked.Expr -> Mono Expr'
monoLet pos d e = do
    (ds', e') <- monoLet' d (mono e)
    let Expr _ l = foldr (Expr pos .* Let) e' ds'
    pure l

monoLet' :: Checked.Def -> Mono a -> Mono ([Def], a)
monoLet' def ma = case def of
    Checked.VarDef d -> fmap (first (map VarDef)) (monoLetVar d ma)
    Checked.RecDefs ds -> fmap (first (pure . RecDefs)) (monoLetRecs ds ma)

monoLetVar :: Checked.VarDef -> Mono a -> Mono ([VarDef], a)
monoLetVar (lhs, rhs) monoBody = do
    parentInsts <- use (defInsts . to (Map.lookup lhs))
    modifying defInsts (Map.insert lhs Map.empty)
    body' <- augment1 envDefs (lhs, unpos rhs) monoBody
    dInsts <- use (defInsts . to (Map.! lhs))
    mapM_ (modifying defInsts . Map.insert lhs) parentInsts
    let ds' = Map.toList dInsts <&> \(t, (us, dbody)) ->
            (TypedVar lhs t, WithPos (getPos rhs) (us, dbody))
    pure (ds', body')

monoLetRecs :: Checked.RecDefs -> Mono a -> Mono (RecDefs, a)
monoLetRecs ds ma = foldr
    (\d1 mb -> monoLetVar (Checked.funDefToVarDef d1) mb
        <&> \(d1's, (d2s, b)) -> (map funDefFromVarDef d1's ++ d2s, b)
    )
    (fmap ([], ) ma)
    ds

monoMatch :: Checked.Expr -> Checked.DecisionTree -> Checked.Type -> Mono Expr'
monoMatch e dt tbody =
    liftA3 Match (mono e) (monoDecisionTree dt) (monotype tbody)

monoDecisionTree :: Checked.DecisionTree -> Mono DecisionTree
monoDecisionTree = \case
    Checked.DSwitch obj cs def -> monoDecisionSwitch obj cs def DSwitch
    Checked.DSwitchStr obj cs def -> monoDecisionSwitch obj cs def DSwitchStr
    Checked.DLeaf (bs, e) -> do
        let bs' = Map.toList bs
        let ks = map (\((Checked.TypedVar x _), _) -> x) bs'
        parentInsts <- use (defInsts . to (lookups ks))
        modifying defInsts (deletes ks)
        bs'' <- mapM
            (bimapM
                (\(Checked.TypedVar x t) -> fmap (TypedVar x) (monotype t))
                monoAccess
            )
            bs'
        e' <- mono e
        modifying defInsts (Map.union (Map.fromList parentInsts))
        pure (DLeaf (bs'', e'))
  where
    monoDecisionSwitch obj cs def f = do
        obj' <- monoAccess obj
        cs' <- mapM monoDecisionTree cs
        def' <- monoDecisionTree def
        pure (f obj' cs' def')

monoAccess :: Checked.Access -> Mono Access
monoAccess = \case
    Checked.Obj -> pure Obj
    Checked.As a span' ts ->
        liftA3 As (monoAccess a) (pure span') (mapM monotype ts)
    Checked.Sel i span' a -> fmap (Sel i span') (monoAccess a)
    Checked.ADeref a -> fmap ADeref (monoAccess a)

monoCtion :: VariantIx -> Span -> Checked.TConst -> [Checked.Expr] -> Mono Expr'
monoCtion i span' (tdefName, tdefArgs) as = do
    tdefArgs' <- mapM monotype tdefArgs
    let tdefInst = (tdefName, tdefArgs')
    as' <- mapM mono as
    pure (Ction (i, span', tdefInst, as'))

addDefInst :: String -> Type -> Mono ()
addDefInst x t1 = do
    use defInsts <&> Map.lookup x >>= \case
        -- If x is not in insts, it's a function parameter. Ignore.
        Nothing -> pure ()
        Just xInsts -> when (not (Map.member t1 xInsts)) $ do
            (Forall _ t2, body) <- view
                (envDefs . to (lookup' (ice (x ++ " not in defs")) x))
            _ <- mfix $ \body' -> do
                -- The instantiation must be in the environment when
                -- monomorphizing the body, or we may infinitely recurse.
                let boundTvs = bindTvs t2 t1
                    instTs = Map.elems boundTvs
                insertInst t1 (instTs, body')
                augment tvBinds boundTvs (fmap expr' (mono body))
            pure ()
    where insertInst t b = modifying defInsts (Map.adjust (Map.insert t b) x)

bindTvs :: Checked.Type -> Type -> Map TVar Type
bindTvs a b = case (a, b) of
    (Checked.TVar v, t) -> Map.singleton v t
    (Checked.TFun p0 r0, TFun p1 r1) ->
        Map.union (bindTvs p0 p1) (bindTvs r0 r1)
    (Checked.TBox t0, TBox t1) -> bindTvs t0 t1
    (Checked.TPrim _, TPrim _) -> Map.empty
    (Checked.TConst (_, ts0), TConst (_, ts1)) ->
        Map.unions (zipWith bindTvs ts0 ts1)
    (Checked.TPrim _, _) -> err
    (Checked.TFun _ _, _) -> err
    (Checked.TBox _, _) -> err
    (Checked.TConst _, _) -> err
    where err = ice $ "bindTvs: " ++ show a ++ ", " ++ show b

monotype :: Checked.Type -> Mono Type
monotype = \case
    Checked.TVar v ->
        view (tvBinds . to (lookup' (ice (show v ++ " not in tvBinds")) v))
    Checked.TPrim c -> pure (TPrim c)
    Checked.TFun a b -> liftA2 TFun (monotype a) (monotype b)
    Checked.TBox t -> fmap TBox (monotype t)
    Checked.TConst (c, ts) -> do
        ts' <- mapM monotype ts
        let tdefInst = (c, ts')
        modifying tdefInsts (Set.insert tdefInst)
        pure (TConst tdefInst)

instTypeDefs :: Checked.TypeDefs -> Mono TypeDefs
instTypeDefs tdefs = do
    insts <- use (tdefInsts . to Set.toList)
    instTypeDefs' tdefs insts

instTypeDefs' :: Checked.TypeDefs -> [TConst] -> Mono TypeDefs
instTypeDefs' tdefs = \case
    [] -> pure []
    inst : insts -> do
        oldTdefInsts <- use tdefInsts
        tdef' <- instTypeDef tdefs inst
        newTdefInsts <- use tdefInsts
        let newInsts = Set.difference newTdefInsts oldTdefInsts
        tdefs' <- instTypeDefs' tdefs (Set.toList newInsts ++ insts)
        pure (tdef' : tdefs')
instTypeDef :: Checked.TypeDefs -> TConst -> Mono (TConst, [VariantTypes])
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
