{-# LANGUAGE TemplateHaskell, LambdaCase, TupleSections
           , TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses
           , FlexibleContexts #-}

-- | Monomorphization
module Monomorphize (monomorphize, builtinExterns) where

import Control.Applicative (liftA2, liftA3)
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor
import Data.Bifunctor
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Bitraversable

import Misc
import SrcPos
import qualified Checked
import Checked (noPos, TVar(..), Scheme(..))
import Monomorphic
import TypeAst hiding (TConst)

type Env = Map TVar Type

type DataInst = TConst
newtype DefInsts = DefInsts (Map String (Set Type))

type Mono' = WriterT [DataInst] (Reader Env)

-- | The monomorphization monad
type Mono = WriterT DefInsts Mono'


instance Semigroup DefInsts where
    DefInsts a <> DefInsts b = DefInsts $ Map.unionWith Set.union a b

instance Monoid DefInsts where
    mempty = DefInsts $ Map.empty


monomorphize :: Checked.Program -> Program
monomorphize (Checked.Program (Topo defs) datas externs) =
    let
        callMain = noPos (Checked.Var (Checked.TypedVar "main" Checked.mainType))
        monoExterns = mapM (\(x, (t, p)) -> fmap (\t' -> (x, t', p)) (monotype t))
                           (Map.toList externs)
        monoDefs = foldr (\d1 md2s -> fmap (uncurry (++)) (monoLet' d1 md2s))
                         (mono callMain $> [])
                         defs
        ((externs', defs'), (DefInsts _defInsts, dataInsts)) =
            evalMono (liftA2 (,) monoExterns monoDefs)
        -- TODO: defInsts should only contain externs at this point. Sanity check this
        --       when in debug mode?
        datas' = instDatas (builtinDataInsts ++ dataInsts)
    in
        Program (Topo defs') datas' externs'
  where
    instDatas :: [DataInst] -> Datas
    instDatas = instDatas' Map.empty

    instDatas' :: Datas -> [DataInst] -> Datas
    instDatas' dones = \case
        [] -> dones
        inst : rest -> if Map.member inst dones
            then instDatas' dones rest
            else
                let (variants, more) = instData inst
                in  instDatas' (Map.insert inst variants dones) (more ++ rest)

    instData :: TConst -> ([VariantTypes], [DataInst])
    instData (x, ts) =
        let (tvars, variants) =
                    Map.findWithDefault (ice "instData no such TConst in datas") x datas
            s = Map.fromList (zip tvars ts)
            (variants', moreInsts) = runWriter (mapM (mapM (monotype' s)) variants)
        in  (variants', moreInsts)

    -- We must manually add instantiations for types that occur in generated code and is
    -- not "detected" by the monomorphization pass, or the types won't be defined.
    builtinDataInsts = [tStr', tUnit', tBool']

builtinExterns :: Map String Type
builtinExterns = fst $ evalMono (mapM monotype Checked.builtinExterns)

evalMono :: Mono a -> (a, (DefInsts, [DataInst]))
evalMono ma =
    (\((a, b), c) -> (a, (b, c))) (runReader (runWriterT (runWriterT ma)) Map.empty)

mono :: Checked.Expr -> Mono Expr
mono (Checked.Expr pos ex) = fmap (Expr pos) $ case ex of
    Checked.Lit c -> pure (Lit c)
    Checked.Var (Checked.TypedVar x t) -> do
        t' <- monotype t
        tell (DefInsts (Map.singleton x (Set.singleton t')))
        pure (Var (TypedVar x t'))
    Checked.App f a rt -> liftA3 App (mono f) (mono a) (monotype rt)
    Checked.If p c a -> liftA3 If (mono p) (mono c) (mono a)
    Checked.Fun f -> fmap (Fun) (monoFun f)
    Checked.Let d e -> monoLet pos d e
    Checked.Match e cs tbody -> monoMatch e cs tbody
    Checked.Ction v span' inst as -> monoCtion v span' inst as
    Checked.Sizeof t -> fmap Sizeof (monotype t)
    Checked.Absurd t -> fmap Absurd (monotype t)

monoFun :: Checked.Fun -> Mono Fun
monoFun ((p, tp), (b, bt)) = do
    censor (mapDefInsts (Map.delete p)) $ do
        tp' <- monotype tp
        b' <- mono b
        bt' <- monotype bt
        pure (TypedVar p tp', (b', bt'))

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
monoLetVar (lhs, WithPos rhsPos (rhsScm, rhs)) monoBody = do
    (body', DefInsts defInsts) <- lift (runWriterT monoBody)
    tell (DefInsts (Map.delete lhs defInsts))
    rhss' <- case Map.lookup lhs defInsts of
        Nothing -> pure []
        Just instTs -> mapM
            (\instT -> fmap (instT, ) (genInst rhsScm (fmap expr' (mono rhs)) instT))
            (Set.toList instTs)
    pure (map (\(t, rhs') -> (TypedVar lhs t, WithPos rhsPos rhs')) rhss', body')

monoLetRecs :: Checked.RecDefs -> Mono a -> Mono (RecDefs, a)
monoLetRecs ds monoBody = do
    (body', DefInsts defInsts) <- lift (runWriterT monoBody)
    let defs = Map.fromList ds
    let monoLetRecs'
            :: Map TypedVar (WithPos ([Type], Fun))
            -> Map String (Set Type)
            -> Mono RecDefs
        monoLetRecs' defs' insts = do
            let (insts', otherInsts) =
                    Map.partitionWithKey (\k _ -> Map.member k defs) insts
            tell (DefInsts otherInsts)
            let insts'' = filter
                    (not . flip Map.member defs')
                    (Map.toList insts' >>= \(x, ts) -> map (TypedVar x) (Set.toList ts))
            if null insts''
                then pure (Map.toList defs')
                else do
                    let genInst' (TypedVar x t) =
                            let WithPos p (scm, WithPos _ f) = defs Map.! x
                            in  fmap ((TypedVar x t, ) . WithPos p)
                                     (genInst scm (monoFun f) t)
                    (newDefs, DefInsts newInsts) <- lift
                        (runWriterT (mapM genInst' insts''))
                    monoLetRecs' (Map.union (Map.fromList newDefs) defs') newInsts
    ds' <- monoLetRecs' Map.empty defInsts
    pure (ds', body')

genInst :: Scheme -> Mono a -> Type -> Mono ([Type], a)
genInst (Forall _ rhsT) monoRhs instT = do
    let boundTvs = bindTvs rhsT instT
    rhs' <- local (Map.union boundTvs) monoRhs
    pure (Map.elems boundTvs, rhs')

monoMatch :: Checked.Expr -> Checked.DecisionTree -> Checked.Type -> Mono Expr'
monoMatch e dt tbody = liftA3 Match (mono e) (monoDecisionTree dt) (monotype tbody)

monoDecisionTree :: Checked.DecisionTree -> Mono DecisionTree
monoDecisionTree = \case
    Checked.DSwitch obj cs def -> monoDecisionSwitch obj cs def DSwitch
    Checked.DSwitchStr obj cs def -> monoDecisionSwitch obj cs def DSwitchStr
    Checked.DLeaf (bs, e) -> do
        let bs' = Map.toList bs
        let ks = map (\((Checked.TypedVar x _), _) -> x) bs'
        censor (mapDefInsts (deletes ks)) $ do
            bs'' <- mapM
                (bimapM (\(Checked.TypedVar x t) -> fmap (TypedVar x) (monotype t))
                        monoAccess
                )
                bs'
            e' <- mono e
            pure (DLeaf (bs'', e'))
  where
    monoDecisionSwitch obj cs def f = do
        obj' <- monoAccess obj
        cs' <- mapM monoDecisionTree cs
        def' <- monoDecisionTree def
        pure (f obj' cs' def')

    deletes :: (Foldable t, Ord k) => t k -> Map k v -> Map k v
    deletes = flip (foldr Map.delete)

monoAccess :: Checked.Access -> Mono Access
monoAccess = \case
    Checked.Obj -> pure Obj
    Checked.As a span' ts -> liftA3 As (monoAccess a) (pure span') (mapM monotype ts)
    Checked.Sel i span' a -> fmap (Sel i span') (monoAccess a)
    Checked.ADeref a -> fmap ADeref (monoAccess a)

monoCtion :: VariantIx -> Span -> Checked.TConst -> [Checked.Expr] -> Mono Expr'
monoCtion i span' (tdefName, tdefArgs) as = do
    tdefArgs' <- mapM monotype tdefArgs
    let tdefInst = (tdefName, tdefArgs')
    as' <- mapM mono as
    pure (Ction (i, span', tdefInst, as'))


bindTvs :: Checked.Type -> Type -> Map TVar Type
bindTvs a b = case (a, b) of
    (Checked.TVar v, t) -> Map.singleton v t
    (Checked.TFun p0 r0, TFun p1 r1) -> Map.union (bindTvs p0 p1) (bindTvs r0 r1)
    (Checked.TBox t, TBox u) -> bindTvs t u
    (Checked.TPrim _, TPrim _) -> Map.empty
    (Checked.TConst (_, ts0), TConst (_, ts1)) -> Map.unions (zipWith bindTvs ts0 ts1)
    (Checked.TPrim _, _) -> err
    (Checked.TFun _ _, _) -> err
    (Checked.TBox _, _) -> err
    (Checked.TConst _, _) -> err
    where err = ice $ "bindTvs: " ++ show a ++ ", " ++ show b

monotype :: Checked.Type -> Mono Type
monotype t = ask >>= \s -> lift (monotype' s t)

monotype' :: MonadWriter [TConst] m => Map TVar Type -> Checked.Type -> m Type
monotype' s t = let t' = subst s t in tell (findTypeInsts t') $> t'

findTypeInsts :: Type -> [TConst]
findTypeInsts = \case
    TPrim _ -> []
    TFun a b -> findTypeInsts a ++ findTypeInsts b
    TBox a -> findTypeInsts a
    TConst inst@(_, ts) -> inst : (findTypeInsts =<< ts)

subst :: Map TVar Type -> Checked.Type -> Type
subst s = \case
    Checked.TVar v -> Map.findWithDefault (ice ("Monomorphize.subst: " ++ show v)) v s
    Checked.TPrim c -> TPrim c
    Checked.TFun a b -> TFun (subst s a) (subst s b)
    Checked.TBox t -> TBox (subst s t)
    Checked.TConst (c, ts) -> TConst (c, map (subst s) ts)

mapDefInsts :: (Map String (Set Type) -> Map String (Set Type)) -> DefInsts -> DefInsts
mapDefInsts f (DefInsts m) = (DefInsts (f m))
