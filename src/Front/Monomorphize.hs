-- | Monomorphization
module Front.Monomorphize (monomorphize, builtinExterns) where

import Control.Applicative (liftA2, liftA3)
import Control.Monad.Reader
import Control.Monad.Writer
import Data.Functor
import Data.Bifunctor
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Bitraversable
import Data.Void

import Misc
import qualified Front.Checked as Checked
import Front.Checked (TVar(..), Scheme(..))
import Front.Monomorphic
import Front.TypeAst

type Env = Map TVar Type

type DataInst = TConst
newtype DefInsts = DefInsts (Map String (Set Type))

type Mono' = WriterT [DataInst] (Reader Env)

-- | The monomorphization monad
type Mono = WriterT DefInsts Mono'


instance Semigroup DefInsts where
    DefInsts a <> DefInsts b = DefInsts $ Map.unionWith Set.union a b

instance Monoid DefInsts where
    mempty = DefInsts Map.empty


monomorphize :: Checked.Program -> Program
monomorphize (Checked.Program (Topo defs) datas externs) =
    let
        callMain = Checked.Var (NonVirt, Checked.TypedVar "main" Checked.mainType)
        monoExterns = mapM (\(x, t) -> fmap (x, ) (monotype t)) (Map.toList externs)
        monoDefs = foldr (\d1 md2s -> fmap (uncurry (++)) (monoLet' d1 md2s))
                         (mono callMain $> [])
                         defs
        ((externs', defs'), (DefInsts _defInsts, dataInsts)) =
            evalMono (liftA2 (,) monoExterns monoDefs)
        -- TODO: defInsts should only contain externs at this point. Sanity check this when in
        --       debug mode?
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

    instData :: TConst -> ([(String, VariantTypes)], [DataInst])
    instData (x, ts) =
        let (tvars, variants) =
                Map.findWithDefault (ice "instData no such TConst in datas") x datas
            s = Map.fromList (zip tvars ts)
            (variants', moreInsts) = runWriter (mapM (secondM (mapM (monotype' s))) variants)
        in  (variants', moreInsts)

    -- We must manually add instantiations for types that occur in generated code and is not
    -- "detected" by the monomorphization pass, or the types won't be defined.
    builtinDataInsts = [tStr', tUnit', tBool']

builtinExterns :: Map String Type
builtinExterns = fst $ evalMono (mapM monotype Checked.builtinExterns)

evalMono :: Mono a -> (a, (DefInsts, [DataInst]))
evalMono ma = (\((a, b), c) -> (a, (b, c))) (runReader (runWriterT (runWriterT ma)) Map.empty)

mono :: Checked.Expr -> Mono Expr
mono = \case
    Checked.Lit c -> pure (Lit c)
    Checked.Var (virt, Checked.TypedVar x t) -> do
        t' <- monotype t
        case virt of
            Virt -> pure ()
            NonVirt -> tell (DefInsts (Map.singleton x (Set.singleton t')))
        pure (Var virt (TypedVar x t'))
    Checked.App f as -> liftA2 App (mono f) (mapM mono as)
    Checked.If p c a -> liftA3 If (mono p) (mono c) (mono a)
    Checked.Fun f -> fmap Fun (monoFun f)
    Checked.Let d e -> monoLet d e
    Checked.Match es cs -> monoMatch es cs
    Checked.Ction v span' inst as -> monoCtion v span' inst as
    Checked.Sizeof t -> fmap Sizeof (monotype t)
    Checked.Absurd t -> fmap Absurd (monotype t)

monoFun :: Checked.Fun -> Mono Fun
monoFun (params, (b, bt)) =
    let (ps, tps) = unzip params
    in  censor (mapDefInsts (flip Map.withoutKeys (Set.fromList ps))) $ do
            tps' <- mapM monotype tps
            b' <- mono b
            bt' <- monotype bt
            pure (zipWith TypedVar ps tps', (b', bt'))

monoLet :: Checked.Def -> Checked.Expr -> Mono Expr
monoLet d e = do
    (ds', e') <- monoLet' d (mono e)
    pure (foldr Let e' ds')

monoLet' :: Checked.Def -> Mono a -> Mono ([Def], a)
monoLet' def ma = case def of
    Checked.VarDef d -> fmap (first (map VarDef)) (monoLetVar d ma)
    Checked.RecDefs ds -> fmap (first (pure . RecDefs)) (monoLetRecs ds ma)

monoLetVar :: Checked.VarDef -> Mono a -> Mono ([VarDef], a)
monoLetVar (lhs, (rhsScm, rhs)) monoBody = do
    (body', DefInsts defInsts) <- lift (runWriterT monoBody)
    tell (DefInsts (Map.delete lhs defInsts))
    rhss' <- case Map.lookup lhs defInsts of
        Nothing -> pure []
        Just instTs ->
            mapM (\instT -> fmap (instT, ) (genInst rhsScm (mono rhs) instT)) (Set.toList instTs)
    pure (map (first (TypedVar lhs)) rhss', body')

monoLetRecs :: Checked.RecDefs -> Mono a -> Mono (RecDefs, a)
monoLetRecs ds monoBody = do
    (body', DefInsts defInsts) <- lift (runWriterT monoBody)
    let defs = Map.fromList ds
    let monoLetRecs' :: Map TypedVar ([Type], Fun) -> Map String (Set Type) -> Mono RecDefs
        monoLetRecs' defs' insts = do
            let (insts', otherInsts) = Map.partitionWithKey (\k _ -> Map.member k defs) insts
            tell (DefInsts otherInsts)
            let insts'' = filter
                    (not . flip Map.member defs')
                    (Map.toList insts' >>= \(x, ts) -> map (TypedVar x) (Set.toList ts))
            if null insts''
                then pure (Map.toList defs')
                else do
                    let genInst' (TypedVar x t) =
                            let (scm, f) = Map.findWithDefault
                                    (ice
                                    $ "monoLetRecs.genInst': generating/instantiating "
                                    ++ (x ++ " as " ++ show t)
                                    ++ ", but that name is not in defs"
                                    )
                                    x
                                    defs
                            in  fmap (TypedVar x t, ) (genInst scm (monoFun f) t)
                    (newDefs, DefInsts newInsts) <- lift (runWriterT (mapM genInst' insts''))
                    monoLetRecs' (Map.union (Map.fromList newDefs) defs') newInsts
    ds' <- monoLetRecs' Map.empty defInsts
    pure (ds', body')

genInst :: Scheme -> Mono a -> Type -> Mono ([Type], a)
genInst (Forall _ _ rhsT) monoRhs instT = do
    let boundTvs = bindTvs rhsT instT
    rhs' <- local (Map.union boundTvs) monoRhs
    pure (Map.elems boundTvs, rhs')

monoMatch :: [Checked.Expr] -> Checked.DecisionTree -> Mono Expr
monoMatch es dt = liftA2 Match (mapM mono es) (monoDecisionTree dt)

monoDecisionTree :: Checked.DecisionTree -> Mono DecisionTree
monoDecisionTree = \case
    Checked.DSwitch span obj cs def -> monoDecisionSwitch obj cs def (DSwitch span)
    Checked.DSwitchStr obj cs def -> monoDecisionSwitch obj cs def DSwitchStr
    Checked.DLeaf (bs, e) -> do
        let bs' = Map.toList bs
        let ks = map (\(Checked.TypedVar x _, _) -> x) bs'
        censor (mapDefInsts (deletes ks)) $ do
            bs'' <- mapM
                (bimapM (\(Checked.TypedVar x t) -> fmap (TypedVar x) (monotype t)) pure)
                bs'
            e' <- mono e
            pure (DLeaf (bs'', e'))
  where
    monoDecisionSwitch obj cs def f = do
        cs' <- mapM monoDecisionTree cs
        def' <- monoDecisionTree def
        pure (f obj cs' def')

    deletes :: (Foldable t, Ord k) => t k -> Map k v -> Map k v
    deletes = flip (foldr Map.delete)

monoCtion :: VariantIx -> Span -> Checked.TConst -> [Checked.Expr] -> Mono Expr
monoCtion i span' (tdefName, tdefArgs) as = do
    tdefArgs' <- mapM monotype tdefArgs
    let tdefInst = (tdefName, tdefArgs')
    as' <- mapM mono as
    pure (Ction (i, span', tdefInst, as'))

bindTvs :: Checked.Type -> Type -> Map TVar Type
bindTvs a b = case (a, b) of
    (TVar v, t) -> Map.singleton v t
    (TFun ps0 r0, TFun ps1 r1) -> Map.unions $ bindTvs r0 r1 : zipWith bindTvs ps0 ps1
    (TBox t, TBox u) -> bindTvs t u
    (TPrim _, TPrim _) -> Map.empty
    (TConst (_, ts0), TConst (_, ts1)) -> Map.unions (zipWith bindTvs ts0 ts1)
    (TPrim _, _) -> err
    (TFun _ _, _) -> err
    (TBox _, _) -> err
    (TConst _, _) -> err
    where err = ice $ "bindTvs: " ++ show a ++ ", " ++ show b

monotype :: Checked.Type -> Mono Type
monotype t = ask >>= \s -> lift (monotype' s t)

monotype' :: MonadWriter [TConst] m => Map TVar Type -> Checked.Type -> m Type
monotype' s t = let t' = subst s t in tell (findTypeInsts t') $> t'

findTypeInsts :: Type -> [TConst]
findTypeInsts = \case
    TVar tv -> absurd tv
    TPrim _ -> []
    TFun as b -> concatMap findTypeInsts as ++ findTypeInsts b
    TBox a -> findTypeInsts a
    TConst inst@(_, ts) -> inst : (findTypeInsts =<< ts)

subst :: Map TVar Type -> Checked.Type -> Type
subst s = \case
    Checked.TVar v -> Map.findWithDefault (ice ("Monomorphize.subst: " ++ show v)) v s
    Checked.TPrim c -> TPrim c
    Checked.TFun as b -> TFun (map (subst s) as) (subst s b)
    Checked.TBox t -> TBox (subst s t)
    Checked.TConst (c, ts) -> TConst (c, map (subst s) ts)

mapDefInsts :: (Map String (Set Type) -> Map String (Set Type)) -> DefInsts -> DefInsts
mapDefInsts f (DefInsts m) = DefInsts (f m)
