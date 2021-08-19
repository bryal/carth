module Back.Lower (lower, builtinExterns) where

import Control.Applicative
import Control.Monad.State
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Vector as Vec

import Misc
import qualified Front.Monomorphic as Ast
import qualified Front.Monomorphize as Monomorphize
import Back.Low

type StrLits = Map String Word

type Lower = State StrLits

lower :: Ast.Program -> Program
lower (Ast.Program defs datas externs) = flip evalState Map.empty $ do
    defs' <- lowerDefs defs
    strs <- get
    let strs' = Vec.fromList $ map fst $ sortOn snd $ Map.toList strs
    pure (Program defs' (lowerDatas datas) (lowerExterns externs) strs')

builtinExterns :: Map String Type
builtinExterns = fmap lowerType Monomorphize.builtinExterns

lowerDefs :: Ast.Defs -> Lower Defs
lowerDefs (Topo defs) = fmap Topo $ mapM lowerDef defs

lowerDef :: Ast.Def -> Lower Def
lowerDef = \case
    Ast.VarDef d -> fmap VarDef $ lowerVarDef d
    Ast.RecDefs ds -> fmap RecDefs $ lowerRecDefs ds

lowerVarDef :: Ast.VarDef -> Lower VarDef
lowerVarDef = bimapM (pure . lowerTypedVar) (bimapM (pure . map lowerType) lowerExpr)

lowerRecDefs :: Ast.RecDefs -> Lower RecDefs
lowerRecDefs = mapM lowerFunDef

lowerFunDef :: Ast.FunDef -> Lower FunDef
lowerFunDef = bimapM (pure . lowerTypedVar) (bimapM (pure . map lowerType) lowerFun)

lowerFun :: Ast.Fun -> Lower Fun
lowerFun = bimapM (pure . lowerTypedVar) (bimapM lowerExpr (pure . lowerType))

lowerExpr :: Ast.Expr -> Lower Expr
lowerExpr = \case
    Ast.Lit (Ast.Int n) -> pure $ Lit (Int n)
    Ast.Lit (Ast.F64 x) -> pure $ Lit (F64 x)
    Ast.Lit (Ast.Str s) -> fmap (Lit . Str) (internStrLit s)
    Ast.Var v -> pure $ Var $ second lowerTypedVar v
    Ast.App f a -> lowerApp f [a]
    Ast.If p c a -> liftA3 If (lowerExpr p) (lowerExpr c) (lowerExpr a)
    Ast.Fun f -> fmap Fun (lowerFun f)
    Ast.Let d e -> liftA2 Let (lowerDef d) (lowerExpr e)
    Ast.Match m dt -> liftA2 Match (lowerExpr m) (lowerDecisionTree dt)
    Ast.Ction c -> fmap Ction $ lowerCtion c
    Ast.Sizeof t -> pure $ Sizeof $ lowerType t
    Ast.Absurd t -> pure $ Absurd $ lowerType t

internStrLit :: String -> Lower Word
internStrLit s = get >>= \m -> case Map.lookup s m of
    Just n -> pure n
    Nothing -> let n = fromIntegral (Map.size m) in modify (Map.insert s n) $> n

-- | Performs a sort of beta reduction
lowerApp :: Ast.Expr -> [Ast.Expr] -> Lower Expr
lowerApp = curry $ \case
    (Ast.Fun (p, (b, _)), a : as) -> liftA2
        Let
        (fmap (VarDef . (lowerTypedVar p, ) . (uniqueInst, )) (lowerExpr a))
        (lowerApp b as)
    (Ast.App f a, as) -> lowerApp f (a : as)
    (f, []) -> lowerExpr f
    (f, as) -> liftA2 App (lowerExpr f) (mapM lowerExpr as)
    where uniqueInst = []

lowerDecisionTree :: Ast.DecisionTree -> Lower DecisionTree
lowerDecisionTree = \case
    Ast.DLeaf (bs, e) -> liftA2 (DLeaf .* (,))
                                (pure $ map (bimap lowerTypedVar lowerAccess) bs)
                                (lowerExpr e)
    Ast.DSwitch span a cs def -> liftA2 (DSwitch span (lowerAccess a))
                                        (mapM lowerDecisionTree cs)
                                        (lowerDecisionTree def)
    Ast.DSwitchStr a cs def -> liftA2
        (DSwitchStr (lowerAccess a))
        (fmap Map.fromList $ mapM (bimapM internStrLit lowerDecisionTree) $ Map.toList cs)
        (lowerDecisionTree def)

lowerAccess :: Ast.Access -> Access
lowerAccess = fmap lowerType

lowerCtion :: Ast.Ction -> Lower Ction
lowerCtion (i, s, tc, es) = fmap (i, s, lowerTConst tc, ) $ mapM lowerExpr es

lowerDatas :: Ast.Datas -> Datas
lowerDatas = Map.fromList . map (bimap lowerTConst (map (map lowerType))) . Map.toList

lowerExterns :: Ast.Externs -> Externs
lowerExterns = map (\(x, t) -> (x, lowerType t))

lowerTypedVar :: Ast.TypedVar -> TypedVar
lowerTypedVar (Ast.TypedVar x t) = TypedVar x (lowerType t)

lowerTConst :: Ast.TConst -> TConst
lowerTConst = second (map lowerType)

lowerType :: Ast.Type -> Type
lowerType = \case
    Ast.TPrim p -> TPrim p
    Ast.TFun a r -> TFun (lowerType a) (lowerType r)
    Ast.TBox t -> TBox (lowerType t)
    Ast.TConst tc -> TConst (lowerTConst tc)
