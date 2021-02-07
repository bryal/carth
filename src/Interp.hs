module Interp (interpret) where

import Control.Monad.Reader
import Data.Foldable
import Data.Functor
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe

import Misc
import SrcPos
import TypeAst
import Selections
import Optimized

type Env = Map TypedVar Val

type Eval = ReaderT Env IO

data Val
    = VInt Int
    | VF64 Double
    | VStr String
    | VFun (Val -> IO Val)
    | VData VariantIx [Val]

instance Show Val where
    show = \case
        VInt x -> "VInt " ++ show x
        VF64 x -> "VF64 " ++ show x
        VStr s -> "VStr " ++ show s
        VFun _ -> "VFun ..."
        VData c xs -> "VData " ++ show c ++ " " ++ show xs

instance Select Eval Val where
    selectAs _ _ = pure
    selectSub _ i = \case
        v@(VData _ xs) ->
            let i' = fromIntegral i
                msg = "i >= length xs in evalSub: " ++ (show i ++ ", " ++ show v)
            in  pure (if i' < length xs then xs !! i' else ice msg)
        _ -> ice "evalSub of non VConstruction"
    selectDeref = pure . deref

interpret :: Program -> IO ()
interpret (Program (Topo defs) _datas _externs) =
    let runMain = (lookupVar (TypedVar "main" mainType) >>= (lift . performIO)) $> ()
        initEnv = Map.empty
    in  runEval initEnv $ foldr withDef runMain defs

withDef :: Def -> Eval a -> Eval a
withDef = flip (foldr withVarDef) . defToVarDefs

withVarDef :: VarDef -> Eval a -> Eval a
withVarDef (lhs, rhs) ma = do
    rhs' <- eval' (snd (unpos rhs))
    withLocal lhs rhs' ma

withLocal :: TypedVar -> Val -> Eval a -> Eval a
withLocal lhs rhs = local (Map.insert lhs rhs)

runEval :: Map TypedVar Val -> Eval a -> IO a
runEval env ma = runReaderT ma env

performIO :: Val -> IO Val
performIO =
    fmap car . (flip app realWorld) . fromMaybe undefined . safeHead . snd . unwrapData

eval :: Expr -> Eval Val
eval (Expr _ e) = eval' e

eval' :: Expr' -> Eval Val
eval' = \case
    Lit (Int x) -> pure (VInt x)
    Lit (F64 x) -> pure (VF64 x)
    Lit (Str s) -> pure (VStr s)
    Var x -> lookupVar x
    App f e _t -> bind2 (lift .* app) (eval f) (eval e)
    If p c a -> eval p >>= \p' -> if getBool p' then eval c else eval a
    Fun (p, (b, _)) ->
        fmap (\env -> VFun (\v -> runEval env $ withLocal p v (eval b))) ask
    Let def e -> withDef def (eval e)
    Match m cs _t -> do
        m' <- eval m
        evalDecisionTree cs (newSelections m')
    Ction (variant, _, _, es) -> fmap (VData variant) (mapM eval es)
    Sizeof _t -> nyi "eval Sizeof"
    Absurd _t -> undefined

evalDecisionTree :: DecisionTree -> Selections Val -> Eval Val
evalDecisionTree dt selections = case dt of
    DSwitch selector cs def -> do
        (m, selections') <- select selector selections
        case m of
            VData ctor _ ->
                evalDecisionTree (fromMaybe def (Map.lookup ctor cs)) selections'
            _ -> ice "not VConstruction in evalDecisionSwitch"
    DSwitchStr selector cs def -> do
        (matchee, selections') <- select selector selections
        let cs' = Map.toAscList cs
        let handleCase (s, dt) next = do
                let isMatch = unwrapStr matchee == s
                pure $ if isMatch then (evalDecisionTree dt selections') else next
        join (foldrM handleCase (evalDecisionTree def selections') cs')
    DLeaf (bs, e) ->
        foldr (uncurry withLocal) (eval e) =<< selectVarBindings selections bs

lookupVar :: TypedVar -> Eval Val
lookupVar x = asks (fromMaybe undefined . Map.lookup x)

app :: Val -> Val -> IO Val
app = unwrapFun

car :: Val -> Val
car = fromMaybe undefined . safeHead . snd . unwrapData

deref :: Val -> Val
deref = id

unwrapData :: Val -> (VariantIx, [Val])
unwrapData = \case
    VData a bs -> (a, bs)
    _ -> undefined

unwrapFun :: Val -> (Val -> IO Val)
unwrapFun = \case
    VFun f -> f
    _ -> undefined

unwrapStr :: Val -> String
unwrapStr = \case
    VStr s -> s
    _ -> undefined

getBool :: Val -> Bool
getBool = \case
    VData 0 [] -> False
    VData 1 [] -> True
    _ -> undefined

realWorld :: Val
realWorld = VData 0 []
