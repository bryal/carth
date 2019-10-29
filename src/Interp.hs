{-# LANGUAGE LambdaCase #-}

module Interp (interpret) where

import Control.Applicative (liftA3)
import Control.Monad.Reader
import Data.Functor
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Maybe
import Data.Word

import Misc
import MonoAst
import Selections

data Val
    = VConst Const
    | VFun (Val -> IO Val)
    | VConstruction VariantIx
                    [Val] -- ^ Arguments are in reverse order -- last arg first

type Env = Map TypedVar Val

type Eval = ReaderT Env IO


instance Show Val where
    show = \case
        VConst c -> "VConst " ++ show c ++ ""
        VFun _ -> "VFun"
        VConstruction c xs -> "VConstruction " ++ show c ++ " " ++ show xs

interpret :: Program -> IO ()
interpret p = runEval (evalProgram p)

runEval :: Eval a -> IO a
runEval m = runReaderT m builtinValues

builtinValues :: Map TypedVar Val
builtinValues = Map.fromList
    [ ( TypedVar "printInt" (TFun (TPrim TInt) (TPrim TUnit))
      , VFun (\v -> print (unwrapInt v) $> VConst Unit)
      )
    , ( TypedVar "+" (TFun (TPrim TInt) (TFun (TPrim TInt) (TPrim TInt)))
      , VFun (\a -> pure (VFun (\b -> pure (plus a b))))
      )
    ]

plus :: Val -> Val -> Val
plus a b = VConst (Int (unwrapInt a + unwrapInt b))

evalProgram :: Program -> Eval ()
evalProgram (Program main defs _) = do
    f <- evalLet defs main
    fmap unwrapUnit (unwrapFun' f (VConst Unit))

evalDefs :: Defs -> Eval (Map TypedVar Val)
evalDefs (Defs defs) = do
    let (defNames, defBodies) = unzip (Map.toList defs)
    mfix $ \(~defs') -> do
        defVals <- withLocals defs' (mapM eval defBodies)
        pure (Map.fromList (zip defNames defVals))

eval :: Expr -> Eval Val
eval = \case
    Lit c -> pure (VConst c)
    Var (TypedVar x t) -> lookupEnv (x, t)
    App ef ea -> evalApp ef ea
    If p c a -> liftA3 (if' . unwrapBool) (eval p) (eval c) (eval a)
    Fun p (b, _) -> do
        env <- ask
        pure (VFun (\v -> runEval (withLocals env (withLocal p v (eval b)))))
    Let defs body -> evalLet defs body
    Match e dt _ -> do
        v <- eval e
        evalDecisionTree dt (newSelections v)
    Ction (i, _, as) -> fmap (VConstruction i) (mapM eval as)

evalApp :: Expr -> Expr -> Eval Val
evalApp ef ea = eval ef >>= \case
    VFun f -> eval ea >>= lift . f
    v -> ice ("Application of non-function: " ++ showVariant v)

evalLet :: Defs -> Expr -> Eval Val
evalLet defs body = do
    defs' <- evalDefs defs
    withLocals defs' (eval body)

evalDecisionTree :: DecisionTree -> Selections Val -> Eval Val
evalDecisionTree = \case
    DSwitch selector cs def -> evalDecisionSwitch selector cs def
    DLeaf l -> evalDecisionLeaf l

evalDecisionSwitch
    :: Access
    -> Map VariantIx DecisionTree
    -> DecisionTree
    -> Selections Val
    -> Eval Val
evalDecisionSwitch selector cs def selections = do
    (m, selections') <- evalSelect selector selections
    case m of
        VConstruction ctor _ ->
            evalDecisionTree (fromMaybe def (Map.lookup ctor cs)) selections'
        _ -> ice "not VConstruction in evalDecisionSwitch"

evalDecisionLeaf :: (VarBindings, Expr) -> Selections Val -> Eval Val
evalDecisionLeaf (bs, e) selections = flip withLocals (eval e)
    =<< fmap Map.fromList (evalSelectVarBindings selections bs)

evalSelect :: Access -> Selections Val -> Eval (Val, Selections Val)
evalSelect = select evalAs evalSub

evalSelectVarBindings :: Selections Val -> VarBindings -> Eval [(TypedVar, Val)]
evalSelectVarBindings = selectVarBindings evalAs evalSub

evalAs :: [MonoAst.Type] -> Val -> Eval Val
evalAs _ = pure

evalSub :: Word32 -> Val -> Eval Val
evalSub i = \case
    v@(VConstruction _ xs) ->
        let
            i' = fromIntegral i
            msg = "i >= length xs in evalSub: " ++ (show i ++ ", " ++ show v)
        in pure (if i' < length xs then xs !! i' else ice msg)
    _ -> ice "evalSub of non VConstruction"

lookupEnv :: (String, Type) -> Eval Val
lookupEnv (x, t) = fmap
    (fromMaybe (ice ("Unbound variable: " ++ x ++ " of type " ++ show t)))
    (asks (Map.lookup (TypedVar x t)))

withLocals :: Map TypedVar Val -> Eval a -> Eval a
withLocals defs = local (Map.union defs)

withLocal :: TypedVar -> Val -> Eval a -> Eval a
withLocal var val = local (Map.insert var val)

unwrapFun' :: Val -> (Val -> Eval Val)
unwrapFun' v = \x -> lift (unwrapFun v x)

unwrapUnit :: Val -> ()
unwrapUnit = \case
    VConst Unit -> ()
    x -> ice ("Unwrapping unit, found " ++ showVariant x)

unwrapInt :: Val -> Int
unwrapInt = \case
    VConst (Int n) -> n
    x -> ice ("Unwrapping int, found " ++ showVariant x)

unwrapBool :: Val -> Bool
unwrapBool = \case
    VConst (Bool b) -> b
    x -> ice ("Unwrapping bool, found " ++ showVariant x)

unwrapFun :: Val -> (Val -> IO Val)
unwrapFun = \case
    VFun f -> f
    x -> ice ("Unwrapping function, found " ++ showVariant x)

showVariant :: Val -> String
showVariant = \case
    VConst c -> case c of
        Unit -> "unit"
        Int _ -> "int"
        Double _ -> "double"
        Str _ -> "string"
        Bool _ -> "bool"
        Char _ -> "character"
    VFun _ -> "function"
    VConstruction c _ -> "construction of variant " ++ show c
