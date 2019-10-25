{-# LANGUAGE LambdaCase #-}

module Interp (interpret) where

import Control.Applicative (liftA3)
import Control.Monad.Reader
import Data.Bool.HT
import Data.Functor
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Maybe
import Data.List

import Misc
import MonoAst

data Val
    = VConst Const
    | VFun (Val -> IO Val)
    | VConstruction VariantIx
                    [Val] -- ^ Arguments are in reverse order -- last arg first

type Env = Map TypedVar Val

type Eval = ReaderT Env IO

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
        evalDecisionTree [v] dt
    Ction (i, _, as) -> fmap (VConstruction i) (mapM eval as)

evalApp :: Expr -> Expr -> Eval Val
evalApp ef ea = eval ef >>= \case
    VFun f -> eval ea >>= lift . f
    v -> ice ("Application of non-function: " ++ showVariant v)

evalLet :: Defs -> Expr -> Eval Val
evalLet defs body = do
    defs' <- evalDefs defs
    withLocals defs' (eval body)

-- | Out to in, left to right.
evalDecisionTree :: [Val] -> DecisionTree -> Eval Val
evalDecisionTree stack = \case
    DecisionTree cs default' -> do
        let
            (m, ms) = fromMaybe
                (ice "Stack is empty in evalDecisionTree")
                (uncons stack)
        evalDecisionTree' m ms cs >>= \case
            Just v -> pure v
            Nothing -> case default' of
                Just (tv, d) -> withLocal tv m (evalDecisionTree ms d)
                Nothing ->
                    ice "default' is Nothing after fail in evalDecisionTree"
    DecisionLeaf e -> eval e

evalDecisionTree'
    :: Val
    -> [Val]
    -> Map VariantIx (VariantTypes, DecisionTree)
    -> Eval (Maybe Val)
evalDecisionTree' m ms cs = case m of
    VConstruction ctor xs -> case Map.lookup ctor cs of
        Just (_, d) -> fmap Just (evalDecisionTree (xs ++ ms) d)
        Nothing -> pure Nothing
    _ -> pure Nothing

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
