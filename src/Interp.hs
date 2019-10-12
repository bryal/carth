{-# LANGUAGE LambdaCase #-}

module Interp (interpret) where

import Control.Applicative (liftA3)
import Control.Monad.Reader
import Data.Bool.HT
import Data.Functor
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Maybe

import Misc
import MonoAst

data Val
    = VConst Const
    | VFun (Val -> IO Val)
    | VConstruction String
                    [Val] -- ^ Arguments are in reverse order--last arg first

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
evalProgram (Program main defs) = do
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
    Match e cs -> eval e >>= flip evalCases cs
    Constructor c -> pure (VConstruction c [])

evalApp :: Expr -> Expr -> Eval Val
evalApp ef ea = eval ef >>= \case
    VFun f -> eval ea >>= lift . f
    VConstruction c xs -> fmap (VConstruction c . (: xs)) (eval ea)
    v -> ice ("Application of non-function: " ++ showVariant v)

evalLet :: Defs -> Expr -> Eval Val
evalLet defs body = do
    defs' <- evalDefs defs
    withLocals defs' (eval body)

evalCases :: Val -> [(Pat, Expr)] -> Eval Val
evalCases matchee = \case
    [] -> ice "Non-exhaustive patterns in match. Fell out!"
    (p, b) : cs -> matchPat matchee p >>= \case
        Just defs -> withLocals defs (eval b)
        Nothing -> evalCases matchee cs

matchPat :: Val -> Pat -> Eval (Maybe (Map TypedVar Val))
matchPat = curry $ \case
    (VConstruction c xs, PConstruction c' ps) | c == c' ->
        zipWithM matchPat (reverse xs) ps <&> sequence <&> \case
            Just defss -> Just (Map.unions defss)
            Nothing -> Nothing
    (_, PConstruction _ _) -> pure Nothing
    (x, PVar v) -> pure (Just (Map.singleton v x))

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
    VConstruction c _ -> "construction of " ++ c
