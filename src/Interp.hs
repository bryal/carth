{-# LANGUAGE LambdaCase #-}

module Interp
    ( interpret
    ) where

import Annot
import Ast (Const(..), Id(..))
import Control.Applicative (liftA3)
import Control.Monad.Reader
import Data.Bool.HT
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe

data Val
    = VConst Const
    | VFun (Val -> Val)

type Env = Map String Val

type Eval = Reader Env

interpret :: Program -> Int
interpret p = runEval (evalProgram p)

runEval :: Eval a -> a
runEval m = runReader m Map.empty

evalProgram :: Program -> Eval Int
evalProgram (Program main defs) = do
    f <- evalLet defs main
    pure (unwrapInt (unwrapFun f (VConst Unit)))

evalDefs :: Defs -> Eval (Map String Val)
evalDefs defs = do
    let defs' = map (\(Id name, (_, body)) -> (name, body)) (Map.toList defs)
    let (defNames, defBodies) = unzip defs'
    defVals <- mapM eval defBodies
    pure (Map.fromList (zip defNames defVals))

eval :: Expr -> Eval Val
eval =
    \case
        Lit c -> pure (VConst c)
        Var (Id x) -> lookupEnv x
        App f a -> fmap unwrapFun (eval f) <*> eval a
        If p c a -> liftA3 (if' . unwrapBool) (eval p) (eval c) (eval a)
        Fun (Id p) b -> do
            env <- ask
            let f v = runEval (withLocals env (withLocal p v (eval b)))
            pure (VFun f)
        Let defs body -> evalLet defs body
        Match _ _ -> undefined
        FunMatch _ -> undefined
        Constructor _ -> undefined

evalLet :: Defs -> Expr -> Eval Val
evalLet defs body = do
    defs' <- evalDefs defs
    withLocals defs' (eval body)

lookupEnv :: String -> Eval Val
lookupEnv x =
    fmap (fromMaybe (ice ("Unbound variable: " ++ x))) (asks (Map.lookup x))

withLocals :: Map String Val -> Eval a -> Eval a
withLocals defs = local (Map.union defs)

withLocal :: String -> Val -> Eval a -> Eval a
withLocal var val = local (Map.insert var val)

unwrapInt :: Val -> Int
unwrapInt =
    \case
        VConst (Int n) -> n
        x -> ice ("Unwrapping int, found " ++ showVariant x)

unwrapBool :: Val -> Bool
unwrapBool =
    \case
        VConst (Bool b) -> b
        x -> ice ("Unwrapping bool, found " ++ showVariant x)

unwrapFun :: Val -> (Val -> Val)
unwrapFun =
    \case
        VFun f -> f
        x -> ice ("Unwrapping function, found " ++ showVariant x)

showVariant :: Val -> String
showVariant =
    \case
        VConst c ->
            case c of
                Unit -> "unit"
                Int _ -> "int"
                Double _ -> "double"
                Str _ -> "string"
                Bool _ -> "bool"
                Char _ -> "character"
        VFun _ -> "function"

ice :: String -> a
ice msg = error ("Internal compiler error: " ++ msg)
