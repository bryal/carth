{-# LANGUAGE LambdaCase #-}

module Interp
    ( interpret
    ) where

import Annot
import Ast (Const(..), Id(..))
import qualified Builtin
import Control.Applicative (liftA3)
import Control.Monad.Reader
import Data.Bool.HT
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Val

type Env = Map String Val

type Eval = ReaderT Env IO

interpret :: Program -> IO ()
interpret p = runEval (evalProgram p)

runEval :: Eval a -> IO a
runEval m = runReaderT m Builtin.values

evalProgram :: Program -> Eval ()
evalProgram (Program main defs) = do
    f <- evalLet defs main
    fmap unwrapUnit (unwrapFun' f (VConst Unit))

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
        App ef ea -> do
            f <- fmap unwrapFun' (eval ef)
            a <- eval ea
            f a
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

unwrapFun' :: Val -> (Val -> Eval Val)
unwrapFun' v = \x -> lift (unwrapFun v x)
