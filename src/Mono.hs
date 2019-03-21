{-# LANGUAGE TemplateHaskell, LambdaCase, TupleSections #-}

-- | Monomorphization
module Mono
    ( monomorphize
    , Program(..)
    , Expr(..)
    , Defs
    , Type(..)
    , typeUnit
    , typeInt
    , typeDouble
    , typeStr
    , typeBool
    , typeChar
    , mainType
    , ice
    ) where

import qualified Annot
import Ast (Const(..))
import Check (unify'')
import Control.Applicative (liftA2, liftA3)
import Control.Lens (makeLenses, over, views)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe

data Type
    = TConst String
    | TFun Type
           Type
    deriving (Show, Eq, Ord)

typeUnit, typeInt, typeDouble, typeStr, typeBool, typeChar :: Type
typeUnit = TConst "Unit"

typeInt = TConst "Int"

typeDouble = TConst "Double"

typeChar = TConst "Char"

typeStr = TConst "Str"

typeBool = TConst "Bool"

mainType :: Type
mainType = TFun typeUnit typeUnit

data Expr
    = Lit Const
    | Var String
          Type
    | App Expr
          Expr
    | If Expr
         Expr
         Expr
    | Fun (String, Type)
          Expr
    | Let Defs
          Expr
    deriving (Show, Eq)

type Defs = Map (String, Type) Expr

data Program =
    Program Expr
            Defs
    deriving (Show)

data Env = Env
    { _defs :: Map String (Annot.Scheme, Annot.Expr)
    , _tvBinds :: Map Annot.TVar Type
    }

makeLenses ''Env

type Insts = Map String (Map Type Expr)

-- | The monomorphization monad
type Mono = ReaderT Env (State Insts)

monomorphize :: Annot.Program -> Program
monomorphize (Annot.Program main ds) =
    (uncurry (flip Program))
        (evalState (runReaderT (monoLet ds main) initEnv) Map.empty)

initEnv :: Env
initEnv = Env {_defs = Map.empty, _tvBinds = Map.empty}

mono :: Annot.Expr -> Mono Expr
mono =
    \case
        Annot.Lit c -> pure (Lit c)
        Annot.Var x t -> do
            t' <- monotype t
            addInst x t'
            pure (Var x t')
        Annot.App f a -> liftA2 App (mono f) (mono a)
        Annot.If p c a -> liftA3 If (mono p) (mono c) (mono a)
        Annot.Fun (p, tp) b -> do
            tp' <- monotype tp
            b' <- mono b
            pure (Fun (p, tp') b')
        Annot.Let ds b -> fmap (uncurry Let) (monoLet ds b)

monoLet :: Annot.Defs -> Annot.Expr -> Mono (Defs, Expr)
monoLet ds body = do
    let ks = Map.keys ds
    parentInsts <- gets (lookups ks)
    let newEmptyInsts = (fmap (const Map.empty) ds)
    modify (Map.union newEmptyInsts)
    body' <- local (over defs (Map.union ds)) (mono body)
    dsInsts <- gets (lookups ks)
    modify (Map.union (Map.fromList parentInsts))
    let ds' =
            Map.fromList $ do
                (name, dInsts) <- dsInsts
                (t, body) <- Map.toList dInsts
                pure ((name, t), body)
    pure (ds', body')

addInst :: String -> Type -> Mono ()
addInst x t1 = do
    insts <- get
    case Map.lookup x insts of
        Nothing -> pure () -- If x is not in insts, it's a function parameter. Ignore.
        Just xInsts ->
            unless (Map.member t1 xInsts) $ do
                (Annot.Forall _ t2, body) <-
                    views defs (lookup' (ice (x ++ " not in defs")) x)
                let s = either ice id (runExcept (unify'' (annottype t1) t2))
                s' <- mapM monotype s
                body' <- local (over tvBinds (Map.union s')) (mono body)
                insertInst x t1 body'

monotype :: Annot.Type -> Mono Type
monotype =
    \case
        Annot.TVar v -> views tvBinds (lookup' (ice (v ++ " not in tvBinds")) v)
        Annot.TConst c -> pure (TConst c)
        Annot.TFun a b -> liftA2 TFun (monotype a) (monotype b)

annottype :: Type -> Annot.Type
annottype =
    \case
        TConst c -> Annot.TConst c
        TFun a b -> Annot.TFun (annottype a) (annottype b)

insertInst :: String -> Type -> Expr -> Mono ()
insertInst x t b = modify (Map.adjust (Map.insert t b) x)

lookup' :: Ord k => v -> k -> Map k v -> v
lookup' = Map.findWithDefault

lookups :: Ord k => [k] -> Map k v -> [(k, v)]
lookups ks m = catMaybes (map (\k -> fmap (k, ) (Map.lookup k m)) ks)

ice :: String -> a
ice msg = error ("Internal compiler error: " ++ msg)
