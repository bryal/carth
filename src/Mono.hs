{-# LANGUAGE TemplateHaskell, LambdaCase, TupleSections #-}

-- | Monomorphization
module Mono (monomorphize, Defs(..), Type(..), MProgram, MExpr) where

import Annot hiding (Type)
import qualified Annot
import Check (CExpr, CProgram, Scheme(..), unify'')
import qualified Check
import Control.Applicative (liftA2, liftA3)
import Control.Lens (makeLenses, over, views)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe

import Misc

data Type
    = TConst String
    | TFun Type
           Type
    deriving (Show, Eq, Ord)

instance Annot.Type Type where
    tConst = TConst
    tFun = TFun

type MExpr = Expr Type Defs

newtype Defs =
    Defs (Map (String, Type) MExpr)

type MProgram = Program Type Defs

data Env = Env
    { _defs :: Map String (Scheme, CExpr)
    , _tvBinds :: Map Check.TVar Type
    }

makeLenses ''Env

type Insts = Map String (Map Type MExpr)

-- | The monomorphization monad
type Mono = ReaderT Env (State Insts)

monomorphize :: CProgram -> MProgram
monomorphize (Program main ds) = (uncurry (flip Program))
    (evalState (runReaderT (monoLet ds main) initEnv) Map.empty)

initEnv :: Env
initEnv = Env {_defs = Map.empty, _tvBinds = Map.empty}

mono :: CExpr -> Mono MExpr
mono = \case
    Lit c -> pure (Lit c)
    Var x t -> do
        t' <- monotype t
        addInst x t'
        pure (Var x t')
    App f a -> liftA2 App (mono f) (mono a)
    If p c a -> liftA3 If (mono p) (mono c) (mono a)
    Fun (p, tp) b -> do
        tp' <- monotype tp
        b' <- mono b
        pure (Fun (p, tp') b')
    Let ds b -> fmap (uncurry Let) (monoLet ds b)

monoLet :: Check.Defs -> CExpr -> Mono (Defs, MExpr)
monoLet (Check.Defs ds) body = do
    let ks = Map.keys ds
    parentInsts <- gets (lookups ks)
    let newEmptyInsts = (fmap (const Map.empty) ds)
    modify (Map.union newEmptyInsts)
    body' <- local (over defs (Map.union ds)) (mono body)
    dsInsts <- gets (lookups ks)
    modify (Map.union (Map.fromList parentInsts))
    let
        ds' = Map.fromList $ do
            (name, dInsts) <- dsInsts
            (t, body) <- Map.toList dInsts
            pure ((name, t), body)
    pure (Defs ds', body')

addInst :: String -> Type -> Mono ()
addInst x t1 = do
    insts <- get
    case Map.lookup x insts of
        Nothing -> pure () -- If x is not in insts, it's a function parameter. Ignore.
        Just xInsts -> unless (Map.member t1 xInsts) $ do
            (Forall _ t2, body) <- views
                defs
                (lookup' (ice (x ++ " not in defs")) x)
            let s = either ice id (runExcept (unify'' (checktype t1) t2))
            s' <- mapM monotype s
            body' <- local (over tvBinds (Map.union s')) (mono body)
            insertInst x t1 body'

monotype :: Check.Type -> Mono Type
monotype = \case
    Check.TVar v -> views tvBinds (lookup' (ice (v ++ " not in tvBinds")) v)
    Check.TConst c -> pure (TConst c)
    Check.TFun a b -> liftA2 TFun (monotype a) (monotype b)

checktype :: Type -> Check.Type
checktype = \case
    TConst c -> tConst c
    TFun a b -> tFun (checktype a) (checktype b)

insertInst :: String -> Type -> MExpr -> Mono ()
insertInst x t b = modify (Map.adjust (Map.insert t b) x)

lookup' :: Ord k => v -> k -> Map k v -> v
lookup' = Map.findWithDefault

lookups :: Ord k => [k] -> Map k v -> [(k, v)]
lookups ks m = catMaybes (map (\k -> fmap (k, ) (Map.lookup k m)) ks)
