{-# LANGUAGE TemplateHaskell, LambdaCase, TupleSections
           , TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses #-}

-- | Monomorphization
module Mono
    ( monomorphize
    , Defs(..)
    , Type(..)
    , TypedVar(..)
    , MProgram
    , MExpr
    , MTypedVar
    , mainType
    )
where

import qualified Data.Set as Set
import Control.Applicative (liftA2, liftA3)
import Control.Lens (makeLenses, over, views)
import Control.Monad.Reader
import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.List

import Misc
import qualified Ast
import Ast (TVar, TPrim(..), Scheme(..))
import Annot
import qualified Check
import Check (CExpr, CProgram)

data Type
    = TPrim TPrim
    | TFun Type
           Type
    | TConst String [Type]
    deriving (Show, Eq, Ord)

mainType :: Type
mainType = TFun (TPrim TUnit) (TPrim TUnit)

type MTypedVar = TypedVar Type
type MExpr = Expr Type Defs

newtype Defs =
    Defs (Map MTypedVar MExpr)
  deriving Show

type MProgram = Program Type Defs

data Env = Env
    { _defs :: Map String (Scheme, CExpr)
    , _tvBinds :: Map TVar Type
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
    Var (TypedVar x t) -> do
        t' <- monotype t
        addInst x t'
        pure (Var (TypedVar x t'))
    App f a -> liftA2 App (mono f) (mono a)
    If p c a -> liftA3 If (mono p) (mono c) (mono a)
    Fun (p, tp) (b, bt) -> do
        tp' <- monotype tp
        b' <- mono b
        bt' <- monotype bt
        pure (Fun (p, tp') (b', bt'))
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
            pure (TypedVar name t, body)
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
            body' <- local (over tvBinds (Map.union (bindTvs t2 t1))) (mono body)
            insertInst x t1 body'

bindTvs :: Ast.Type -> Type -> Map TVar Type
bindTvs = curry $ \case
    (Ast.TVar v, t) -> Map.singleton v t
    (Ast.TFun p0 r0, TFun p1 r1) -> Map.union (bindTvs p0 p1) (bindTvs r0 r1)
    (Ast.TPrim a, TPrim b) | a == b -> Map.empty
    (a, b) -> ice $ "bindTvs: " ++ show a ++ ", " ++ show b

monotype :: Ast.Type -> Mono Type
monotype = \case
    Ast.TVar v -> views tvBinds (lookup' (ice (show v ++ " not in tvBinds")) v)
    Ast.TPrim c -> pure (TPrim c)
    Ast.TFun a b -> liftA2 TFun (monotype a) (monotype b)
    Ast.TConst c ts -> fmap (TConst c) (mapM monotype ts)

insertInst :: String -> Type -> MExpr -> Mono ()
insertInst x t b = modify (Map.adjust (Map.insert t b) x)

lookup' :: Ord k => v -> k -> Map k v -> v
lookup' = Map.findWithDefault

lookups :: Ord k => [k] -> Map k v -> [(k, v)]
lookups ks m = catMaybes (map (\k -> fmap (k, ) (Map.lookup k m)) ks)

instance FreeVars Defs MTypedVar where
    freeVars (Defs ds) = Set.unions (map freeVars (Map.elems ds))
    boundVars (Defs ds) = Set.fromList (Map.keys ds)

instance Pretty MProgram where pretty' = prettyProg
instance Pretty Defs     where pretty' = prettyDefs
instance Pretty Type     where pretty' _ = prettyType

prettyType :: Type -> String
prettyType = \case
    TPrim c -> pretty c
    TFun a b -> concat ["(-> ", pretty a, " ", pretty b, ")"]
    TConst c ts ->
        concat ["(", c, " ", intercalate " " (map prettyType ts), ")"]

prettyDefs :: Int -> Defs -> String
prettyDefs d (Defs binds) = intercalate
    ("\n" ++ replicate d ' ')
    (map (prettyBinding d) (Map.toList binds))
  where
    prettyBinding d ((TypedVar name t), body) = concat
        [ "["
        , pretty name
        , " #instance "
        , pretty t
        , "\n"
        , replicate (d + 1) ' '
        , pretty' (d + 1) body
        , "]"
        ]

prettyProg :: Int -> MProgram -> String
prettyProg d (Annot.Program main (Mono.Defs defs)) =
    let
        allDefs = (TypedVar "main" Mono.mainType, main) : Map.toList defs
        prettyDef ((TypedVar name t), val) = concat
            [ replicate d ' '
            , "(define "
            , name
            , " #instance "
            , pretty t
            , "\n"
            , replicate (d + 2) ' '
            , pretty' (d + 2) val
            , ")"
            ]
    in unlines (map prettyDef allDefs)
