{-# LANGUAGE TemplateHaskell #-}

-- | Lower from higher level AST to our low-level IR
module Lower where

import Data.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Foldable
import Data.Function
import Data.Functor
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Lens.Micro.Platform (makeLenses, modifying, use, view, assign, to)

import Misc
import qualified Monomorphic as AST
import Monomorphic (TypedVar(..))
import Low
import FreeVars

data Env = Env
    { _localEnv :: Map TypedVar Operand
    }

data St = St
    { _strLits :: Map String Word
    -- A cache of already generated unapplied builtin virtuals
    , _builtinVirtuals :: Map (TypedVar, Word) Operand
    }

type Lower = StateT St (ReaderT Env (Writer [Stmt]))

makeLenses ''Env
makeLenses ''St

lowerExpr :: AST.Expr -> Lower Operand
lowerExpr (AST.Expr _ e) = lowerExpr' e

lowerExpr' :: AST.Expr' -> Lower Operand
lowerExpr' = \case
    AST.Lit c -> fmap Const $ lowerConst c
    AST.Var tv -> lookupVar tv
    AST.App f e _ -> lowerApp (f, [e])
    AST.If p c a -> do
        p' <- lowerExpr p
        lowerBranch p' (lowerExpr c) (lowerExpr a)
    AST.Fun (p, b) -> lowerLambda p b
    AST.Let d b -> lowerLet d b
    AST.Match e cs tbody -> lowerMatch e cs =<< lowerType tbody
    AST.Ction c -> lowerCtion c
    AST.Sizeof t -> undefined
    AST.Absurd t -> fmap undef (lowerType t)
  where
    lowerConst :: AST.Const -> Lower Const
    lowerConst = \case
        AST.Int n -> pure (Int n)
        AST.F64 x -> pure (F64 x)
        AST.Str s -> fmap Str $ lowerStrLit s

    lowerStrLit s = do
        m <- use strLits
        case Map.lookup s m of
            Just n -> pure n
            Nothing ->
                let n = fromIntegral (Map.size m)
                in  modifying strLits (Map.insert s n) $> n

    -- Beta-reduction and closure application
    lowerApp application = ask >>= \env -> case application of
        (AST.Expr _ (AST.Fun (p, (b, _))), ae : aes) -> do
            a <- lowerExpr ae
            withVal p a (lowerApp (b, aes))
        (AST.Expr _ (AST.App fe ae _), aes) -> lowerApp (fe, ae : aes)
        (fe, []) -> lowerExpr fe
        (AST.Expr _ (AST.Var x), aes) | isNothing (lookupVar' x env) ->
            lowerAppBuiltinVirtual x (map lowerExpr aes)
        (fe, aes) -> do
            f <- lowerExpr fe
            as <- mapM lowerExpr (init aes)
            closure <- foldlM app f as
            arg <- lowerExpr (last aes)
            app closure arg

    lowerBranch pred mconseq malt = undefined pred mconseq malt

    lowerLambda p (b, bt) = do
        fvs <- view localEnv <&> \locals -> Set.toList
            (Set.intersection (Set.delete p (freeVars b)) (Map.keysSet locals))
        lowerClosure fvs p (b, bt)

    lowerClosure fvs p (b, bt) = undefined

    lowerLet d b = undefined

    lowerMatch = undefined

    lowerCtion = undefined

    lowerType = undefined

    undef = undefined

app :: Operand -> Operand -> Lower Operand
app = undefined

-- | Given the name of a builtin virtual function and a list of arguments, generate the
--   lowering of applying this function to the list of arguments. An empty argument list
lowerAppBuiltinVirtual :: TypedVar -> [Lower Operand] -> Lower Operand
lowerAppBuiltinVirtual = undefined
   -- use builtinVirtuals to cache results

withVal :: TypedVar -> Operand -> Lower a -> Lower a
withVal x v = locally localEnv (Map.insert x v)

lookupVar :: TypedVar -> Lower Operand
lookupVar x = maybe (lowerAppBuiltinVirtual x []) pure =<< lookupVar' x

lookupVar' :: MonadReader Env m => TypedVar -> m (Maybe Operand)
lookupVar' x = undefined
