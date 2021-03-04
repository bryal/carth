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
import Lens.Micro.Platform (makeLenses, modifying, use, view, assign, to)

import Misc
import qualified Monomorphic as AST
import Monomorphic (TypedVar(..))
import Low

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
    AST.Lit c -> lowerConst c
    AST.Var tv -> lookupVar tv
    AST.App f e _ -> lowerApp (f, [e])
    _ -> nyi "rest of lowerExpr'"
  where

    lowerConst = \case
        AST.Int n -> pure (Const (Int n))
        AST.F64 x -> pure (Const (F64 x))
        AST.Str s -> fmap (Const . Str) $ lowerStrLit s

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

app :: Operand -> Operand -> Lower Operand
app = nyi "app"

-- | Given the name of a builtin virtual function and a list of arguments, generate the
--   lowering of applying this function to the list of arguments. An empty argument list
lowerAppBuiltinVirtual :: TypedVar -> [Lower Operand] -> Lower Operand
lowerAppBuiltinVirtual = nyi "lowerAppBuiltinVirtual"
   -- use builtinVirtuals to cache results

withVal :: TypedVar -> Operand -> Lower a -> Lower a
withVal x v = locally localEnv (Map.insert x v)

lookupVar :: TypedVar -> Lower Operand
lookupVar x = maybe (lowerAppBuiltinVirtual x []) pure =<< lookupVar' x

lookupVar' :: MonadReader Env m => TypedVar -> m (Maybe Operand)
lookupVar' x = nyi "lookupVar'"
