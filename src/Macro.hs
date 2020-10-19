{-# LANGUAGE LambdaCase #-}

module Macro (expandMacros) where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map

import SrcPos
import Lexd
import Parser

type Macros = Map String ([String], [TokenTree])
type Bindings = Map String TokenTree
type Expand = ReaderT Bindings (StateT Macros (Except (SrcPos, String)))

expandMacros :: [TokenTree] -> Except (SrcPos, String) [TokenTree]
expandMacros tts = evalStateT (runReaderT (toplevels tts) Map.empty) Map.empty

toplevels :: [TokenTree] -> Expand [TokenTree]
toplevels = fmap concat . mapM toplevel

toplevel :: TokenTree -> Expand [TokenTree]
toplevel = \case
    WithPos _ (Parens (WithPos _ (Keyword Kdefmacro) : tts)) -> do
        def <- lift $ lift $ runParser pdefmacro tts
        modify (uncurry Map.insert def)
        pure []
    tt -> expand tt

pdefmacro :: Parser (String, ([String], [TokenTree]))
pdefmacro = do
    (x, params) <- parens (liftA2 (,) small' (many small'))
    template <- many anyToken
    pure (x, (params, template))

expand :: TokenTree -> Expand [TokenTree]
expand tt@(WithPos tpos tt') = do
    bs <- ask
    ms <- get
    case tt' of
        Lit _ -> pure [tt]
        Small x -> case Map.lookup x bs of
            Just xtt -> pure [xtt]
            Nothing -> pure [tt]
        Big _ -> pure [tt]
        Keyword _ -> pure [tt]
        Parens (WithPos _ (Small x) : tts) | Just m <- Map.lookup x ms -> do
            tts' <- expands tts
            applyMacro tpos m tts'
        Parens tts -> par Parens tts
        Brackets tts -> par Brackets tts
        Braces tts -> par Braces tts
    where par ctor tts = fmap (pure . WithPos tpos . ctor) (expands tts)

expands :: [TokenTree] -> Expand [TokenTree]
expands = fmap concat . mapM expand

applyMacro :: SrcPos -> ([String], [TokenTree]) -> [TokenTree] -> Expand [TokenTree]
applyMacro appPos (params, template) args = if length params /= length args
    then throwError
        ( appPos
        , "Arity mismatch in application of macro.\n"
        ++ ("Expected " ++ show (length params))
        ++ (", found " ++ show (length args))
        )
    else local (Map.union (Map.fromList (zip params args))) (expands template)
