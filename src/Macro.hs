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

type Rules = [([TokenTree], [TokenTree])]
type Macros = Map String Rules
type Bindings = Map String TokenTree'
type Expand = ReaderT Bindings (StateT Macros (Except (SrcPos, String)))

expandMacros :: [TokenTree] -> Except (SrcPos, String) [TokenTree]
expandMacros tts = evalStateT (runReaderT (toplevels tts) Map.empty) Map.empty

toplevels :: [TokenTree] -> Expand [TokenTree]
toplevels = fmap concat . mapM toplevel

toplevel :: TokenTree -> Expand [TokenTree]
toplevel = \case
    WithPos mpos (Parens (WithPos _ (Keyword Kdefmacro) : tts)) -> do
        def <- lift $ lift $ runParser pdefmacro mpos tts
        validateRules (snd def)
        modify (uncurry Map.insert def)
        pure []
    tt -> expand tt

pdefmacro :: Parser (String, Rules)
pdefmacro = liftA2 (,) small' (some prule)
  where
    prule = parens $ do
        reserved Kcase
        params <- parens (many anyToken)
        template <- many anyToken
        pure (params, template)

-- TODO: Check for example that there's max one ellipses in the params.
validateRules :: Rules -> Expand ()
validateRules _ = pure ()

expand :: TokenTree -> Expand [TokenTree]
expand tt@(WithPos tpos tt') = do
    bs <- ask
    ms <- get
    case tt' of
        Lit _ -> pure [tt]
        Small x -> case Map.lookup x bs of
            Just xtt -> pure [WithPos tpos xtt]
            Nothing -> pure [tt]
        Big _ -> pure [tt]
        Keyword _ -> pure [tt]
        Parens (WithPos _ (Small x) : tts) | Just m <- Map.lookup x ms -> do
            tts' <- expands tts
            applyMacro tpos tts' m
        Parens tts -> par Parens tts
        Brackets tts -> par Brackets tts
        Braces tts -> par Braces tts
        Ellipsis (WithPos epos (Small x)) -> case Map.lookup x bs of
            Just (Parens xtts) -> expands xtts
            Just (Brackets xtts) -> expands xtts
            Just (Braces xtts) -> expands xtts
            Just _ -> throwError
                (epos, "Cannot ellipsis splice non-sequence macro pattern variable")
            Nothing -> throwError (epos, "Unbound macro pattern variable")
        Ellipsis (WithPos epos _) ->
            throwError (epos, "Can only ellipsis splice macro pattern variable")
    where par ctor tts = fmap (pure . WithPos tpos . ctor) (expands tts)

expands :: [TokenTree] -> Expand [TokenTree]
expands = fmap concat . mapM expand

applyMacro :: SrcPos -> [TokenTree] -> Rules -> Expand [TokenTree]
applyMacro appPos args = \case
    [] -> throwError (appPos, "No rule matched in application of macro")
    (params, template) : rules -> case matchRule (map unpos params, args) of
        Just bindings -> local (Map.union (Map.fromList bindings)) (expands template)
        Nothing -> applyMacro appPos args rules
  where
    matchRule = \case
        ([], []) -> Just []
        (Ellipsis (WithPos _ (Small x)) : _, args) -> Just [(x, Parens args)]
        (Small x : params, arg : args) ->
            fmap ((x, unpos arg) :) (matchRule (params, args))
        _ -> Nothing
