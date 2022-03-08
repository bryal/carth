module Front.Macro (expandMacros) where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Misc
import Front.SrcPos
import Front.Lexd
import Front.Parser

type Literals = Set String
type Rules = [([TokenTree], [TokenTree])]
type Macros = Map String (Literals, Rules)
type Bindings = Map String TokenTree'
type Expand = ReaderT (Bindings, Maybe SrcPos) (StateT Macros (Except (SrcPos, String)))

expandMacros :: [TokenTree] -> Except (SrcPos, String) [TokenTree]
expandMacros tts = evalStateT (runReaderT (toplevels tts) (Map.empty, Nothing)) Map.empty

toplevels :: [TokenTree] -> Expand [TokenTree]
toplevels = fmap concat . mapM toplevel

toplevel :: TokenTree -> Expand [TokenTree]
toplevel = \case
    WithPos mpos (Parens (WithPos _ (Keyword Kdefmacro) : tts)) -> do
        (name, lits, rules) <- lift $ lift $ runParser pdefmacro mpos tts
        modify (Map.insert name (lits, rules))
        pure []
    tt -> expand tt

pdefmacro :: Parser (String, Literals, Rules)
pdefmacro = liftA3 (,,) small' (fmap Set.fromList (parens (many small'))) (some prule)
  where
    prule = parens $ do
        reserved Kcase
        params <- parens (many anyToken)
        template <- many anyToken
        pure (params, template)

expand :: TokenTree -> Expand [TokenTree]
expand (WithPos tpos tt') = do
    (bs, expPos) <- ask
    ms <- get
    let tpos' = tpos { inExpansion = expPos }
    let tt = WithPos tpos' tt'
    let par ctor tts = fmap (pure . WithPos tpos' . ctor) (expands tts)
    case tt' of
        Lit _ -> pure [tt]
        Small x -> case Map.lookup x bs of
            Just xtt -> pure [WithPos tpos' xtt]
            Nothing -> pure [tt]
        Big _ -> pure [tt]
        Keyword _ -> pure [tt]
        Parens (WithPos _ (Small x) : tts1) | Just m <- Map.lookup x ms -> do
            tts2 <- expands tts1
            local (second (const (Just tpos'))) $ do
                tts3 <- uncurry (applyMacro tpos' tts2) m
                expands tts3
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

expands :: [TokenTree] -> Expand [TokenTree]
expands = fmap concat . mapM expand

applyMacro :: SrcPos -> [TokenTree] -> Literals -> Rules -> Expand [TokenTree]
applyMacro appPos args lits = \case
    [] -> throwError (appPos, "No rule matched in application of macro")
    (params, template) : rules -> case matchRule (map unpos params, args) of
        Just bindings -> local (first (Map.union bindings)) (expands template)
        Nothing -> applyMacro appPos args lits rules
  where
    matchRule :: ([TokenTree'], [TokenTree]) -> Maybe (Map String TokenTree')
    matchRule = \case
        ([], []) -> Just mempty
        (Ellipsis (WithPos _ x) : xs, ys) ->
            let ms = takeWhileJust (matchPat x) ys
                ys' = drop (length ms) ys
                -- By default, each pattern variable in an ellipsis pattern should be
                -- bound to an empty Parens, even if ys was empty
                ms' = Map.fromSet (const []) (fvPat x) : map (fmap pure) ms
                ms'' = fmap Parens (Map.unionsWith (++) ms')
            in  fmap (Map.union ms'') (matchRule (xs, ys'))
        (x : xs, y : ys) ->
            liftA2 (Map.union . fmap unpos) (matchPat x y) (matchRule (xs, ys))
        ([], _ : _) -> Nothing
        (_ : _, []) -> Nothing

    matchPat :: TokenTree' -> TokenTree -> Maybe (Map String TokenTree)
    matchPat p (WithPos apos a) = case (p, a) of
        (Small x, _) | not (Set.member x lits) -> Just (Map.singleton x (WithPos apos a))
        (Parens xs, Parens ys) -> par xs ys
        (Brackets xs, Brackets ys) -> par xs ys
        (Braces xs, Braces ys) -> par xs ys
        (_, _) | p == a -> Just mempty
               | otherwise -> Nothing
      where
        par xs ys = if length xs == length ys
            then fmap Map.unions $ zipWithM matchPat (map unpos xs) ys
            else Nothing

    fvPat = \case
        Small x | not (Set.member x lits) -> Set.singleton x
        Parens tts -> par tts
        Brackets tts -> par tts
        Braces tts -> par tts
        Ellipsis tt -> fvPat (unpos tt)
        _ -> Set.empty
        where par = Set.unions . map (fvPat . unpos)
