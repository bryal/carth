{-# LANGUAGE TemplateHaskell, DataKinds #-}

module Front.Parser where

import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer
import Control.Monad.Except
import Data.Bifunctor
import Data.Functor
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set
import Lens.Micro.Platform (makeLenses, view)

import Misc
import Front.SrcPos
import Front.Lexd
import Front.Parsed
import Pretty

data Err = Err
    { errLength :: Word
    , errPos :: SrcPos
    , errExpecteds :: Set String
    }
    deriving (Show, Eq)

instance Semigroup Err where
    (<>) e1 e2
        | e2 == mempty = e1
        | errLength e1 > errLength e2 = e1
        | errLength e1 < errLength e2 = e2
        | otherwise = Err (errLength e2)
                          (errPos e2)
                          (Set.union (errExpecteds e1) (errExpecteds e2))

instance Monoid Err where
    mempty = Err 0 (SrcPos "<dummy>" 0 0 Nothing) Set.empty

data St = St
    { stCount :: Word
    , stOuterPos :: SrcPos
    , stInput :: [TokenTree]
    }
    deriving Show

data Out = Out
    { _deBruijnIndices :: [Word]
    , _messages :: [Message]
    }
makeLenses ''Out

instance Semigroup Out where
    (<>) (Out xs1 ys1) (Out xs2 ys2) = Out (xs1 ++ xs2) (ys1 ++ ys2)

instance Monoid Out where
    mempty = Out mempty mempty

newtype Parser a = Parser (ExceptT Err (StateT St (Writer Out)) a)
    deriving (Functor, Applicative, MonadPlus, Monad, MonadError Err, MonadState St, MonadWriter Out)

instance Alternative Parser where
    empty = Parser (throwError mempty)
    (<|>) ma mb = do
        st@(St n _ _) <- get
        catchError ma $ \e -> do
            m <- gets stCount
            if m > n then throwError e else put st *> catchError mb (throwError . (e <>))

runParser' :: Parser a -> [TokenTree] -> (Either (SrcPos, String) a, [Message])
runParser' ma = runParser ma (ice "read SrcPos in parser state at top level")

runParser :: Parser a -> SrcPos -> [TokenTree] -> (Either (SrcPos, String) a, [Message])
runParser (Parser ma) surroundingPos tts =
    let initSt = St 0 surroundingPos tts
        formatExpecteds es = case Set.toList es of
            [] -> ice "empty list of expecteds in formatExpecteds"
            [e] -> "Expected " ++ e
            es' -> "Expected one of: " ++ intercalate ", " es'
    in  bimap
            liftEither
            (view messages)
            (runWriter
                (evalStateT
                    (runExceptT (withExceptT (\(Err _ pos es) -> (pos, formatExpecteds es)) ma))
                    initSt
                )
            )

token :: String -> (SrcPos -> TokenTree' -> Maybe a) -> Parser a
token exp f = do
    St n outerPos xs <- get
    case xs of
        WithPos innerPos x : xs' -> do
            a <- mexcept (Err n innerPos (Set.singleton exp)) (f innerPos x)
            modify (\st -> st { stCount = n + 1, stInput = xs' })
            pure a
        [] -> throwError $ Err n outerPos (Set.singleton "continuation of token sequence")

-- | Succeeds only when current input sequence (may be nested in sexpr) is empty
end :: Parser ()
end = get >>= \(St n _ inp) -> case inp of
    [] -> pure ()
    WithPos p _ : _ -> throwError (Err n p (Set.singleton "end of (nested) token sequence"))

mexcept :: MonadError e m => e -> Maybe a -> m a
mexcept e = maybe (throwError e) pure

lookAhead :: Parser a -> Parser a
lookAhead pa = get >>= \s -> pa >>= \a -> put s $> a

try :: Parser a -> Parser a
try ma = do
    s <- get
    catchError ma $ \e -> do
        put s
        throwError e

getSrcPos :: Parser SrcPos
getSrcPos = lookAhead (token "token" (Just .* const))

anyToken :: Parser TokenTree
anyToken = token "any token" (Just .* WithPos)

withPos :: Parser a -> Parser (WithPos a)
withPos = liftA2 WithPos getSrcPos

parens :: Parser a -> Parser a
parens ma = parens' (const ma)

parens' :: (SrcPos -> Parser a) -> Parser a
parens' = sexpr "`(`" $ \case
    Parens tts -> Just tts
    _ -> Nothing

tryParens :: Parser a -> Parser a
tryParens ma = tryParens' (const ma)

tryParens' :: (SrcPos -> Parser a) -> Parser a
tryParens' = trySexpr "`(`" $ \case
    Parens tts -> Just tts
    _ -> Nothing

brackets :: Parser a -> Parser a
brackets ma = brackets' (const ma)

brackets' :: (SrcPos -> Parser a) -> Parser a
brackets' = sexpr "`[`" $ \case
    Brackets tts -> Just tts
    _ -> Nothing

sexpr :: String -> (TokenTree' -> Maybe [TokenTree]) -> (SrcPos -> Parser a) -> Parser a
sexpr expected extract f = do
    (p, tts) <- token expected $ \p' -> fmap (p', ) . extract
    St _ pOld ttsOld <- get
    modify (\st -> st { stOuterPos = p, stInput = tts })
    a <- f p
    end
    modify (\st -> st { stOuterPos = pOld, stInput = ttsOld })
    pure a

trySexpr :: String -> (TokenTree' -> Maybe [TokenTree]) -> (SrcPos -> Parser a) -> Parser a
trySexpr expected extract f = do
    stOldest <- get
    (p, tts) <- token expected $ \p' -> fmap (p', ) . extract
    St cOld pOld ttsOld <- get
    modify (\st -> st { stOuterPos = p, stInput = tts })
    a <- catchError (f p <* end) $ \e -> do
        cNew <- gets stCount
        when (cOld == cNew) (put stOldest)
        throwError e
    modify (\st -> st { stOuterPos = pOld, stInput = ttsOld })
    pure a

big :: Parser (Id 'Front.Parsed.Big)
big = token "big identifier" $ \p -> \case
    Front.Lexd.Big x -> Just (Id (WithPos p x))
    _ -> Nothing

small' :: Parser String
small' = fmap idstr small

small :: Parser (Id 'Front.Parsed.Small)
small = token "small identifier" $ \p -> \case
    Front.Lexd.Small x -> Just (Id (WithPos p x))
    _ -> Nothing

reserved :: Reserved -> Parser ()
reserved k = token (pretty k) $ const $ \case
    Reserved k' | k == k' -> Just ()
    _ -> Nothing

keyword :: String -> Parser ()
keyword k = token k $ const $ \case
    Keyword k' | k == k' -> Just ()
    _ -> Nothing
