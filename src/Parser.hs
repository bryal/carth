{-# LANGUAGE DataKinds #-}

module Parser where

import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Functor
import Data.List
import Data.Set (Set)
import qualified Data.Set as Set

import Misc
import SrcPos
import Lexd
import Parsed
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

newtype Parser a = Parser (StateT St (Except Err) a)
    deriving (Functor, Applicative, MonadPlus, Monad, MonadError Err, MonadState St)

instance Alternative Parser where
    empty = Parser (throwError mempty)
    (<|>) ma mb = do
        n <- gets stCount
        catchError ma $ \e -> if errLength e > n
            then throwError e
            else catchError mb (throwError . (e <>))

runParser' :: Parser a -> [TokenTree] -> Except (SrcPos, String) a
runParser' ma = runParser ma (ice "read SrcPos in parser state at top level")

runParser :: Parser a -> SrcPos -> [TokenTree] -> Except (SrcPos, String) a
runParser (Parser ma) surroundingPos tts =
    let initSt = St 0 surroundingPos tts
        formatExpecteds es = case Set.toList es of
            [] -> ice "empty list of expecteds in formatExpecteds"
            [e] -> "Expected " ++ e
            es' -> "Expected one of: " ++ intercalate ", " es'
    in  withExcept (\(Err _ pos es) -> (pos, formatExpecteds es)) (evalStateT ma initSt)

token :: String -> (SrcPos -> TokenTree' -> Maybe a) -> Parser a
token exp f = do
    St n outerPos xs <- get
    case xs of
        WithPos innerPos x : xs' -> do
            a <- mexcept (Err n innerPos (Set.singleton exp)) (f innerPos x)
            modify (\st -> st { stCount = n + 1, stInput = xs' })
            pure a
        [] -> throwError
            $ Err n outerPos (Set.singleton "continuation of token sequence")

-- | Succeeds only when current input sequence (may be nested in sexpr) is empty
end :: Parser ()
end = get >>= \(St n _ inp) -> case inp of
    [] -> pure ()
    WithPos p _ : _ ->
        throwError (Err n p (Set.singleton "end of (nested) token sequence"))

mexcept :: MonadError e m => e -> Maybe a -> m a
mexcept e = maybe (throwError e) pure

lookAhead :: Parser a -> Parser a
lookAhead pa = get >>= \s -> pa >>= \a -> put s $> a

try :: Parser a -> Parser a
try ma = do
    s <- get
    catchError ma $ \e -> do
        put s
        throwError (e { errLength = stCount s })

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

big :: Parser (Id 'Parsed.Big)
big = token "big identifier" $ \p -> \case
    Lexd.Big x -> Just (Id (WithPos p x))
    _ -> Nothing

small' :: Parser String
small' = fmap idstr small

small :: Parser (Id 'Parsed.Small)
small = token "small identifier" $ \p -> \case
    Lexd.Small x -> Just (Id (WithPos p x))
    _ -> Nothing

reserved :: Keyword -> Parser ()
reserved k = token ("keyword " ++ pretty k) $ const $ \case
    Keyword k' | k == k' -> Just ()
    _ -> Nothing
