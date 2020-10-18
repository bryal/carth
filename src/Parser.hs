{-# LANGUAGE FlexibleContexts, LambdaCase, TupleSections, DataKinds
           , GeneralizedNewtypeDeriving #-}

module Parser (Parser, St (..), runParser, token, end, lookAhead, try, getSrcPos) where

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

data Err = Err { errLength :: Word, errPos :: SrcPos, errExpecteds :: Set String }
    deriving (Show, Eq)

-- TODO: Semigroup instance for the error type should select the one with the longest
--       match. We need to keep track of how long the match is.
--
--       If two matches are of the same / no length, combine the sets of "expected"s of
--       both. So it's like "expected keyword extern or keyword data".
instance Semigroup Err where
    (<>) e1 e2
        | e2 == mempty = e1
        | errLength e1 > errLength e2 = e1
        | errLength e1 < errLength e2 = e2
        | otherwise = Err (errLength e2)
                          (errPos e2)
                          (Set.union (errExpecteds e1) (errExpecteds e2))

instance Monoid Err where
    mempty = Err 0 (SrcPos "<dummy>" 0 0) Set.empty

data St = St { stCount :: Word, stOuterPos :: SrcPos, stInput :: [TokenTree] }

newtype Parser a = Parser (StateT St (Except Err) a)
    deriving (Functor, Applicative, MonadPlus, Monad, MonadError Err, MonadState St)

instance Alternative Parser where
    empty = Parser (throwError mempty)
    (<|>) ma mb = do
        n <- gets stCount
        catchError ma $ \e -> if errLength e > n
            then throwError e
            else catchError mb (throwError . (e <>))

runParser :: Parser a -> [TokenTree] -> Except (SrcPos, String) a
runParser (Parser ma) tts =
    let noPos = ice "read SrcPos in parser state at top level"
        initSt = St 0 noPos tts
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
