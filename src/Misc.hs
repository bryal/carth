{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, LambdaCase, RankNTypes #-}

module Misc where

import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Bifunctor
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Lens.Micro.Platform (Lens, Lens', over, set, use, modifying)
import Data.Bitraversable
import System.Exit
import qualified Text.Megaparsec as Mega
import Text.Megaparsec hiding (parse, match)
import Text.Megaparsec.Char hiding (space, space1)
import Data.Void


newtype TopologicalOrder a = Topo [a]
    deriving Show

type Source = String


ice :: String -> a
ice = error . ("Internal Compiler Error: " ++)

nyi :: String -> a
nyi = error . ("Not yet implemented: " ++)

-- | Like `intercalate`, but concatenate a list with a prefix before each
--   element, instead of an separator between each pair of elements.
precalate :: [a] -> [[a]] -> [a]
precalate prefix = \case
    [] -> []
    xs -> prefix ++ intercalate prefix xs

indent :: Int -> String
indent = flip replicate ' '

both :: (a -> b) -> (a, a) -> (b, b)
both f (a0, a1) = (f a0, f a1)

firstM :: (Bitraversable t, Applicative f) => (a -> f a') -> t a b -> f (t a' b)
firstM = flip bimapM pure

secondM :: (Bitraversable t, Applicative f) => (b -> f b') -> t a b -> f (t a b')
secondM = bimapM pure

locallySet :: MonadReader s m => Lens' s a -> a -> m r -> m r
locallySet l = locally l . const

locally :: MonadReader s m => Lens' s a -> (a -> a) -> m r -> m r
locally l f = local (over l f)

augment1 :: (MonadReader e m, Ord k) => Lens' e (Map k v) -> (k, v) -> m a -> m a
augment1 l = locally l . uncurry Map.insert

augment :: (MonadReader s m, Monoid a) => Lens' s a -> a -> m x -> m x
augment l = locally l . mappend

scribe :: (MonadWriter t m, Monoid s) => Lens s t a b -> b -> m ()
scribe l b = tell (set l b mempty)

(<<+=) :: (MonadState s m, Num a) => Lens' s a -> a -> m a
(<<+=) l n = use l <* modifying l (+ n)

(.*) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.*) = (.) . (.)
infixr 8 .*

(.**) :: (d -> e) -> (a -> b -> c -> d) -> a -> b -> c -> e
(.**) = (.) . (.*)
infixr 8 .**

abort :: FilePath -> IO a
abort f = do
    putStrLn "Error: Aborting due to previous error."
    putStrLn $ "Error: Could not compile " ++ f ++ "."
    exitFailure

splitOn :: String -> String -> [String]
splitOn sep = fromMaybe [] . Mega.parseMaybe splitOn'
  where
    splitOn' :: Parsec Void String [String]
    splitOn' = do
        as <- many (try (manyTill anySingle (try (string sep))))
        a <- many anySingle
        pure $ (as ++) $ if not (null a) then [a] else []

parse' :: Parsec Void String a -> FilePath -> Source -> Either String a
parse' p name src = first errorBundlePretty (Mega.parse p name src)

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith f = foldr
    (\x (bs, cs) -> case f x of
        Left b -> (b : bs, cs)
        Right c -> (bs, c : cs)
    )
    ([], [])

rightToMaybe :: Either a b -> Maybe b
rightToMaybe = either (const Nothing) Just

unsnoc :: [a] -> Maybe ([a], a)
unsnoc = \case
    [] -> Nothing
    x : xs -> case unsnoc xs of
        Just (ys, y) -> Just (x : ys, y)
        Nothing -> Just ([], x)

is2tup :: [a] -> Maybe (a, a)
is2tup = \case
    a1 : [a2] -> Just (a1, a2)
    _ -> Nothing

is3tup :: [a] -> Maybe (a, a, a)
is3tup = \case
    a1 : a2 : [a3] -> Just (a1, a2, a3)
    _ -> Nothing
