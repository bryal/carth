{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, LambdaCase, RankNTypes #-}

module Misc
    ( ice
    , nyi
    , precalate
    , prettyPrint
    , pretty
    , Pretty(..)
    , indent
    , both
    , secondM
    , locally
    , augment
    , scribe
    , (<<+=)
    , abort
    , splitOn
    , (.*)
    , (.**)
    )
where

import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import Lens.Micro.Platform (Lens, Lens', over, set, use, modifying)
import Data.Bitraversable
import System.Exit
import LLVM.AST.Type (Type)
import LLVM.AST (Name, Module)
import LLVM.Pretty ()
import qualified Data.Text.Prettyprint.Doc as Prettyprint
import qualified Text.Megaparsec as Mega
import Text.Megaparsec hiding (parse, match)
import Text.Megaparsec.Char hiding (space, space1)
import Data.Void

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

-- Pretty printing
prettyPrint :: Pretty a => a -> IO ()
prettyPrint = putStrLn . pretty

pretty :: Pretty a => a -> String
pretty = pretty' 0

-- Pretty print starting at some indentation depth
class Pretty a where
    pretty' :: Int -> a -> String

instance Pretty String where
    pretty' _ = id

instance Pretty Type where
    pretty' _ = show . Prettyprint.pretty
instance Pretty Name where
    pretty' _ = show . Prettyprint.pretty
instance Pretty Module where
    pretty' _ = show . Prettyprint.pretty

indent :: Int -> String
indent = flip replicate ' '

both :: (a -> b) -> (a, a) -> (b, b)
both f (a0, a1) = (f a0, f a1)

secondM
    :: (Bitraversable t, Applicative f) => (b -> f b') -> t a b -> f (t a b')
secondM = bimapM pure

locally :: MonadReader s m => Lens' s a -> (a -> a) -> m r -> m r
locally l f = local (over l f)

augment
    :: (MonadReader e m, Ord k) => Lens' e (Map k v) -> Map k v -> m a -> m a
augment l = locally l . Map.union

scribe :: (MonadWriter t m, Monoid s) => Lens s t a b -> b -> m ()
scribe l b = tell (set l b mempty)

(<<+=) :: (MonadState s m, Num a) => Lens' s a -> a -> m a
(<<+=) l n = use l <* modifying l (+ n)

(.*) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.*) = (.) . (.)

(.**) :: (d -> e) -> (a -> b -> c -> d) -> a -> b -> c -> e
(.**) = (.) . (.*)

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
