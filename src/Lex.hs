{-# LANGUAGE FlexibleContexts, LambdaCase, TupleSections, DataKinds #-}

-- Note: Some parsers are greedy wrt consuming spaces and comments succeding the
--       item, while others are lazy. You'll have to look at the impl to be
--       sure.
--
--       If a parser has a variant with a "ns_" prefix, that variant does not
--       consume succeding space, while the unprefixed variant does.

module Lex (lex, toplevel, tokentree) where

import Control.Monad
import Control.Monad.Except
import Data.Char (isMark, isPunctuation, isSymbol)
import Data.Functor
import Data.Maybe
import Control.Applicative (liftA2)
import Text.Megaparsec hiding (parse, match)
import Text.Megaparsec.Char hiding (space, space1)
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Data.Set (Set)
import qualified Data.Set as Set
import System.FilePath
import System.Directory
import Data.Void
import Prelude hiding (lex)

import Misc
import SrcPos
import Lexd
import Literate
import EnvVars


type Lexer = Parsec Void String

type Import = String

data TopLevel = TImport Import -- | TMacro Macro
    | TTokenTree TokenTree


lex :: FilePath -> ExceptT String IO [TokenTree]
lex filepath = do
    modPaths <- lift modulePaths
    lexModules modPaths Set.empty [filepath]

lexModules :: [FilePath] -> Set String -> [String] -> ExceptT String IO [TokenTree]
lexModules modPaths visiteds = \case
    [] -> pure []
    f : nexts | Set.member f visiteds -> lexModules modPaths visiteds nexts
    f : nexts -> do
        s <- lift (readFile f)
            <&> \s' -> if takeExtension f == ".org" then untangleOrg s' else s'
        (imps, tts) <- liftEither $ parse' toplevels f s
        let ps = takeDirectory f : modPaths
        let resolve m = do
                let gs = [ p </> addExtension m e | p <- ps, e <- [".carth", ".org"] ]
                gs' <- filterM (lift . doesFileExist) gs
                case listToMaybe gs' of
                    Nothing ->
                        throwError
                            $ ("Error: No file for module " ++ m ++ " exists.\n")
                            ++ ("Searched paths: " ++ show ps)
                    Just g' -> pure g'
        impFs <- mapM resolve imps
        ttsNexts <- lexModules modPaths (Set.insert f visiteds) (impFs ++ nexts)
        pure (tts ++ ttsNexts)

toplevels :: Lexer ([Import], [TokenTree])
toplevels = do
    space
    tops <- many toplevel
    eof
    pure $ foldr
        (\top (is, tts) -> case top of
            TImport i -> (i : is, tts)
            TTokenTree tt -> (is, tt : tts)
        )
        ([], [])
        tops

toplevel :: Lexer TopLevel
toplevel = getSrcPos >>= \p -> parens
    (fmap TImport import' <|> fmap (TTokenTree . WithPos p . Parens) (many tokentree))
    where import' = keyword' "import" *> small

tokentree :: Lexer TokenTree
tokentree = withPos tokentree'
  where
    tokentree' = choice
        [ fmap Small smallSpecial
        , fmap Big bigSpecial
        , fmap Keyword (try keyword)
        , fmap Small smallNormal
        , fmap Big bigNormal
        , fmap Lit lit
        , fmap Parens (parens (many tokentree))
        , fmap Brackets (brackets (many tokentree))
        , fmap Braces (braces (many tokentree))
        ]
    lit = try num <|> fmap Str strlit
    num = andSkipSpaceAfter ns_num
    ns_num = do
        neg <- option False (char '-' $> True)
        a <- eitherP (try (ns_nat <* notFollowedBy (char '.'))) Lexer.float
        pure $ either ((\n -> Int (if neg then -n else n)) . fromIntegral)
                      (\x -> F64 (if neg then -x else x))
                      a
    ns_nat :: Lexer Word
    ns_nat = choice
        [string "0b" *> Lexer.binary, string "0x" *> Lexer.hexadecimal, Lexer.decimal]

strlit :: Lexer String
strlit = andSkipSpaceAfter ns_strlit
    where ns_strlit = char '"' >> manyTill Lexer.charLiteral (char '"')

keyword :: Lexer Keyword
keyword = andSkipSpaceAfter $ choice $ (++)
    (map
        (\p -> try (p <* notFollowedBy identLetter))
        [ string ":" $> Kcolon
        , string "." $> Kdot
        , string "Fun" $> KFun
        , string "Box" $> KBox
        , string "define" $> Kdefine
        , string "define:" $> KdefineColon
        , string "extern" $> Kextern
        , string "forall" $> Kforall
        , string "fmatch" $> Kfmatch
        , string "match" $> Kmatch
        , string "if" $> Kif
        , string "fun" $> Kfun
        , string "let1" $> Klet1
        , string "let" $> Klet
        , string "letrec" $> Kletrec
        , string "data" $> Kdata
        , string "sizeof" $> Ksizeof
        , string "import" $> Kimport
        , string "case" $> Kcase
        , string "defmacro" $> Kdefmacro
        ]
    )
    [string "id@" $> KidAt, string "Id@" $> KIdAt]

keyword' :: String -> Lexer ()
keyword' x = andSkipSpaceAfter $ label ("keyword " ++ x) (string x) $> ()

small, smallSpecial, smallNormal :: Lexer String
small = smallSpecial <|> smallNormal
smallSpecial = keyword' "id@" *> strlit
smallNormal = andSkipSpaceAfter $ liftA2 (:) smallStart identRest
  where
    smallStart = lowerChar <|> otherChar <|> try (oneOf "-+" <* notFollowedBy digitChar)

bigSpecial, bigNormal :: Lexer String
bigSpecial = keyword' "id@" *> strlit
bigNormal = andSkipSpaceAfter $ liftA2 (:) bigStart identRest
    where bigStart = upperChar <|> char ':'

identRest :: Lexer String
identRest = many identLetter

identLetter :: Lexer Char
identLetter = letterChar <|> otherChar <|> oneOf "-+:" <|> digitChar

otherChar :: Lexer Char
otherChar = satisfy
    (\c -> and
        [ any ($ c) [isMark, isPunctuation, isSymbol]
        , not (elem c "()[]{}")
        , not (elem c "\"-+:")
        ]
    )

parens, ns_parens :: Lexer a -> Lexer a
parens = andSkipSpaceAfter . ns_parens
ns_parens = between (symbol "(") (string ")")

brackets, ns_brackets :: Lexer a -> Lexer a
brackets = andSkipSpaceAfter . ns_brackets
ns_brackets = between (symbol "[") (string "]")

braces, ns_braces :: Lexer a -> Lexer a
braces = andSkipSpaceAfter . ns_braces
ns_braces = between (symbol "{") (string "}")

andSkipSpaceAfter :: Lexer a -> Lexer a
andSkipSpaceAfter = Lexer.lexeme space

symbol :: String -> Lexer String
symbol = Lexer.symbol space

-- | Spaces, line comments, and block comments
space :: Lexer ()
space = Lexer.space Char.space1 (Lexer.skipLineComment ";") empty

withPos :: Lexer a -> Lexer (WithPos a)
withPos = liftA2 WithPos getSrcPos

getSrcPos :: Lexer SrcPos
getSrcPos = fmap
    (\(SourcePos f l c) -> SrcPos f (fromIntegral (unPos l)) (fromIntegral (unPos c)))
    getSourcePos
