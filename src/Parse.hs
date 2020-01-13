{-# LANGUAGE FlexibleContexts, LambdaCase, TupleSections, DataKinds #-}

-- Note: Some parsers are greedy wrt consuming spaces and comments succeding the
--       item, while others are lazy. You'll have to look at the impl to be
--       sure.
--
--       If a parser has a variant with a "ns_" prefix, that variant does not
--       consume succeding space, while the unprefixed variant does.

module Parse
    ( Parser
    , Source
    , parse
    , parse'
    , parseTokenTreeOrRest
    , toplevels
    )
where

import Control.Monad
import Data.Char (isMark, isPunctuation, isSymbol, isUpper)
import Data.Functor
import Data.Bifunctor
import Data.Maybe
import Control.Applicative (liftA2)
import qualified Text.Megaparsec as Mega
import Text.Megaparsec hiding (parse, match)
import Text.Megaparsec.Char hiding (space, space1)
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void
import Data.List
import System.FilePath
import System.Directory
import qualified Data.List.NonEmpty as NonEmpty

import Misc
import SrcPos
import Ast
import Literate
import EnvVars

type Parser = Parsec Void String
type Source = String
type Import = String


parse :: FilePath -> IO (Either String Program)
parse filepath = do
    let (dir, file) = splitFileName filepath
    let moduleName = dropExtension file
    r <- parseModule filepath dir moduleName Set.empty []
    pure (fmap (\(ds, ts, es) -> Program ds ts es) r)

parseModule
    :: FilePath
    -> FilePath
    -> String
    -> Set String
    -> [String]
    -> IO (Either String ([Def], [TypeDef], [Extern]))
parseModule filepath dir m visiteds nexts = do
    modPaths <- fmap (dir :) modulePaths
    (src, f) <- parseModule' modPaths
    let visiteds' = Set.insert m visiteds
    case parse' toplevels f src of
        Left e -> pure (Left e)
        Right (is, ds, ts, es) -> case is ++ nexts of
            [] -> pure (Right (ds, ts, es))
            next : nexts' -> do
                r <- parseModule filepath dir next visiteds' nexts'
                pure $ fmap
                    (\(ds', ts', es') -> (ds ++ ds', ts ++ ts', es ++ es'))
                    r
  where
    parseModule' modPaths = do
        let fs = do
                p <- modPaths
                let pm = p </> m
                fmap (addExtension pm) [".carth", ".org"]
        fs' <- filterM doesFileExist fs
        f <- case listToMaybe fs' of
            Nothing -> do
                putStrLn
                    $ ("Error: No file for module " ++ m)
                    ++ (" exists.\nSearched paths: " ++ show modPaths)
                abort filepath
            Just f' -> pure f'
        s <- readFile f
        s' <- if takeExtension f == ".org"
            then do
                let s' = untangleOrg s
                writeFile (addExtension m "untangled") s'
                pure s'
            else pure s
        pure (s', f)

parse' :: Parser a -> FilePath -> Source -> Either String a
parse' p name src = first errorBundlePretty (Mega.parse p name src)

-- | For use in module TypeErr to get the length of the tokentree to draw a
--   squiggly line under it.
parseTokenTreeOrRest :: Source -> Either String String
parseTokenTreeOrRest = parse' tokenTreeOrRest ""
  where
    tokenTreeOrRest =
        fmap fst (Mega.match (try ns_tokenTree <|> (restOfInput $> ())))
    ns_tokenTree = choice
        [ ns_strlit $> ()
        , ns_ident $> ()
        , ns_num $> ()
        , ns_parens (many tokenTree) $> ()
        ]
    tokenTree = andSkipSpaceAfter ns_tokenTree
    restOfInput = many Mega.anySingle

toplevels :: Parser ([Import], [Def], [TypeDef], [Extern])
toplevels = do
    space
    r <- option ([], [], [], []) (toplevel >>= flip fmap toplevels)
    eof
    pure r
  where
    toplevel = do
        topPos <- getSrcPos
        parens $ choice
            [ fmap (\i (is, ds, ts, es) -> (i : is, ds, ts, es)) import'
            , fmap
                (\d (is, ds, ts, es) -> (is, d : ds, ts, es))
                (def topPos)
            , fmap (\t (is, ds, ts, es) -> (is, ds, t : ts, es)) typedef
            , fmap (\e (is, ds, ts, es) -> (is, ds, ts, e : es)) extern
            ]

import' :: Parser Import
import' = reserved "import" *> fmap idstr small'

extern :: Parser Extern
extern = reserved "extern" *> liftA2 Extern small' type_

typedef :: Parser TypeDef
typedef = do
    _ <- reserved "type"
    let onlyName = fmap (, []) big'
    let nameAndSome = parens . liftA2 (,) big' . some
    (name, params) <- onlyName <|> nameAndSome small'
    constrs <- many (onlyName <|> nameAndSome type_)
    pure (TypeDef name params (ConstructorDefs constrs))

def :: SrcPos -> Parser Def
def topPos = defUntyped topPos <|> defTyped topPos

defUntyped :: SrcPos -> Parser Def
defUntyped = (reserved "define" *>) . def' (pure Nothing)

defTyped :: SrcPos -> Parser Def
defTyped = (reserved "define:" *>) . def' (fmap Just scheme)

def'
    :: Parser (Maybe (WithPos Scheme))
    -> SrcPos
    -> Parser (Id 'Small, (Maybe (WithPos Scheme), Expr))
def' schemeParser topPos = varDef <|> funDef
  where
    varDef = do
        name <- small'
        scm <- schemeParser
        body <- expr
        pure (name, (scm, body))
    funDef = do
        (name, params) <- parens (liftM2 (,) small' (some pat))
        scm <- schemeParser
        body <- expr
        let f = foldr (WithPos topPos .* Fun) body params
        pure (name, (scm, f))

expr :: Parser Expr
expr = withPos $ choice [unit, estr, ebool, var, num, eConstructor, pexpr]
  where
    unit = reserved "unit" $> Lit Unit
    estr = fmap (Lit . Str) strlit
    ebool = fmap (Lit . Bool) bool
    eConstructor = fmap Ctor big'
    var = fmap Var small'
    pexpr =
        parens $ choice
            [funMatch, match, if', fun, let', typeAscr, box, deref, app]
    funMatch = reserved "fun-match" *> fmap FunMatch cases
    match = reserved "match" *> liftA2 Match expr cases
    cases = many (parens (reserved "case" *> (liftA2 (,) pat expr)))
    if' = reserved "if" *> liftM3 If expr expr expr
    fun = do
        reserved "fun"
        params <- choice [parens (some pat), fmap (pure . PVar) small']
        body <- expr
        pure $ unpos
            (foldr (\p b -> WithPos (getPos p) (Fun p b)) body params)
    let' = reserved "let" *> liftA2 Let (parens (many binding)) expr
    binding = parens (bindingTyped <|> bindingUntyped)
    bindingTyped = reserved ":"
        *> liftA2 (,) small' (liftA2 (,) (fmap Just scheme) expr)
    bindingUntyped = liftA2 (,) small' (fmap (Nothing, ) expr)
    typeAscr = reserved ":" *> liftA2 TypeAscr expr type_
    box = reserved "box" *> fmap Box expr
    deref = reserved "deref" *> fmap Deref expr
    app = do
        rator <- expr
        rands <- some expr
        pure (unpos (foldl' (WithPos (getPos rator) .* App) rator rands))

num :: Parser Expr'
num = andSkipSpaceAfter ns_num

ns_num :: Parser Expr'
ns_num = do
    neg <- option False (char '-' $> True)
    a <- eitherP (try (Lexer.decimal <* notFollowedBy (char '.'))) Lexer.float
    let e = either
            (\n -> Int (if neg then -n else n))
            (\x -> Double (if neg then -x else x))
            a
    pure (Lit e)

bool :: Parser Bool
bool = (reserved "true" $> True) <|> (reserved "false" $> False)

strlit :: Parser String
strlit = andSkipSpaceAfter ns_strlit

ns_strlit :: Parser String
ns_strlit = char '"' >> manyTill Lexer.charLiteral (char '"')

pat :: Parser Pat
pat = choice [patInt, patBool, patStr, patCtor, patVar, ppat]
  where
    patInt = liftA2 PInt getSrcPos int
    int = andSkipSpaceAfter (Lexer.signed empty Lexer.decimal)
    patBool = liftA2 PBool getSrcPos bool
    patStr = liftA2 PStr getSrcPos strlit
    patCtor = fmap (\x -> PConstruction (getPos x) x []) big'
    patVar = fmap PVar small'
    ppat = do
        pos <- getSrcPos
        parens (choice [patBox pos, patCtion pos])
    patBox pos = reserved "Box" *> fmap (PBox pos) pat
    patCtion pos = liftM3 PConstruction (pure pos) big' (some pat)

scheme :: Parser (WithPos Scheme)
scheme = withPos $ wrap nonptype <|> (parens (universal <|> wrap ptype))
  where
    wrap = fmap (Forall Set.empty)
    universal = reserved "forall" *> liftA2 Forall tvars type_
    tvars = parens (fmap Set.fromList (many tvar))

type_ :: Parser Type
type_ = nonptype <|> parens ptype

nonptype :: Parser Type
nonptype = choice
    [fmap TPrim tprim, fmap TVar tvar, fmap (TConst . (, [])) big]
  where
    tprim = try $ do
        s <- big
        case s of
            "Unit" -> pure TUnit
            "Nat8" -> pure TNat8
            "Nat16" -> pure TNat16
            "Nat32" -> pure TNat32
            "Nat" -> pure TNat
            "Int8" -> pure TInt8
            "Int16" -> pure TInt16
            "Int32" -> pure TInt32
            "Int" -> pure TInt
            "Double" -> pure TDouble
            "Bool" -> pure TBool
            _ -> fail $ "Undefined type constant " ++ s

ptype :: Parser Type
ptype = choice [tfun, tbox, tapp]
  where
    tfun = do
        reserved "Fun"
        t <- type_
        ts <- some type_
        pure (foldr1 TFun (t : ts))
    tbox = reserved "Box" *> fmap TBox type_
    tapp = liftA2 (TConst .* (,)) big (some type_)

tvar :: Parser TVar
tvar = fmap TVExplicit small'

parens :: Parser a -> Parser a
parens = andSkipSpaceAfter . ns_parens

ns_parens :: Parser a -> Parser a
ns_parens = between (symbol "(") (string ")")

big' :: Parser (Id 'Big)
big' = fmap Id (withPos big)

big :: Parser String
big = try $ do
    s <- identifier
    let c = head s
    if (isUpper c || [c] == ":")
        then pure s
        else fail "Big identifier must start with an uppercase letter or colon."

small' :: Parser (Id 'Small)
small' = fmap Id $ withPos $ try $ do
    s <- identifier
    let c = head s
    if (isUpper c || [c] == ":")
        then
            fail
                "Small identifier must not start with an uppercase letter or colon."
        else pure s

identifier :: Parser String
identifier = do
    name <- ident
    if elem name reserveds
        then unexpected
            (Label (NonEmpty.fromList ("reserved word " ++ show name)))
        else pure name

ident :: Parser String
ident = andSkipSpaceAfter ns_ident

ns_ident :: Parser String
ns_ident = label "identifier" $ liftA2 (:) identStart (many identLetter)
  where
    identStart =
        choice
            [ letterChar
            , otherChar
            , try (oneOf "-+" <* notFollowedBy digitChar)
            ]
    identLetter = letterChar <|> otherChar <|> oneOf "-+" <|> digitChar

reserved :: String -> Parser ()
reserved x = do
    if not (elem x reserveds)
        then ice ("`" ++ x ++ "` is not a reserved word")
        else label ("reserved word " ++ x) (try (mfilter (== x) ident)) $> ()

andSkipSpaceAfter :: Parser a -> Parser a
andSkipSpaceAfter = Lexer.lexeme space

symbol :: String -> Parser String
symbol = Lexer.symbol space

reserveds :: [String]
reserveds =
    [ ":"
    , "Fun"
    , "Box"
    , "define"
    , "define:"
    , "extern"
    , "forall"
    , "unit"
    , "true"
    , "false"
    , "fun-match"
    , "match"
    , "if"
    , "fun"
    , "let"
    , "type"
    , "box"
    , "deref"
    , "import"
    , "case"
    ]

otherChar :: Parser Char
otherChar = satisfy
    (\c -> and
        [ any ($ c) [isMark, isPunctuation, isSymbol]
        , not (elem c "()[]{}")
        , not (elem c "\"-+")
        ]
    )

-- | Spaces, line comments, and block comments
space :: Parser ()
space = Lexer.space Char.space1 (Lexer.skipLineComment ";") empty

withPos :: Parser a -> Parser (WithPos a)
withPos = liftA2 WithPos getSrcPos

getSrcPos :: Parser SrcPos
getSrcPos = fmap SrcPos getSourcePos
