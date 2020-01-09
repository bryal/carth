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
    , reserveds
    , ns_scheme
    , ns_pat
    , ns_small'
    , eConstructor
    , ns_expr
    , ns_big
    , ns_parens
    , def
    , getSrcPos
    )
where

import Control.Monad
import Data.Char (isMark, isPunctuation, isSymbol, isUpper)
import Data.Functor
import Control.Applicative (liftA2)
import qualified Text.Megaparsec as Mega
import Text.Megaparsec hiding (parse, match)
import Text.Megaparsec.Char hiding (space, space1)
import qualified Text.Megaparsec.Char as Char
import qualified Text.Megaparsec.Char.Lexer as Lexer
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Either.Combinators
import Data.Void
import Data.Composition
import Data.List
import System.FilePath
import System.Directory
import qualified Data.List.NonEmpty as NonEmpty

import Misc hiding (if')
import SrcPos
import Ast
import Literate
import CompiletimeVars

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
    (src, f) <- parseModule' dir >>= \case
        Just x -> pure x
        Nothing -> parseModule' modDir >>= \case
            Just x -> pure x
            Nothing -> do
                putStrLn ("Error: No file for module " ++ m ++ " exists.")
                abort filepath
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
    parseModule' dir' = do
        let m' = dir' </> m
            carthf = addExtension m' ".carth"
            orgf = addExtension m' ".org"
        dotCarth <- doesFileExist carthf
        dotOrg <- doesFileExist orgf
        case (dotCarth, dotOrg) of
            (True, True) -> do
                putStrLn
                    $ ("Error: File of module " ++ m)
                    ++ " is ambiguous. Both .org and .carth exist."
                abort filepath
            (True, False) -> fmap (Just . (, carthf)) (readFile carthf)
            (False, True) -> do
                s <- readFile orgf
                let s' = untangleOrg s
                writeFile (addExtension m "untangled") s
                pure (Just (s', orgf))
            (False, False) -> pure Nothing

parse' :: Parser a -> FilePath -> Source -> Either String a
parse' p name src = mapLeft errorBundlePretty (Mega.parse p name src)

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
expr = andSkipSpaceAfter ns_expr

ns_expr :: Parser Expr
ns_expr = withPos $ choice [unit, str, ebool, var, num, eConstructor, pexpr]
  where
    unit = ns_reserved "unit" $> Lit Unit
    num = do
        neg <- option False (char '-' $> True)
        a <- eitherP
            (try (Lexer.decimal <* notFollowedBy (char '.')))
            Lexer.float
        let e = either
                (\n -> Int (if neg then -n else n))
                (\x -> Double (if neg then -x else x))
                a
        pure (Lit e)
    str = fmap (Lit . Str) $ char '"' >> manyTill
        Lexer.charLiteral
        (char '"')
    ebool = fmap (Lit . Bool) bool
    pexpr =
        ns_parens $ choice
            [funMatch, match, if', fun, let', typeAscr, box, deref, app]

bool :: Parser Bool
bool = (ns_reserved "true" $> True) <|> (ns_reserved "false" $> False)

int :: Parser Int
int = Lexer.signed empty Lexer.decimal

eConstructor :: Parser Expr'
eConstructor = fmap Ctor ns_big'

var :: Parser Expr'
var = fmap Var ns_small'

funMatch :: Parser Expr'
funMatch = reserved "fun-match" *> fmap FunMatch cases

match :: Parser Expr'
match = do
    reserved "match"
    e <- expr
    cs <- cases
    pure (Match e cs)

cases :: Parser [(Pat, Expr)]
cases = many (parens (reserved "case" *> (liftA2 (,) pat expr)))

pat :: Parser Pat
pat = andSkipSpaceAfter ns_pat

ns_pat :: Parser Pat
ns_pat = choice [patInt, patBool, patCtor, patVar, ppat]
  where
    patInt = liftA2 PInt getSrcPos int
    patBool = liftA2 PBool getSrcPos bool
    patCtor = fmap (\x -> PConstruction (getPos x) x []) ns_big'
    patVar = fmap PVar ns_small'
    ppat = do
        pos <- getSrcPos
        ns_parens (choice [patBox pos, patCtion pos])
    patBox pos = reserved "Box" *> fmap (PBox pos) pat
    patCtion pos = liftM3 PConstruction (pure pos) big' (some pat)

app :: Parser Expr'
app = do
    rator <- expr
    rands <- some expr
    pure (unpos (foldl' (WithPos (getPos rator) .* App) rator rands))

if' :: Parser Expr'
if' = do
    reserved "if"
    pred' <- expr
    conseq <- expr
    alt <- expr
    pure (If pred' conseq alt)

fun :: Parser Expr'
fun = do
    reserved "fun"
    params <- choice [parens (some pat), fmap (pure . PVar) small']
    body <- expr
    pure $ unpos (foldr (\p b -> WithPos (getPos p) (Fun p b)) body params)

let' :: Parser Expr'
let' = do
    reserved "let"
    bindings <- parens (many binding)
    body <- expr
    pure (Let bindings body)

binding :: Parser Def
binding = parens (bindingTyped <|> bindingUntyped)
  where
    bindingTyped = reserved ":"
        *> liftA2 (,) small' (liftA2 (,) (fmap Just scheme) expr)
    bindingUntyped = liftA2 (,) small' (fmap (Nothing, ) expr)

typeAscr :: Parser Expr'
typeAscr = reserved ":" *> liftA2 TypeAscr expr type_

box :: Parser Expr'
box = reserved "box" *> fmap Box expr

deref :: Parser Expr'
deref = reserved "deref" *> fmap Deref expr

scheme :: Parser (WithPos Scheme)
scheme = andSkipSpaceAfter ns_scheme

ns_scheme :: Parser (WithPos Scheme)
ns_scheme =
    withPos $ wrap ns_nonptype <|> (ns_parens (universal <|> wrap ptype'))
  where
    wrap = fmap (Forall Set.empty)
    universal = reserved "forall" *> liftA2 Forall tvars type_
    tvars = parens (fmap Set.fromList (many tvar))

type_ :: Parser Type
type_ = nonptype <|> ptype

nonptype :: Parser Type
nonptype = andSkipSpaceAfter ns_nonptype

ns_nonptype :: Parser Type
ns_nonptype = choice
    [fmap TPrim ns_tprim, fmap TVar ns_tvar, fmap (TConst . (, [])) ns_big]

ptype :: Parser Type
ptype = parens ptype'

ptype' :: Parser Type
ptype' = tfun <|> tbox <|> tapp

tapp :: Parser Type
tapp = liftA2 (TConst .* (,)) big (some type_)

tfun :: Parser Type
tfun = do
    reserved "Fun"
    t <- type_
    ts <- some type_
    pure (foldr1 TFun (t : ts))

tbox :: Parser Type
tbox = reserved "Box" *> fmap TBox type_

ns_tprim :: Parser TPrim
ns_tprim = try $ do
    s <- ns_big
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

tvar :: Parser TVar
tvar = andSkipSpaceAfter ns_tvar

ns_tvar :: Parser TVar
ns_tvar = fmap TVExplicit ns_small'

parens :: Parser a -> Parser a
parens = andSkipSpaceAfter . ns_parens

ns_parens :: Parser a -> Parser a
ns_parens = between (symbol "(") (string ")")

big' :: Parser (Id 'Big)
big' = andSkipSpaceAfter ns_big'

ns_big' :: Parser (Id 'Big)
ns_big' = fmap Id (withPos ns_big)

big :: Parser String
big = andSkipSpaceAfter ns_big

ns_big :: Parser String
ns_big = try $ do
    s <- identifier
    let c = head s
    if (isUpper c || [c] == ":")
        then pure s
        else fail "Big identifier must start with an uppercase letter or colon."

small' :: Parser (Id 'Small)
small' = andSkipSpaceAfter ns_small'

ns_small' :: Parser (Id 'Small)
ns_small' = fmap Id $ withPos $ try $ do
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
ident = label "identifier" $ liftA2 (:) identStart (many identLetter)

identStart :: Parser Char
identStart =
    choice [letterChar, otherChar, try (oneOf "-+" <* notFollowedBy digitChar)]

identLetter :: Parser Char
identLetter = letterChar <|> otherChar <|> oneOf "-+" <|> digitChar

reserved :: String -> Parser ()
reserved = andSkipSpaceAfter . ns_reserved

ns_reserved :: String -> Parser ()
ns_reserved x = do
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
