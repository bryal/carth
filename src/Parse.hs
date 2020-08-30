{-# LANGUAGE FlexibleContexts, LambdaCase, TupleSections, DataKinds #-}

-- Note: Some parsers are greedy wrt consuming spaces and comments succeding the
--       item, while others are lazy. You'll have to look at the impl to be
--       sure.
--
--       If a parser has a variant with a "ns_" prefix, that variant does not
--       consume succeding space, while the unprefixed variant does.

module Parse (Parser, Source, parse, parse', parseTokenTreeOrRest, toplevels) where

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
import Parsed
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
parseModule filepath dir m visiteds nexts =
    let readModuleIn modPaths = do
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

        advance (is, ds, ts, es) = case (is ++ nexts) of
            [] -> pure (Right (ds, ts, es))
            next : nexts' -> fmap
                (fmap (\(ds', ts', es') -> (ds ++ ds', ts ++ ts', es ++ es')))
                (parseModule filepath dir next (Set.insert m visiteds) nexts')
    in  if Set.member m visiteds
            then advance ([], [], [], [])
            else do
             -- TODO: make dir absolute to make debug work when binary is moved?
                modPaths <- fmap (dir :) modulePaths
                (src, f) <- readModuleIn modPaths
                case parse' toplevels f src of
                    Left e -> pure (Left e)
                    Right r -> advance r

parse' :: Parser a -> FilePath -> Source -> Either String a
parse' p name src = first errorBundlePretty (Mega.parse p name src)

-- | For use in module TypeErr to get the length of the tokentree to draw a
--   squiggly line under it.
parseTokenTreeOrRest :: Source -> Either String String
parseTokenTreeOrRest = parse' tokenTreeOrRest ""
  where
    tokenTreeOrRest = fmap fst (Mega.match (try ns_tokenTree <|> (restOfInput $> ())))
    ns_tokenTree = choice
        [ns_strlit $> (), ns_ident $> (), ns_num $> (), ns_parens (many tokenTree) $> ()]
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
            , fmap (\d (is, ds, ts, es) -> (is, d : ds, ts, es)) (def topPos)
            , fmap (\t (is, ds, ts, es) -> (is, ds, t : ts, es)) typedef
            , fmap (\e (is, ds, ts, es) -> (is, ds, ts, e : es)) extern
            ]

import' :: Parser Import
import' = reserved "import" *> fmap idstr small

extern :: Parser Extern
extern = reserved "extern" *> liftA2 Extern small type_

typedef :: Parser TypeDef
typedef = do
    _ <- reserved "data"
    let onlyName = fmap (, []) big
    let nameAndSome = parens . liftA2 (,) big . some
    (name, params) <- onlyName <|> nameAndSome small
    constrs <- many (onlyName <|> nameAndSome type_)
    pure (TypeDef name params (ConstructorDefs constrs))

def :: SrcPos -> Parser Def
def topPos = defUntyped topPos <|> defTyped topPos

defUntyped :: SrcPos -> Parser Def
defUntyped pos = reserved "define" *> def' (pure Nothing) pos

defTyped :: SrcPos -> Parser Def
defTyped pos = reserved "define:" *> def' (fmap Just scheme) pos

def'
    :: Parser (Maybe Scheme)
    -> SrcPos
    -> Parser (Id 'Small, (WithPos (Maybe Scheme, Expr)))
def' schemeParser topPos = varDef <|> funDef
  where
    parenDef = try (getSrcPos >>= (parens . def))
    body = withPos $ do
        ds <- many parenDef
        if null ds then expr' else fmap (LetRec ds) expr
    varDef = do
        name <- small
        scm <- schemeParser
        b <- body
        pure (name, (WithPos topPos (scm, b)))
    funDef = do
        (name, params) <- parens (liftM2 (,) small (some pat))
        scm <- schemeParser
        b <- body
        let f = foldr (WithPos topPos . FunMatch . pure .* (,)) b params
        pure (name, (WithPos topPos (scm, f)))

expr :: Parser Expr
expr = withPos expr'

data BindingLhs
    = VarLhs (Id 'Small)
    | FunLhs (Id 'Small) [Pat]
    | CaseVarLhs Pat

expr' :: Parser Expr'
expr' = choice [var, estr, num, eConstructor, etuple, pexpr]
  where
    estr = fmap (Lit . Str) strlit
    eConstructor = fmap Ctor big
    -- FIXME: These positions are completely wack. Gotta get a separate variant in the AST
    --        for pairs. Similar to Box.
    etuple =
        fmap unpos
            $ tuple expr (\p -> WithPos p (Ctor (Id (WithPos p "Unit"))))
            $ \l r ->
                  let p = getPos l
                  in  WithPos
                          p
                          (App
                              (WithPos
                                  p
                                  (App (WithPos p (Ctor (Id (WithPos p "Cons")))) l)
                              )
                              r
                          )
    var = fmap Var small
    pexpr = getSrcPos >>= \p -> parens $ choice
        [funMatch, match, if', fun, let1 p, let', letrec, typeAscr, sizeof, app]
    funMatch = reserved "fmatch" *> fmap FunMatch cases
    match = reserved "match" *> liftA2 Match expr cases
    cases = many (parens (reserved "case" *> (liftA2 (,) pat expr)))
    if' = reserved "if" *> liftM3 If expr expr expr
    fun = do
        reserved "fun"
        params <- parens (some pat)
        body <- expr
        pure $ unpos $ foldr (\p b -> WithPos (getPos p) (FunMatch [(p, b)])) body params
    let1 p = reserved "let1" *> (varLhs <|> try funLhs <|> caseVarLhs) >>= \case
        VarLhs lhs -> liftA2 Let1 (varBinding p lhs) expr
        FunLhs name params -> liftA2 Let1 (funBinding p name params) expr
        CaseVarLhs lhs -> liftA2 Match expr (fmap (pure . (lhs, )) expr)
    let' = do
        reserved "let"
        bs <- parens (many pbinding)
        e <- expr
        pure $ unpos $ foldr
            (\b x -> case b of
                Left (lhs, rhs) -> WithPos (getPos rhs) (Let1 (lhs, rhs) x)
                Right (lhs, rhs) -> WithPos (getPos rhs) (Match rhs [(lhs, x)])
            )
            e
            bs
      where
        pbinding = getSrcPos >>= parens . binding
        binding p = (varLhs <|> try funLhs <|> caseVarLhs) >>= \case
            VarLhs lhs -> fmap Left (varBinding p lhs)
            FunLhs name params -> fmap Left (funBinding p name params)
            CaseVarLhs lhs -> fmap (Right . (lhs, )) expr
    letrec = reserved "letrec" *> liftA2 LetRec (parens (many pbinding)) expr
      where
        pbinding = getSrcPos >>= parens . binding
        binding p = (varLhs <|> funLhs) >>= \case
            VarLhs lhs -> varBinding p lhs
            FunLhs name params -> funBinding p name params
            CaseVarLhs _ -> ice "binding: CaseVarLhs unreachable"
    varLhs = fmap VarLhs small
    funLhs = parens (liftA2 FunLhs small (some pat))
    caseVarLhs = fmap CaseVarLhs pat
    varBinding pos lhs = do
        rhs <- expr
        pure (lhs, WithPos pos (Nothing, rhs))
    funBinding pos name params = do
        b <- expr
        let f = foldr (WithPos pos . FunMatch . pure .* (,)) b params
        pure (name, WithPos pos (Nothing, f))
    typeAscr = reserved ":" *> liftA2 TypeAscr expr type_
    sizeof = reserved "sizeof" *> fmap Sizeof type_
    app = do
        rator <- expr
        rands <- some expr
        pure (unpos (foldl' (WithPos (getPos rator) .* App) rator rands))

num :: Parser Expr'
num = andSkipSpaceAfter ns_num

ns_num :: Parser Expr'
ns_num = do
    neg <- option False (char '-' $> True)
    a <- eitherP (try (ns_nat <* notFollowedBy (char '.'))) Lexer.float
    let e = either ((\n -> Int (if neg then -n else n)) . fromIntegral)
                   (\x -> F64 (if neg then -x else x))
                   a
    pure (Lit e)

ns_nat :: Parser Word
ns_nat =
    choice [string "0b" *> Lexer.binary, string "0x" *> Lexer.hexadecimal, Lexer.decimal]

strlit :: Parser String
strlit = andSkipSpaceAfter ns_strlit

ns_strlit :: Parser String
ns_strlit = char '"' >> manyTill Lexer.charLiteral (char '"')

pat :: Parser Pat
pat = choice [patInt, patStr, patCtor, patVar, patTuple, ppat]
  where
    patInt = liftA2 PInt getSrcPos int
    patStr = liftA2 PStr getSrcPos strlit
    patCtor = fmap (\x -> PConstruction (getPos x) x []) big
    patVar = fmap PVar small
    patTuple = tuple pat (\p -> PConstruction p (Id (WithPos p "Unit")) [])
        $ \l r -> let p = getPos l in PConstruction p (Id (WithPos p "Cons")) [l, r]
    ppat = do
        pos <- getSrcPos
        parens (choice [patBox pos, patCtion pos])
    patBox pos = reserved "Box" *> fmap (PBox pos) pat
    patCtion pos = liftM3 PConstruction (pure pos) big (some pat)

scheme :: Parser Scheme
scheme = do
    pos <- getSrcPos
    let wrap = fmap (Forall pos Set.empty)
        universal = reserved "forall" *> liftA2 (Forall pos) tvars type_
        tvars = parens (fmap Set.fromList (many tvar))
    wrap nonptype <|> (parens (universal <|> wrap ptype))

type_ :: Parser Type
type_ = nonptype <|> parens ptype

nonptype :: Parser Type
nonptype = choice
    [fmap TPrim tprim, fmap TVar tvar, fmap (TConst . (, []) . idstr) big, ttuple]
  where
    tprim = try $ andSkipSpaceAfter
        (choice
                [ string "Nat" *> (fmap TNat ns_word <|> pure TNatSize)
                , string "Int" *> (fmap TInt ns_word <|> pure TIntSize)
                , string "F16" $> TF16
                , string "F32" $> TF32
                , string "F64" $> TF64
                , string "F128" $> TF128
                ]
        <* notFollowedBy identLetter
        )
    ttuple = tuple type_ (const (TConst ("Unit", []))) $ \l r -> TConst ("Cons", [l, r])

tuple :: Parser a -> (SrcPos -> a) -> (a -> a -> a) -> Parser a
tuple p unit f = brackets $ do
    a <- p
    as <- many (try p)
    let ls = a : as
    pos <- getSrcPos
    r <- option (unit pos) (try (reserved "." *> p))
    pure $ foldr f r ls

ptype :: Parser Type
ptype = choice [tfun, tbox, tapp]
  where
    tfun = do
        reserved "Fun"
        t <- type_
        ts <- some type_
        pure (foldr1 TFun (t : ts))
    tbox = reserved "Box" *> fmap TBox type_
    tapp = liftA2 (TConst .* (,) . idstr) big (some type_)

tvar :: Parser TVar
tvar = fmap TVExplicit small

parens :: Parser a -> Parser a
parens = andSkipSpaceAfter . ns_parens

ns_parens :: Parser a -> Parser a
ns_parens = between (symbol "(") (string ")")

brackets :: Parser a -> Parser a
brackets = andSkipSpaceAfter . ns_brackets

ns_brackets :: Parser a -> Parser a
ns_brackets = between (symbol "[") (string "]")

int :: Num a => Parser a
int = andSkipSpaceAfter (Lexer.signed empty ns_word)

ns_word :: Num a => Parser a
ns_word = Lexer.decimal

big :: Parser (Id 'Big)
big = fmap Id (special <|> normal)
  where
    special = reserved "Id@" *> withPos strlit
    normal = withPos $ try $ do
        s <- identifier
        let c = head s
        if (isUpper c || [c] == ":")
            then pure s
            else fail "Big identifier must start with an uppercase letter or colon."

small :: Parser (Id 'Small)
small = fmap Id (special <|> normal)
  where
    special = reserved "id@" *> withPos strlit
    normal = withPos $ try $ do
        s <- identifier
        let c = head s
        if (isUpper c || [c] == ":")
            then fail "Small identifier must not start with an uppercase letter or colon."
            else pure s

identifier :: Parser String
identifier = do
    name <- ident
    if elem name reserveds
        then unexpected (Label (NonEmpty.fromList ("reserved word " ++ show name)))
        else pure name

ident :: Parser String
ident = andSkipSpaceAfter ns_ident

ns_ident :: Parser String
ns_ident = label "identifier" $ liftA2 (:) identStart (many identLetter)
  where
    identStart =
        choice [letterChar, otherChar, try (oneOf "-+" <* notFollowedBy digitChar)]

identLetter :: Parser Char
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
    , "."
    , "Fun"
    , "Box"
    , "define"
    , "define:"
    , "extern"
    , "forall"
    , "fmatch"
    , "match"
    , "if"
    , "fun"
    , "let1"
    , "let"
    , "letrec"
    , "data"
    , "sizeof"
    , "import"
    , "case"
    , "id@"
    , "Id@"
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
getSrcPos = fmap
    (\(SourcePos f l c) -> SrcPos f (fromIntegral (unPos l)) (fromIntegral (unPos c)))
    getSourcePos
