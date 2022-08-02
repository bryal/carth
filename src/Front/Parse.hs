{-# LANGUAGE DataKinds #-}

module Front.Parse (parse, c_validIdent, c_validIdentFirst, c_validIdentRest, c_keywords) where

import Control.Arrow
import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Writer
import Control.Monad.Combinators
import Data.Char
import Data.Maybe
import qualified Data.Set as Set
import Text.Read (readMaybe)

import Misc
import Front.SrcPos
import Front.Lexd hiding (Big, Small)
import qualified Front.Lexd as Lexd
import Front.Parser
import Front.Parsed hiding (Lit)
import qualified Front.Parsed as Parsed

parse :: [TokenTree] -> (Either (SrcPos, String) Program, [Message])
parse = runParser' (fmap (\(ds, ts, es) -> Program ds ts es) toplevels)

toplevels :: Parser ([Def], [TypeDef], [Extern])
toplevels = fmap mconcat (manyTill toplevel end)
  where
    toplevel = parens' $ \topPos -> choice
        [ fmap (\d -> ([d], [], [])) (def topPos)
        , fmap (\t -> ([], [t], [])) typedef
        , fmap (\e -> ([], [], [e])) extern
        ]

extern :: Parser Extern
extern = do
    reserved Kextern
    x@(Id (WithPos pos x')) <- small
    unless (c_validIdent x') $ tell
        [ Warning
              pos
              "This identifier is not guaranteed to be compatible with any C compiler, according to the C11 standard.\nThis is likely to cause issues if you use the C backend when compiling this Carth program, or if you want to link to the symbol later on in C."
        ]
    Extern x <$> type_

typedef :: Parser TypeDef
typedef = do
    _ <- reserved Kdata
    let onlyName = fmap (, []) big
    let nameAndSome = parens . liftA2 (,) big . some
    (name, params) <- onlyName <|> nameAndSome small
    constrs <- many (onlyName <|> nameAndSome type_)
    pure (TypeDef name params (ConstructorDefs constrs))

def :: SrcPos -> Parser Def
def topPos = defUntyped topPos <|> defTyped topPos

-- TODO: ~define (foo a b)~ -> ~defun foo [a b]~
defUntyped :: SrcPos -> Parser Def
defUntyped pos = reserved Kdefine *> def' (pure Nothing) pos

defTyped :: SrcPos -> Parser Def
defTyped pos = reserved KdefineColon *> def' (fmap Just scheme) pos

def' :: Parser (Maybe Scheme) -> SrcPos -> Parser Def
def' schemeParser topPos = varDef <|> funDef
  where
    -- FIXME: Don't `try` the whole def. If we find a define keyword in the beginning of the
    --        parens, we know it's supposed to be a definition. Don't backtrack and try to parse it
    --        as an expression if some later part of the definition is invalid.
    parenDef = try (parens' def)
    body = do
        ds <- many parenDef
        if null ds then expr else fmap (\b -> WithPos (getPos b) (LetRec ds b)) expr
    varDef = do
        name <- small
        scm <- schemeParser
        VarDef topPos name scm <$> body
    funDef = do
        pos <- getSrcPos -- FIXME: This should be a pos surrounding only the params
        (name, params) <- parens (liftM2 (,) small (some pat))
        scm <- schemeParser
        FunDef topPos name scm (WithPos pos params) <$> body

expr :: Parser Expr
expr = withPos expr'

data BindingLhs
    = VarLhs (Id 'Small)
    | FunLhs (Id 'Small) FunPats
    | CaseVarLhs Pat

expr' :: Parser Expr'
expr' = choice [var, lit, eConstructor, etuple, pexpr]
  where
    lit = token "constant literal" $ const $ \case
        Lit c -> Just (Parsed.Lit c)
        _ -> Nothing
    eConstructor = fmap Ctor big
    -- FIXME: These positions are completely wack. Gotta get a separate variant in the AST for
    --        pairs. Similar to Box.
    etuple = fmap unpos $ tuple expr (\p -> WithPos p (Ctor (Id (WithPos p "Unit")))) $ \l r ->
        let p = getPos l in WithPos p (App (WithPos p (Ctor (Id (WithPos p "Cons")))) [l, r])
    var = fmap Var small
    pexpr = parens'
        $ \p -> choice [funMatch, match, if', fun, let1 p, let', letrec, typeAscr, sizeof, app]
    funMatch = do
        reserved KfunStar
        FunMatch <$> some
            (parens (reserved Kcase *> liftA2 (,) (withPos (brackets (some pat))) expr))
    match = reserved Kmatch
        *> liftA2 Match expr (many (parens (reserved Kcase *> liftA2 (,) pat expr)))
    if' = reserved Kif *> liftM3 If expr expr expr
    fun = do
        reserved Kfun
        -- TODO: Make this brackets. Since it's tuple-like, and we could do with some variation
        --       when reading...
        params <- withPos $ parens (some pat)
        body <- expr
        pure $ FunMatch [(params, body)]
    let1 p = reserved Klet1 *> (varLhs <|> try funLhs <|> caseVarLhs) >>= \case
        VarLhs lhs -> liftA2 (Let1 . Def) (varBinding p lhs) expr
        FunLhs name params -> liftA2 (Let1 . Def) (funBinding p name params) expr
        CaseVarLhs lhs -> liftA2 Let1 (fmap (Deconstr lhs) expr) expr
    let' = do
        reserved Klet
        bs <- parens (many pbinding)
        Let bs <$> expr
      where
        pbinding = parens' binding
        binding p = (varLhs <|> try funLhs <|> caseVarLhs) >>= \case
            VarLhs lhs -> fmap Def (varBinding p lhs)
            FunLhs name params -> fmap Def (funBinding p name params)
            CaseVarLhs lhs -> fmap (Deconstr lhs) expr
    letrec = reserved Kletrec *> liftA2 LetRec (parens (many pbinding)) expr
      where
        pbinding = parens' binding
        binding p = (varLhs <|> funLhs) >>= \case
            VarLhs lhs -> varBinding p lhs
            FunLhs name params -> funBinding p name params
            CaseVarLhs _ -> ice "letrec binding: CaseVarLhs"
    varLhs = fmap VarLhs small
    funLhs = parens' (\pos -> liftA2 FunLhs small (fmap (WithPos pos) (some pat)))
    caseVarLhs = fmap CaseVarLhs pat
    varBinding pos lhs = VarDef pos lhs Nothing <$> expr
    funBinding pos name params = FunDef pos name Nothing params <$> expr
    typeAscr = reserved Kcolon *> liftA2 TypeAscr expr type_
    sizeof = reserved Ksizeof *> fmap Sizeof type_
    app = do
        rator <- expr
        rands <- some expr
        pure (App rator rands)

pat :: Parser Pat
pat = choice [patInt, patStr, patCtor, patVar, patTuple, ppat]
  where
    patInt = token "integer literal" $ \p -> \case
        Lit (Int x) -> Just (PInt p x)
        _ -> Nothing
    patStr = liftA2 PStr getSrcPos strlit
    strlit = token "string literal" $ const $ \case
        Lit (Str s) -> Just s
        _ -> Nothing
    patCtor = fmap (\x -> PConstruction (getPos x) x []) big
    patVar = fmap PVar small
    patTuple = tuple pat (\p -> PConstruction p (Id (WithPos p "Unit")) [])
        $ \l r -> let p = getPos l in PConstruction p (Id (WithPos p "Cons")) [l, r]
    ppat = parens' $ \pos -> choice [patBox pos, patCtion pos]
    patBox pos = reserved KBox *> fmap (PBox pos) pat
    patCtion pos = liftM3 PConstruction (pure pos) big (some pat)

scheme :: Parser Scheme
scheme = do
    pos <- getSrcPos
    let wrap = fmap (Forall pos Set.empty Set.empty)
        universal =
            reserved Kforall *> liftA3 (Forall pos) tvars (option Set.empty (try constrs)) type_
        tvars = parens (fmap Set.fromList (some tvar))
        constrs = parens (reserved Kwhere *> fmap Set.fromList (some (parens tapp)))
    wrap nonptype <|> parens (universal <|> wrap ptype)

type_ :: Parser Type
type_ = nonptype <|> parens ptype

nonptype :: Parser Type
nonptype = choice [fmap TPrim tprim, fmap TVar tvar, fmap (TConst . (, []) . idstr) big, ttuple]
  where
    tprim = token "primitive type" $ const $ \case
        Lexd.Big ('N' : 'a' : 't' : s) | isWord s -> Just (TNat (read s))
        Lexd.Big ('I' : 'n' : 't' : s) | isWord s -> Just (TInt (read s))
        Lexd.Big "Nat" -> Just TNatSize
        Lexd.Big "Int" -> Just TIntSize
        Lexd.Big "F32" -> Just TF32
        Lexd.Big "F64" -> Just TF64
        _ -> Nothing
    ttuple = tuple type_ (const (TConst ("Unit", []))) $ \l r -> TConst ("Cons", [l, r])

-- | FIXME: Positions in here are kind of bad
tuple :: Parser a -> (SrcPos -> a) -> (a -> a -> a) -> Parser a
tuple p unit f = brackets $ do
    a <- p
    as <- many (try p)
    let ls = a : as
    pos <- gets stOuterPos
    r <- option (unit pos) (try (reserved Kdot *> p))
    pure $ foldr f r ls

ptype :: Parser Type
ptype = choice [tfun, tbox, fmap (TConst . second (map snd)) tapp]
  where
    tfun = do
        reserved KFun
        ts <- some type_
        let (ps, r) = fromJust $ unsnoc ts
        pure (TFun ps r)
    tbox = reserved KBox *> fmap TBox type_

tapp :: Parser (String, [(SrcPos, Type)])
tapp = liftA2 ((,) . idstr) big (some (liftA2 (,) getSrcPos type_))

tvar :: Parser TVar
tvar = fmap TVExplicit small

isWord :: String -> Bool
isWord s = isJust (readMaybe s :: Maybe Word)

-- | Valid identifiers in the C language according to the C11 standard "ISO/IEC 9899:2011",
--   excluding "other implementation-defined characters".
--
--   Carth is in some ways more liberal with what characters are allowed in an identifier, like the
--   plain old dash (-). As one often wants to link with C or C-compatible languages when using
--   ~extern~, it's a good idea to warn the user if she attempts to import or export a symbol
--   externally that has a name incompatible with C. Such a name would also prevent codegen with
--   the C backend completely.
--
--   As an ~extern~ is not necessarely used in conjunction with C, however, we don't want to impose
--   a hard limit their names being C compatible, wherefore it's a warning and not an error.
c_validIdent :: String -> Bool
c_validIdent s =
    c_validIdentFirst (head s) && all c_validIdentRest (tail s) && notElem s c_keywords

c_validIdentFirst :: Char -> Bool
c_validIdentFirst = c_identNondigit

c_validIdentRest :: Char -> Bool
c_validIdentRest c = c_identNondigit c || isDigit c

c_identNondigit :: Char -> Bool
c_identNondigit c = nondigit c || universalCharacterName c
  where
    nondigit c = c == '_' || isAsciiUpper c || isAsciiLower c
    universalCharacterName = ord >>> \c ->
        (c == 0x00A8)
            || (c == 0x00AA)
            || (c == 0x00AD)
            || (c == 0x00AF)
            || (c >= 0x00B2 && c <= 0x00B5)
            || (c >= 0x00B7 && c <= 0x00BA)
            || (c >= 0x00BC && c <= 0x00BE)
            || (c >= 0x00C0 && c <= 0x00D6)
            || (c >= 0x00D8 && c <= 0x00F6)
            || (c >= 0x00F8 && c <= 0x00FF)
            || (c >= 0x0100 && c <= 0x167F)
            || (c >= 0x1681 && c <= 0x180D)
            || (c >= 0x180F && c <= 0x1FFF)
            || (c >= 0x200B && c <= 0x200D)
            || (c >= 0x202A && c <= 0x202E)
            || (c >= 0x203F && c <= 0x2040)
            || (c == 0x2054)
            || (c >= 0x2060 && c <= 0x206F)
            || (c >= 0x2070 && c <= 0x218F)
            || (c >= 0x2460 && c <= 0x24FF)
            || (c >= 0x2776 && c <= 0x2793)
            || (c >= 0x2C00 && c <= 0x2DFF)
            || (c >= 0x2E80 && c <= 0x2FFF)
            || (c >= 0x3004 && c <= 0x3007)
            || (c >= 0x3021 && c <= 0x302F)
            || (c >= 0x3031 && c <= 0x303F)
            || (c >= 0x3040 && c <= 0xD7FF)
            || (c >= 0xF900 && c <= 0xFD3D)
            || (c >= 0xFD40 && c <= 0xFDCF)
            || (c >= 0xFDF0 && c <= 0xFE44)
            || (c >= 0xFE47 && c <= 0xFFFD)
            || (c >= 0x10000 && c <= 0x1FFFD)
            || (c >= 0x20000 && c <= 0x2FFFD)
            || (c >= 0x30000 && c <= 0x3FFFD)
            || (c >= 0x40000 && c <= 0x4FFFD)
            || (c >= 0x50000 && c <= 0x5FFFD)
            || (c >= 0x60000 && c <= 0x6FFFD)
            || (c >= 0x70000 && c <= 0x7FFFD)
            || (c >= 0x80000 && c <= 0x8FFFD)
            || (c >= 0x90000 && c <= 0x9FFFD)
            || (c >= 0xA0000 && c <= 0xAFFFD)
            || (c >= 0xB0000 && c <= 0xBFFFD)
            || (c >= 0xC0000 && c <= 0xCFFFD)
            || (c >= 0xD0000 && c <= 0xDFFFD)
            || (c >= 0xE0000 && c <= 0xEFFFD)

c_keywords :: [String]
c_keywords =
    [ "auto"
    , "break"
    , "case"
    , "char"
    , "const"
    , "continue"
    , "default"
    , "do"
    , "double"
    , "else"
    , "enum"
    , "extern"
    , "float"
    , "for"
    , "goto"
    , "if"
    , "inline"
    , "int"
    , "long"
    , "register"
    , "restrict"
    , "return"
    , "short"
    , "signed"
    , "sizeof"
    , "static"
    , "struct"
    , "switch"
    , "typedef"
    , "union"
    , "unsigned"
    , "void"
    , "volatile"
    , "while"
    , "_Alignas"
    , "_Alignof"
    , "_Atomic"
    , "_Bool"
    , "_Complex"
    , "_Generic"
    , "_Imaginary"
    , "_Noreturn"
    , "_Static_assert"
    , "_Thread_local"
    ]
