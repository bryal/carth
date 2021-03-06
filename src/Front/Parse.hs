{-# LANGUAGE DataKinds #-}

module Front.Parse (parse) where

import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Monad.Combinators
import Data.Bifunctor
import Data.Maybe
import qualified Data.Set as Set
import Data.List
import Text.Read (readMaybe)

import Misc
import Front.SrcPos
import Front.Lexd hiding (Big, Small)
import qualified Front.Lexd as Lexd
import Front.Parser
import Front.Parsed hiding (Lit)
import qualified Front.Parsed as Parsed

parse :: [TokenTree] -> Except (SrcPos, String) Program
parse tts = fmap (\(ds, ts, es) -> Program ds ts es) (runParser' toplevels tts)

toplevels :: Parser ([Def], [TypeDef], [Extern])
toplevels = fmap mconcat (manyTill toplevel end)
  where
    toplevel = parens' $ \topPos -> choice
        [ fmap (\d -> ([d], [], [])) (def topPos)
        , fmap (\t -> ([], [t], [])) typedef
        , fmap (\e -> ([], [], [e])) extern
        ]

extern :: Parser Extern
extern = reserved Kextern *> liftA2 Extern small type_

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

defUntyped :: SrcPos -> Parser Def
defUntyped pos = reserved Kdefine *> def' (pure Nothing) pos

defTyped :: SrcPos -> Parser Def
defTyped pos = reserved KdefineColon *> def' (fmap Just scheme) pos

def' :: Parser (Maybe Scheme) -> SrcPos -> Parser Def
def' schemeParser topPos = varDef <|> funDef
  where
    parenDef = try (parens' def)
    body = do
        ds <- many parenDef
        if null ds then expr else fmap (\b -> WithPos (getPos b) (LetRec ds b)) expr
    varDef = do
        name <- small
        scm <- schemeParser
        b <- body
        pure (VarDef topPos name scm b)
    funDef = do
        (name, params) <- parens (liftM2 (,) small (some pat))
        scm <- schemeParser
        b <- body
        pure (FunDef topPos name scm params b)

expr :: Parser Expr
expr = withPos expr'

data BindingLhs
    = VarLhs (Id 'Small)
    | FunLhs (Id 'Small) [Pat]
    | CaseVarLhs Pat

expr' :: Parser Expr'
expr' = choice [var, lit, eConstructor, etuple, pexpr]
  where
    lit = token "constant literal" $ const $ \case
        Lit c -> Just (Parsed.Lit c)
        _ -> Nothing
    eConstructor = fmap Ctor big
    -- FIXME: These positions are completely wack. Gotta get a separate variant in the AST
    --        for pairs. Similar to Box.
    etuple =
        fmap unpos
            $ tuple expr (\p -> WithPos p (Ctor (Id (WithPos p "Unit"))))
            $ \l r ->
                  let p = getPos l
                  in  WithPos p $ App
                          (WithPos p (App (WithPos p (Ctor (Id (WithPos p "Cons")))) l))
                          r
    var = fmap Var small
    pexpr = parens' $ \p -> choice
        [funMatch, match, if', fun, let1 p, let', letrec, typeAscr, sizeof, app]
    funMatch = reserved Kfmatch *> fmap FunMatch cases
    match = reserved Kmatch *> liftA2 Match expr cases
    cases = many (parens (reserved Kcase *> (liftA2 (,) pat expr)))
    if' = reserved Kif *> liftM3 If expr expr expr
    fun = do
        reserved Kfun
        params <- parens (some pat)
        body <- expr
        pure $ unpos $ foldr (\p b -> WithPos (getPos p) (FunMatch [(p, b)])) body params
    let1 p = reserved Klet1 *> (varLhs <|> try funLhs <|> caseVarLhs) >>= \case
        VarLhs lhs -> liftA2 (Let1 . Def) (varBinding p lhs) expr
        FunLhs name params -> liftA2 (Let1 . Def) (funBinding p name params) expr
        CaseVarLhs lhs -> liftA2 Let1 (fmap (Deconstr lhs) expr) expr
    let' = do
        reserved Klet
        bs <- parens (many pbinding)
        e <- expr
        pure (Let bs e)
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
    funLhs = parens (liftA2 FunLhs small (some pat))
    caseVarLhs = fmap CaseVarLhs pat
    varBinding pos lhs = do
        rhs <- expr
        pure (VarDef pos lhs Nothing rhs)
    funBinding pos name params = do
        b <- expr
        pure (FunDef pos name Nothing params b)
    typeAscr = reserved Kcolon *> liftA2 TypeAscr expr type_
    sizeof = reserved Ksizeof *> fmap Sizeof type_
    app = do
        rator <- expr
        rands <- some expr
        pure (unpos (foldl' (WithPos (getPos rator) .* App) rator rands))

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
    ppat = parens' $ \pos -> (choice [patBox pos, patCtion pos])
    patBox pos = reserved KBox *> fmap (PBox pos) pat
    patCtion pos = liftM3 PConstruction (pure pos) big (some pat)

scheme :: Parser Scheme
scheme = do
    pos <- getSrcPos
    let wrap = fmap (Forall pos Set.empty Set.empty)
        universal =
            reserved Kforall
                *> liftA3 (Forall pos) tvars (option Set.empty (try constrs)) type_
        tvars = parens (fmap Set.fromList (some tvar))
        constrs = parens (reserved Kwhere *> fmap Set.fromList (some (parens tapp)))
    wrap nonptype <|> (parens (universal <|> wrap ptype))

type_ :: Parser Type
type_ = nonptype <|> parens ptype

nonptype :: Parser Type
nonptype = choice
    [fmap TPrim tprim, fmap TVar tvar, fmap (TConst . (, []) . idstr) big, ttuple]
  where
    tprim = token "primitive type" $ const $ \case
        Lexd.Big ('N' : 'a' : 't' : s) | isWord s -> Just (TNat (read s))
        Lexd.Big ('I' : 'n' : 't' : s) | isWord s -> Just (TInt (read s))
        Lexd.Big "Nat" -> Just TNatSize
        Lexd.Big "Int" -> Just TIntSize
        Lexd.Big "F16" -> Just TF16
        Lexd.Big "F32" -> Just TF32
        Lexd.Big "F64" -> Just TF64
        Lexd.Big "F128" -> Just TF128
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
        t <- type_
        ts <- some type_
        pure (foldr1 TFun (t : ts))
    tbox = reserved KBox *> fmap TBox type_

tapp :: Parser (String, [(SrcPos, Type)])
tapp = liftA2 ((,) . idstr) big (some (liftA2 (,) getSrcPos type_))

tvar :: Parser TVar
tvar = fmap TVExplicit small

isWord :: String -> Bool
isWord s = isJust ((readMaybe s) :: Maybe Word)
