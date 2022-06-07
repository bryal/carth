{-# LANGUAGE UndecidableInstances #-}

module Pretty (pretty, Pretty(..), prettyTConst) where

import Prelude hiding (showChar)
import Data.Bifunctor
import qualified Data.Set as Set
import Data.Set (Set)
import LLVM.AST (Module)
import LLVM.Pretty ()
import qualified Prettyprinter as Prettyprint

import Misc
import Front.TypeAst
import Front.SrcPos
import qualified Front.Lexd as Lexd
import qualified Front.Parsed as Parsed
import qualified Front.Inferred as Inferred


-- Pretty print starting at some indentation depth
class Pretty a where
    pretty' :: Int -> a -> String

pretty :: Pretty a => a -> String
pretty = pretty' 0

spcPretty :: Pretty a => [a] -> String
spcPretty = unwords . map pretty


instance Pretty a => Pretty (WithPos a) where
    pretty' d = pretty' d . unpos

instance Pretty Lexd.Keyword where
    pretty' _ = \case
        Lexd.Kcolon -> ":"
        Lexd.Kdot -> "."
        Lexd.Kforall -> "forall"
        Lexd.Kwhere -> "where"
        Lexd.KFun -> "Fun"
        Lexd.KBox -> "Box"
        Lexd.Kdefine -> "define"
        Lexd.KdefineColon -> "define:"
        Lexd.Kimport -> "import"
        Lexd.Kextern -> "extern"
        Lexd.Kdata -> "data"
        Lexd.KfunStar -> "fun*"
        Lexd.Kmatch -> "match"
        Lexd.Kcase -> "case"
        Lexd.Kif -> "if"
        Lexd.Kfun -> "fun"
        Lexd.Klet1 -> "let1"
        Lexd.Klet -> "let"
        Lexd.Kletrec -> "letrec"
        Lexd.Ksizeof -> "sizeof"
        Lexd.KidAt -> "id@"
        Lexd.KIdAt -> "Id@"
        Lexd.Kdefmacro -> "defmacro"

instance Pretty var => Pretty (Type' var) where
    pretty' _ = prettyType
instance Pretty TPrim where
    pretty' _ = prettyTPrim

instance Pretty Parsed.Scheme where
    pretty' _ (Parsed.Forall _ ps cs t) =
        prettyScheme ps (map (second (map snd)) (Set.toList cs)) t
instance Pretty Parsed.TVar where
    pretty' _ = prettyTVar
instance Pretty (Parsed.Id a) where
    pretty' _ = Parsed.idstr

prettyType :: Pretty var => Type' var -> String
prettyType = \case
    TVar tv -> pretty tv
    TPrim c -> pretty c
    TFun ps r -> prettyTFun ps r
    TBox t -> prettyTBox t
    TConst tc -> prettyTConst tc

prettyScheme :: (Pretty p, Pretty var) => Set p -> [(String, [Type' var])] -> Type' var -> String
prettyScheme ps cs t = concat
    [ "(forall (" ++ spcPretty (Set.toList ps) ++ ") "
    , "(where " ++ unwords (map prettyTConst cs) ++ ") "
    , pretty t ++ ")"
    ]

prettyTConst :: (Pretty var) => (String, [Type' var]) -> String
prettyTConst = \case
    ("Cons", [t1, t2]) -> "[" ++ pretty t1 ++ prettyConses t2
    ("Cons", []) -> ice "prettyTConst: Cons hasn't two types"
    (c, []) -> c
    (c, ts) -> concat ["(", c, " ", spcPretty ts, ")"]
  where
    prettyConses t = case unTconst t of
        Just ("Cons", [t1, t2]) -> " " ++ pretty t1 ++ prettyConses t2
        Just ("Unit", _) -> "]"
        _ -> " . " ++ pretty t ++ "]"


prettyTBox :: Pretty t => t -> String
prettyTBox t = "(Box " ++ pretty t ++ ")"

prettyTFun :: Pretty var => [Type' var] -> Type' var -> String
prettyTFun as b = concat ["(Fun ", spcPretty as, " ", pretty b, ")"]

prettyTPrim :: Parsed.TPrim -> String
prettyTPrim = \case
    Parsed.TNat w -> "Nat" ++ show w
    Parsed.TNatSize -> "Nat"
    Parsed.TInt w -> "Int" ++ show w
    Parsed.TIntSize -> "Int"
    Parsed.TF32 -> "F32"
    Parsed.TF64 -> "F64"

prettyTVar :: Parsed.TVar -> String
prettyTVar = \case
    Parsed.TVExplicit v -> Parsed.idstr v
    Parsed.TVImplicit v -> "•" ++ v

instance Pretty Inferred.Scheme where
    pretty' _ (Inferred.Forall ps cs t) = prettyScheme ps (Set.toList cs) t

instance Pretty Module where
    pretty' _ = show . Prettyprint.pretty
