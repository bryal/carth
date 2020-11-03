{-# LANGUAGE LambdaCase #-}

module Pretty (pretty, Pretty(..)) where

import Prelude hiding (showChar)
import Data.Bifunctor
import qualified Data.Set as Set
import Data.Set (Set)
import LLVM.AST (Module)
import LLVM.Pretty ()
import qualified Data.Text.Prettyprint.Doc as Prettyprint

import SrcPos
import qualified Lexd
import qualified Parsed
import qualified Inferred
import qualified Optimized as Ast


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
        Lexd.KFun -> "Fun"
        Lexd.KBox -> "Box"
        Lexd.Kdefine -> "define"
        Lexd.KdefineColon -> "define:"
        Lexd.Kimport -> "import"
        Lexd.Kextern -> "extern"
        Lexd.Kdata -> "data"
        Lexd.Kfmatch -> "fmatch"
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


instance Pretty Parsed.Scheme where
    pretty' _ (Parsed.Forall _ ps t) = prettyScheme ps t
instance Pretty Parsed.Type where
    pretty' _ = prettyType
instance Pretty Parsed.TPrim where
    pretty' _ = prettyTPrim
instance Pretty Parsed.TVar where
    pretty' _ = prettyTVar
instance Pretty (Parsed.Id a) where
    pretty' _ = Parsed.idstr

prettyScheme :: (Pretty p, Pretty t) => Set p -> t -> String
prettyScheme ps t =
    concat ["(forall (" ++ spcPretty (Set.toList ps) ++ ") ", pretty t ++ ")"]

prettyType :: Parsed.Type -> String
prettyType = \case
    Parsed.TVar tv -> pretty tv
    Parsed.TPrim c -> pretty c
    Parsed.TFun a b -> prettyTFun a b
    Parsed.TBox t -> prettyTBox t
    Parsed.TConst tc -> prettyTConst tc

prettyTConst :: Pretty t => (String, [t]) -> String
prettyTConst (c, ts) = case ts of
    [] -> c
    _ -> concat ["(", c, " ", spcPretty ts, ")"]

prettyTBox :: Pretty t => t -> String
prettyTBox t = "(Box " ++ pretty t ++ ")"

prettyTFun :: Parsed.Type -> Parsed.Type -> String
prettyTFun a b =
    let (bParams, bBody) = f b
        f = \case
            Parsed.TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in  concat ["(Fun ", pretty a, " ", spcPretty (bParams ++ [bBody]), ")"]

prettyTPrim :: Parsed.TPrim -> String
prettyTPrim = \case
    Parsed.TNat w -> "Nat" ++ show w
    Parsed.TNatSize -> "Nat"
    Parsed.TInt w -> "Int" ++ show w
    Parsed.TIntSize -> "Int"
    Parsed.TF16 -> "F16"
    Parsed.TF32 -> "F32"
    Parsed.TF64 -> "F64"
    Parsed.TF128 -> "F128"

prettyTVar :: Parsed.TVar -> String
prettyTVar = \case
    Parsed.TVExplicit v -> Parsed.idstr v
    Parsed.TVImplicit v -> "•" ++ v


instance Pretty Inferred.Scheme where
    pretty' _ (Inferred.Forall ps t) = prettyScheme ps t
instance Pretty Inferred.Type where
    pretty' _ = prettyAnType

prettyAnType :: Inferred.Type -> String
prettyAnType = \case
    Inferred.TVar tv -> pretty tv
    Inferred.TPrim c -> pretty c
    Inferred.TFun a b -> prettyAnTFun a b
    Inferred.TBox t -> prettyTBox t
    Inferred.TConst tc -> prettyTConst tc

prettyAnTFun :: Inferred.Type -> Inferred.Type -> String
prettyAnTFun a b =
    let (bParams, bBody) = f b
        f = \case
            Inferred.TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in  concat ["(Fun ", pretty a, " ", spcPretty (bParams ++ [bBody]), ")"]


instance Pretty Ast.Type where
    pretty' _ = prettyMonoType

prettyMonoType :: Ast.Type -> String
prettyMonoType = \case
    Ast.TPrim c -> pretty c
    Ast.TFun a b -> prettyMonoTFun a b
    Ast.TBox t -> prettyTBox t
    Ast.TConst tc -> prettyTConst tc

prettyMonoTFun :: Ast.Type -> Ast.Type -> String
prettyMonoTFun a b =
    let (bParams, bBody) = f b
        f = \case
            Ast.TFun a' b' -> first (a' :) (f b')
            t -> ([], t)
    in  concat ["(Fun ", pretty a, " ", spcPretty (bParams ++ [bBody]), ")"]


instance Pretty Module where
    pretty' _ = show . Prettyprint.pretty
