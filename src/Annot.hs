{-# LANGUAGE TemplateHaskell, LambdaCase, MultiParamTypeClasses
           , FlexibleInstances, FlexibleContexts #-}

module Annot (Program(..), Expr(..), Const(..), TypedVar(..)) where

import qualified Data.Set as Set
import Data.Set (Set)

import Misc
import Ast (Const(..))

data TypedVar t = TypedVar String t
  deriving (Show, Eq, Ord)

data Expr t ds
    = Lit Const
    | Var (TypedVar t)
    | App (Expr t ds)
          (Expr t ds)
    | If (Expr t ds)
         (Expr t ds)
         (Expr t ds)
    | Fun (String, t)
          (Expr t ds, t)
    | Let ds
          (Expr t ds)
    deriving (Show, Eq)

data Program typ defs =
    Program (Expr typ defs)
            defs
    deriving (Show)

instance (Ord t, FreeVars ds (TypedVar t))
      => FreeVars (Expr t ds) (TypedVar t) where
    freeVars = fvExpr

fvExpr :: (Ord t, FreeVars ds (TypedVar t)) => Expr t ds -> Set (TypedVar t)
fvExpr = \case
    Lit _ -> Set.empty
    Var v -> Set.singleton v
    App f a -> Set.unions (map freeVars [f, a])
    If p c a -> Set.unions (map freeVars [p, c, a])
    Fun (p, pt) (b, _) -> Set.delete (TypedVar p pt) (freeVars b)
    Let ds e ->
        Set.difference (Set.union (freeVars e) (freeVars ds)) (boundVars ds)

instance (Pretty t, Pretty ds) => Pretty (Annot.Expr t ds) where
    pretty' = prettyExpr

prettyExpr :: (Pretty t, Pretty ds) => Int -> Annot.Expr t ds -> String
prettyExpr d = \case
    Annot.Lit l -> pretty l
    Annot.Var (Annot.TypedVar v t) -> "(: " ++ v ++ " " ++ pretty t ++ ")"
    Annot.App f x -> concat
        [ "("
        , pretty' (d + 1) f
        , "\n"
        , replicate (d + 1) ' '
        , pretty' (d + 1) x
        , ")"
        ]
    Annot.If pred cons alt -> concat
        [ "(if "
        , pretty' (d + 4) pred
        , "\n"
        , replicate (d + 4) ' '
        , pretty' (d + 4) cons
        , "\n"
        , replicate (d + 2) ' '
        , pretty' (d + 2) alt
        , ")"
        ]
    Annot.Fun (param, tp) (body, _) -> concat
        [ "(fun (: "
        , param
        , " "
        , pretty tp
        , ")"
        , "\n"
        , replicate (d + 2) ' '
        , pretty' (d + 2) body
        , ")"
        ]
    Annot.Let binds body -> concat
        [ "(let ["
        , pretty' (d + 6) binds
        , "]\n"
        , replicate (d + 2) ' ' ++ pretty' (d + 2) body
        , ")"
        ]
