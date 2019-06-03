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
