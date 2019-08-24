{-# LANGUAGE MultiParamTypeClasses, LambdaCase #-}

module FreeVars
    ( FreeVars(..)
    , Pattern(..)
    , fvApp
    , fvIf
    , fvFun
    , fvLet
    , fvMatch
    , fvCases
    )
where

import qualified Data.Set as Set
import Data.Set (Set)
import Data.Foldable

class Ord b => FreeVars a b where
    freeVars :: a -> Set b

class Ord b => Pattern a b where
    patternBoundVars :: a -> Set b

fvApp :: FreeVars e t => e -> e -> Set t
fvApp f a = Set.unions (map freeVars [f, a])

fvIf :: FreeVars e t => e -> e -> e -> Set t
fvIf p c a = Set.unions (map freeVars [p, c, a])

fvFun :: FreeVars e t => t -> e -> Set t
fvFun p b = Set.delete p (freeVars b)

fvLet :: (FreeVars e t, Foldable f) => (Set t, f e) -> e -> Set t
fvLet (bVs, bBs) b = Set.difference
    (Set.union (freeVars b) (foldr (Set.union . freeVars) Set.empty bBs))
    (Set.fromList (toList bVs))

fvMatch :: (Pattern p t, FreeVars e t) => e -> [(p, e)] -> Set t
fvMatch e cs = Set.union (freeVars e) (fvCases cs)

fvCases :: (Pattern p t, FreeVars e t) => [(p, e)] -> Set t
fvCases = Set.unions
    . map (\(p, e) -> Set.difference (freeVars e) (patternBoundVars p))
