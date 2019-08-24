{-# LANGUAGE MultiParamTypeClasses, LambdaCase #-}

module FreeVars
    ( FreeVars(..)
    , Pattern(..)
    , fvLit
    , fvVar
    , fvApp
    , fvIf
    , fvFun
    , fvLet
    , fvMatch
    )
where

import qualified Data.Set as Set
import Data.Set (Set)
import Data.Foldable

class Ord b => FreeVars a b where
    freeVars :: a -> Set b

class Ord b => Pattern a b where
    patternBoundVars :: a -> Set b

fvLit :: a -> Set b
fvLit = const Set.empty

fvVar :: a -> Set a
fvVar = Set.singleton

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
fvMatch e cs = Set.union
    (freeVars e)
    (Set.unions
        (map (\(p, e) -> Set.difference (freeVars e) (patternBoundVars p)) cs)
    )
