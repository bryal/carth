module FreeVars where

import qualified Data.Set as Set
import Data.Set (Set)

class Ord b => FreeVars a b where
    freeVars :: a -> Set b

fvApp :: FreeVars e t => e -> [e] -> Set t
fvApp f as = Set.unions (map freeVars (f : as))

fvIf :: FreeVars e t => e -> e -> e -> Set t
fvIf p c a = Set.unions (map freeVars [p, c, a])

fvFun :: FreeVars e t => t -> e -> Set t
fvFun p b = Set.delete p (freeVars b)

fvLet :: (FreeVars a t, FreeVars b t, Foldable f) => ([t], f a) -> b -> Set t
fvLet (bVs, bBs) e = Set.difference
    (Set.union (freeVars e) (foldr (Set.union . freeVars) Set.empty bBs))
    (Set.fromList bVs)
