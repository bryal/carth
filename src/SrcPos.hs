module SrcPos
    ( SourcePos(..)
    , WithPos(..)
    , HasPos(..)
    , onPosd
    , unpos
    , dummyPos
    , sourcePosPretty
    )
where

import Text.Megaparsec.Pos

import Misc

data WithPos a = WithPos SourcePos a

instance Show a => Show (WithPos a) where
    showsPrec p (WithPos _ a) = showsPrec p a
instance Eq a => Eq (WithPos a) where
    (WithPos _ a) == (WithPos _ b) = a == b
instance Ord a => Ord (WithPos a) where
    compare (WithPos _ a) (WithPos _ b) = compare a b
instance Pretty a => Pretty (WithPos a) where
    pretty' d = pretty' d . unpos

class HasPos a where
    getPos :: a -> SourcePos

instance HasPos (WithPos a) where
    getPos (WithPos p _) = p

onPosd :: (a -> b) -> WithPos a -> b
onPosd f = f . unpos

unpos :: WithPos a -> a
unpos (WithPos _ a) = a

dummyPos :: SourcePos
dummyPos = initialPos "DUMMY"
