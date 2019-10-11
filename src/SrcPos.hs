module SrcPos
    ( SourcePos(..)
    , WithPos(..)
    , onPosd
    , getPos
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

onPosd :: (a -> b) -> WithPos a -> b
onPosd f = f . unpos

getPos :: WithPos a -> SourcePos
getPos (WithPos p _) = p

unpos :: WithPos a -> a
unpos (WithPos _ a) = a

dummyPos :: SourcePos
dummyPos = initialPos "DUMMY"
