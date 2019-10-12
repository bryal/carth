module SrcPos
    ( SrcPos(..)
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

newtype SrcPos = SrcPos SourcePos
    deriving Show

data WithPos a = WithPos SrcPos a

instance Show a => Show (WithPos a) where
    showsPrec p (WithPos _ a) = showsPrec p a
instance Eq a => Eq (WithPos a) where
    (WithPos _ a) == (WithPos _ b) = a == b
instance Ord a => Ord (WithPos a) where
    compare (WithPos _ a) (WithPos _ b) = compare a b
instance Pretty a => Pretty (WithPos a) where
    pretty' d = pretty' d . unpos

class HasPos a where
    getPos :: a -> SrcPos

instance HasPos (WithPos a) where
    getPos (WithPos p _) = p

onPosd :: (a -> b) -> WithPos a -> b
onPosd f = f . unpos

unpos :: WithPos a -> a
unpos (WithPos _ a) = a

dummyPos :: SrcPos
dummyPos = SrcPos (initialPos "DUMMY")
