module SrcPos
    ( SrcPos(..)
    , SourcePos(..)
    , WithPos(..)
    , HasPos(..)
    , mapPos
    , unpos
    , unPos
    , dummyPos
    , sourcePosPretty
    )
where

import Text.Megaparsec.Pos


newtype SrcPos = SrcPos SourcePos
    deriving (Show, Eq, Ord)

data WithPos a = WithPos SrcPos a

class HasPos a where
    getPos :: a -> SrcPos


instance Show a => Show (WithPos a) where
    showsPrec p (WithPos _ a) = showsPrec p a
instance Eq a => Eq (WithPos a) where
    (WithPos _ a) == (WithPos _ b) = a == b
instance Ord a => Ord (WithPos a) where
    compare (WithPos _ a) (WithPos _ b) = compare a b

instance HasPos (WithPos a) where
    getPos (WithPos p _) = p

mapPos :: (a -> b) -> WithPos a -> WithPos b
mapPos f (WithPos p a) = WithPos p (f a)

unpos :: WithPos a -> a
unpos (WithPos _ a) = a

dummyPos :: SrcPos
dummyPos = SrcPos (initialPos "DUMMY")
