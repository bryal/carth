module Back.Lower (lower, builtinExterns) where

import Data.Map (Map)

import qualified Front.Monomorphic as Ast
import Back.Low -- hiding (StrLits)



lower :: Ast.Program -> Program
lower = undefined lowerDatas

-- | To generate cleaner code, a data-type is only represented as a tagged union (Data) if
--   it has to be. If there is only a single variant, we skip the tag and represent it as
--   a Struct. If the struct also has no members, we simplify it further and represent it
--   as a Unit. If instead the data-type has multiple variants, but no variant has any
--   members, it is represented as an Enum.
lowerDatas :: ()
lowerDatas = ()

builtinExterns :: Map String Type
builtinExterns = undefined
