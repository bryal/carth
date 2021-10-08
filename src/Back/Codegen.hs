{-# LANGUAGE DuplicateRecordFields, GADTs, RankNTypes #-}

-- | Generation of LLVM IR code from our monomorphic AST.
module Back.Codegen (codegen) where

import LLVM.Prelude
import LLVM.AST hiding (args)
import LLVM.AST.DataLayout
import Data.String
import System.FilePath
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Vector as Vec

import Misc
import Sizeof (variantsTagSize)
import qualified Back.Low as Low
import Back.Low hiding (Type, Const)

codegen :: FilePath -> Program -> DataLayout -> ShortByteString -> Module
codegen moduleFilePath (Program fs es gs ts vs) layout triple = Module
    { moduleName = fromString (takeBaseName moduleFilePath)
    , moduleSourceFileName = fromString moduleFilePath
    , moduleDataLayout = Just layout
    , moduleTargetTriple = Just triple
    , moduleDefinitions = concat
                              [ defineTypes ts
                              , declareExterns es
                              , declareGlobals gs
                              , defineFunctions fs
                              , defineInit gs
                              , defineMain
                              ]
    }

-- | How the different sorts of types are represented in LLVM:
--
--   A Unit is represented by a zero-sized array. The reason for using an array is that
--   LLVM did some "optimization" on empty structs that broke tail recursion when the
--   return type was a zero sized type.
--
--   An Enum is represented as the smallest integer type that can fit all variants.
--
--   A Data is represented by a struct that consists of 2 members: an integer that can fit
--   the variant index as well as "fill" the succeeding space (implied by alignment) until
--   the second member starts, followed by the second member which is an array of integers
--   with integer size equal to the alignment of the greatest aligned variant and array
--   length equal to the smallest n that results in the array being of size >= the size of
--   the largest sized variant.
--
--   The reason we must make sure to "fill" all space in the representing struct is that
--   LLVM may essentially otherwise incorrectly assume that the space is unused and
--   doesn't have to be considered passing the type as an argument to a function.
--
--   The reason we fill it with values the size of the alignment instead of bytes is to
--   not wrongfully signal to LLVM that the padding will be used as-is, and should be
--   passed/returned in its own registers (or whatever exactly is going on). I just know
--   from trial and error when debugging issues with how the representation of `(Maybe
--   Int8)` affects how it is returned from a function. The intuitive definition (which
--   indeed could be used for `Maybe` specifically without problems, since the only other
--   variant is the non-data-carrying `None`) is `{i8, i64}`. Representing it instead with
--   `{i64, i64}` (to make alignment-induced padding explicit, also this is how Rust
--   represents it) works well -- it seems to be passed/returned in exactly the same
--   way. However, if we represent it as `{i8, [7 x i8], i64}` or `{i8, [15 x i8], [0 x
--   i64]}`: while having the same size and alignment, it is not returned in the same way
--   (seeming instead to use an additional return parameter), and as such, a Carth
--   function returning `(Maybe Int8)` represented as `{i8, [15 x i8], [0 x i64]}` is not
--   ABI compatible with a Rust function returning `Maybe<i8>` represented as `{i64,
--   i64}`.
defineTypes :: TypeDefs -> [Definition]
defineTypes = (=<<) define . Vec.toList
  where
    define :: TypeDef -> [Definition]
    define = \case
        Enum _ _ -> []
        Struct name ms ->
            [TypeDefinition (mkName name) (Just (structType (map genType ms)))]
        Data' (Data name vs aMax sMax) ->
            let sTag = max (fromJust (variantsTagSize vs)) aMax
                tag = IntegerType (8 * fromIntegral sTag)
                fill = ArrayType (fromIntegral (div (sMax + aMax - 1) aMax))
                                 (IntegerType (8 * fromIntegral aMax))
            in  [TypeDefinition (mkName name) (Just (structType [tag, fill]))]

declareExterns :: [ExternDecl] -> [Definition]
declareExterns = _

declareGlobals :: [GlobDef] -> [Definition]
declareGlobals = _

defineFunctions :: [FunDef] -> [Definition]
defineFunctions = _

defineInit :: [GlobDef] -> [Definition]
defineInit = _

defineMain :: [Definition]
defineMain = _

genType :: Low.Type -> Type
genType = _

structType :: [Type] -> Type
structType ts = StructureType { isPacked = False, elementTypes = ts }

