{-# LANGUAGE LambdaCase, TemplateHaskell #-}

module Gen
    ( Gen
    , Gen'
    , Out(..)
    , outBlocks
    , outStrings
    , outFuncs
    , outSrcPos
    , St(..)
    , currentBlockLabel
    , currentBlockInstrs
    , registerCount
    , metadataCount
    , lambdaParentFunc
    , outerLambdaN
    , srcPosToMetadata
    , Env(..)
    , env
    , enumTypes
    , dataTypes
    , srcPos
    , lookupDatatype
    , typeUnit
    , typeStruct
    )
where

import LLVM.AST
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Word
import Lens.Micro.Platform (makeLenses, view, to)

import Misc
import SrcPos
import Monomorphic hiding (Type, Const)


data Env = Env
    -- TODO: Could operands in env be Val instead? I.e., either stack-allocated
    --       or local?
    { _env :: Map TypedVar Operand -- ^ Environment of stack allocated variables
    , _enumTypes :: Map Name Word32
    , _dataTypes :: Map Name [Type]
    , _srcPos :: Maybe SrcPos
    }
makeLenses ''Env

data St = St
    { _currentBlockLabel :: Name
    , _currentBlockInstrs :: [Named Instruction]
    , _registerCount :: Word
    , _metadataCount :: Word
    -- | Keep track of the parent function name so that we can name the
    --   outermost lambdas of a function definition well.
    , _lambdaParentFunc :: Maybe String
    , _outerLambdaN :: Word
    , _srcPosToMetadata :: Map SrcPos (MDRef MDNode)
    }
makeLenses ''St

type Gen' = StateT St (Reader Env)

-- | The output of generating a function. Dependencies of stuff within the
--   function that must be generated at the top-level.
data Out = Out
    { _outBlocks :: [BasicBlock]
    , _outStrings :: [(Name, String)]
    , _outFuncs :: [(Name, [TypedVar], SrcPos, TypedVar, Expr)]
    , _outSrcPos :: [(SrcPos, MetadataNodeID)]
    }
makeLenses ''Out

type Gen = WriterT Out Gen'


instance Semigroup Out where
    Out bs1 ss1 fs1 ps1 <> Out bs2 ss2 fs2 ps2 =
        Out (bs1 <> bs2) (ss1 <> ss2) (fs1 <> fs2) (ps1 <> ps2)
instance Monoid Out where
    mempty = Out [] [] [] []


lookupDatatype :: Name -> Gen' Type
lookupDatatype x = view (enumTypes . to (Map.lookup x)) >>= \case
    Just 0 -> pure (typeUnit)
    Just w -> pure (IntegerType w)
    Nothing -> fmap
        (maybe (ice ("Undefined datatype " ++ show x)) typeStruct)
        (view (dataTypes . to (Map.lookup x)))

typeUnit :: Type
typeUnit = typeStruct []

typeStruct :: [Type] -> Type
typeStruct ts = StructureType { isPacked = False, elementTypes = ts }
