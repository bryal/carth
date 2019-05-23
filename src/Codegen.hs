{-# LANGUAGE OverloadedStrings, LambdaCase, TemplateHaskell #-}

module Codegen where

import LLVM.AST
import LLVM.AST.Typed
import qualified LLVM.AST.CallingConvention
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Float as LLFloat
import qualified LLVM.AST.Global as LLGlob
import Data.String
import System.FilePath
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Char
import Data.Bool
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Functor
import Control.Applicative
import Data.Maybe
import Control.Lens (makeLenses, modifying, (<<+=), use, uses, assign)

import Misc
import qualified Annot as An
import qualified Mono

-- | An instruction that returns a value. The name refers to the fact that a
-- mathematical function always returns a value, but an imperative procedure may
-- only produce side effects.
data FunInstruction = WithRetType Instruction Type

type Env = Map String Operand

data St = St
    { _currentBlockLabel :: Name
    , _currentBlockInstrs :: [Named Instruction]
    , _registerCount :: Word
    }
makeLenses ''St

type Gen a = WriterT [BasicBlock] (StateT St (Reader Env)) a

semiRunGen :: Gen a -> Reader Env [BasicBlock]
semiRunGen g = evalStateT (execWriterT g) initSt

initSt :: St
initSt = St
    { _currentBlockLabel = "entry"
    , _currentBlockInstrs = []
    , _registerCount = 0
    }

genModule :: FilePath -> Mono.MExpr -> Mono.Defs -> Module
genModule moduleFilePath main defs = defaultModule
    { moduleName = fromString ((takeBaseName moduleFilePath))
    , moduleSourceFileName = fromString moduleFilePath
    , moduleDefinitions =
        runReader (genMain main) Map.empty : runReader (genDefs defs) Map.empty
    }

genMain :: Mono.MExpr -> Reader Env Definition
genMain main = semiRunGen (genExpr main) <&> \blocks -> GlobalDefinition
    (functionDefaults
        { LLGlob.name = "main"
        , LLGlob.parameters = ([], False)
        , LLGlob.returnType = VoidType
        , LLGlob.basicBlocks = blocks
        }
    )

genDefs :: Mono.Defs -> Reader Env [Definition]
genDefs defs = undefined defs

genExpr :: Mono.MExpr -> Gen Operand
genExpr = \case
    An.Lit c -> pure (ConstantOperand (toLlvmConstant c))
    An.Var x _ -> lookupVar x
    An.App f e -> emitAnon =<< liftA2 call (genExpr f) (genExpr e)
    An.If p c a -> genIf p c a
    An.Fun _ _ -> undefined
    An.Let _ _ -> undefined

toLlvmConstant :: An.Const -> LLConst.Constant
toLlvmConstant = \case
    An.Unit -> litStruct []
    An.Int n -> litI64 n
    An.Double x -> litDouble x
    An.Char c -> litI32 (Data.Char.ord c)
    An.Str _ -> undefined
    An.Bool b -> litBool b

lookupVar :: String -> Gen Operand
lookupVar x = asks (fromMaybe (ice $ "Undefined variable " ++ x) . Map.lookup x)

genIf :: Mono.MExpr -> Mono.MExpr -> Mono.MExpr -> Gen Operand
genIf pred conseq alt = do
    conseqL <- newLabel "consequent"
    altL <- newLabel "alternative"
    nextL <- newLabel "next"
    predV <- genExpr pred
    commitToNewBlock (condbr predV conseqL altL) conseqL
    conseqV <- genExpr conseq
    fromConseqL <- use currentBlockLabel
    commitToNewBlock (br nextL) altL
    altV <- genExpr alt
    fromAltL <- use currentBlockLabel
    commitToNewBlock (br nextL) nextL
    emitAnon (phi [(conseqV, fromConseqL), (altV, fromAltL)])

emitAnon :: FunInstruction -> Gen Operand
emitAnon (WithRetType instr rt) = do
    reg <- newAnonRegister
    modifying currentBlockInstrs ((reg := instr) :)
    pure (LocalReference rt reg)

commitToNewBlock :: Terminator -> Name -> Gen ()
commitToNewBlock t l = do
    n <- use currentBlockLabel
    is <- uses currentBlockInstrs reverse
    tell [BasicBlock n is (Do t)]
    assign currentBlockLabel l
    assign currentBlockInstrs []

newAnonRegister :: Gen Name
newAnonRegister = fmap UnName (registerCount <<+= 1)

newRegister :: String -> Gen Name
newRegister s = fmap (mkName . (s ++) . show) (registerCount <<+= 1)

newLabel :: String -> Gen Name
newLabel = newRegister

condbr :: Operand -> Name -> Name -> Terminator
condbr c t f = CondBr c t f []

br :: Name -> Terminator
br = flip Br []

phi :: [(Operand, Name)] -> FunInstruction
phi = \case
    [] -> ice "phi was given empty list of cases"
    cs@((op, _) : _) -> let t = typeOf op in WithRetType (Phi t cs []) t

call :: Operand -> Operand -> FunInstruction
call f a = WithRetType
    (Call
        { tailCallKind = Just Tail
        , callingConvention = LLVM.AST.CallingConvention.C
        , returnAttributes = []
        , function = Right f
        , arguments = [(a, [])]
        , functionAttributes = []
        , metadata = []
        }
    )
    (getFunRet (typeOf f))

alloca :: Type -> FunInstruction
alloca t = WithRetType (Alloca t Nothing 0 []) t

litI64 :: Int -> LLConst.Constant
litI64 = LLConst.Int 64 . toInteger

litI32 :: Int -> LLConst.Constant
litI32 = LLConst.Int 32 . toInteger

litBool :: Bool -> LLConst.Constant
litBool = LLConst.Int 1 . bool 1 0

litDouble :: Double -> LLConst.Constant
litDouble = LLConst.Float . LLFloat.Double

litStruct :: [LLConst.Constant] -> LLConst.Constant
litStruct = LLConst.Struct Nothing False

getFunRet :: Type -> Type
getFunRet = \case
    FunctionType rt _ _ -> rt
    t -> ice $ "Tried to get return type of non-function type " ++ show t
