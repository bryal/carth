{-# LANGUAGE OverloadedStrings, LambdaCase, TemplateHaskell, TupleSections
  , FlexibleContexts #-}

module Codegen where

import LLVM.AST
import LLVM.AST.Typed
import qualified LLVM.AST.CallingConvention as LLCallConv
import qualified LLVM.AST.Linkage as LLLink
import qualified LLVM.AST.Visibility as LLVis
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

type Env = Map Mono.TypedVar Operand

data St = St
    { _currentBlockLabel :: Name
    , _currentBlockInstrs :: [Named Instruction]
    , _registerCount :: Word
    }
makeLenses ''St

type Gen' = StateT St (Reader Env)

type Gen = WriterT [BasicBlock] Gen'

callConv :: LLCallConv.CallingConvention
callConv = LLCallConv.C

runGen' :: Gen' a -> a
runGen' g = runReader (evalStateT g initSt) Map.empty

semiRunGen :: Gen a -> Gen' [BasicBlock]
semiRunGen = execWriterT

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
    , moduleDefinitions = runGen' (genMain main) : runGen' (genGlobDefs defs)
    }

genMain :: Mono.MExpr -> Gen' Definition
genMain main = semiRunGen (genExpr main) <&> \blocks -> GlobalDefinition
    (functionDefaults
        { LLGlob.name = "main"
        , LLGlob.parameters = ([], False)
        , LLGlob.returnType = VoidType
        , LLGlob.basicBlocks = blocks
        }
    )

genGlobDefs :: Mono.Defs -> Gen' [Definition]
genGlobDefs (Mono.Defs defs) =
    let defs' = Map.toList defs in withGlobDefSigs defs' (mapM genGlobDef defs')

genGlobDef :: (Mono.TypedVar, Mono.MExpr) -> Gen' Definition
genGlobDef (Mono.TypedVar n t, e) = case (t, e) of
    (Mono.TFun _ rt, An.Fun p body) ->
        fmap GlobalDefinition (genFunDef (mkName n) p rt body)
    (t, _) -> ice $ "genDef of non-function " ++ show t

genFunDef
    :: Name -> (String, Mono.Type) -> Mono.Type -> Mono.MExpr -> Gen' Global
genFunDef name (p, pt) rt body = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    basicBlocks <- semiRunGen (genExpr body)
    pure $ Function
        { LLGlob.linkage = LLLink.External
        , LLGlob.visibility = LLVis.Default
        , LLGlob.dllStorageClass = Nothing
        , LLGlob.callingConvention = callConv
        , LLGlob.returnAttributes = []
        , LLGlob.returnType = toLlvmType rt
        , LLGlob.name = name
        , LLGlob.parameters = ([toLlvmParameter p pt], False)
        , LLGlob.functionAttributes = []
        , LLGlob.section = Nothing
        , LLGlob.comdat = Nothing
        , LLGlob.alignment = 0
        , LLGlob.garbageCollectorName = Nothing
        , LLGlob.prefix = Nothing
        , LLGlob.basicBlocks = basicBlocks
        , LLGlob.personalityFunction = Nothing
        , LLGlob.metadata = []
        }

toLlvmParameter :: String -> Mono.Type -> LLGlob.Parameter
toLlvmParameter p pt = LLGlob.Parameter (toLlvmType pt) (mkName p) []

withGlobDefSigs
    :: MonadReader Env m => [(Mono.TypedVar, Mono.MExpr)] -> m a -> m a
withGlobDefSigs = local . Map.union . Map.fromList . map
    (\(v@(Mono.TypedVar n t), _) -> (v, globRefOp (toLlvmType t) (mkName n)))
    where globRefOp t n = ConstantOperand (LLConst.GlobalReference t n)

genExpr :: Mono.MExpr -> Gen Operand
genExpr = \case
    An.Lit c -> pure (ConstantOperand (toLlvmConstant c))
    An.Var x t -> lookupVar (Mono.TypedVar x t)
    An.App f e -> emitAnon =<< liftA2 call (genExpr f) (genExpr e)
    An.If p c a -> genIf p c a
    An.Fun _ _ -> undefined
    An.Let ds b -> genLet ds b

toLlvmType :: Mono.Type -> Type
toLlvmType = \case
    Mono.TConst "Unit" -> StructureType {isPacked = False, elementTypes = []}
    Mono.TConst "Int" -> IntegerType 64
    Mono.TConst "Double" -> FloatingPointType DoubleFP
    Mono.TConst "Char" -> IntegerType 32
    Mono.TConst "Str" -> undefined
    Mono.TConst "Bool" -> IntegerType 1
    Mono.TConst c -> ice $ "toLlvmType of undefined type " ++ c
    Mono.TFun a r -> FunctionType
        { resultType = toLlvmType r
        , argumentTypes = [toLlvmType a]
        , isVarArg = False
        }

toLlvmConstant :: An.Const -> LLConst.Constant
toLlvmConstant = \case
    An.Unit -> litStruct []
    An.Int n -> litI64 n
    An.Double x -> litDouble x
    An.Char c -> litI32 (Data.Char.ord c)
    An.Str _ -> undefined
    An.Bool b -> litBool b

lookupVar :: Mono.TypedVar -> Gen Operand
lookupVar x =
    asks (fromMaybe (ice $ "Undefined variable " ++ show x) . Map.lookup x)

genIf :: Mono.MExpr -> Mono.MExpr -> Mono.MExpr -> Gen Operand
genIf pred conseq alt = do
    conseqL <- newName "consequent"
    altL <- newName "alternative"
    nextL <- newName "next"
    predV <- genExpr pred
    commitToNewBlock (condbr predV conseqL altL) conseqL
    conseqV <- genExpr conseq
    fromConseqL <- use currentBlockLabel
    commitToNewBlock (br nextL) altL
    altV <- genExpr alt
    fromAltL <- use currentBlockLabel
    commitToNewBlock (br nextL) nextL
    emitAnon (phi [(conseqV, fromConseqL), (altV, fromAltL)])

genLet :: Mono.Defs -> Mono.MExpr -> Gen Operand
genLet (Mono.Defs ds) b = do
    let (vs, es) = unzip (Map.toList ds)
    let (ns, ts) = unzip (map (\(Mono.TypedVar n t) -> (n, t)) vs)
    ns' <- mapM newName ns
    let ts' = map toLlvmType ts
    withDefSigs (zip vs ns') (mapM genDef (zip3 ns' ts' es) *> genExpr b)

withDefSigs :: [(Mono.TypedVar, Name)] -> Gen a -> Gen a
withDefSigs = local . Map.union . Map.fromList . map
    (\(v@(Mono.TypedVar _ t), n') -> (v, LocalReference (toLlvmType t) n'))

genDef :: (Name, Type, Mono.MExpr) -> Gen ()
genDef (n, t, e) = genExpr e >>= genVar n t

genVar :: Name -> Type -> Operand -> Gen ()
genVar var t val = emitReg var (alloca t) >>= emit . store val

emit :: Instruction -> Gen ()
emit instr = emit' (Do instr)

emit' :: (Named Instruction) -> Gen ()
emit' = modifying currentBlockInstrs . (:)

emitReg :: Name -> FunInstruction -> Gen Operand
emitReg reg (WithRetType instr rt) = do
    emit' (reg := instr)
    pure (LocalReference rt reg)

emitAnon :: FunInstruction -> Gen Operand
emitAnon instr = newAnonRegister >>= flip emitReg instr

commitToNewBlock :: Terminator -> Name -> Gen ()
commitToNewBlock t l = do
    n <- use currentBlockLabel
    is <- uses currentBlockInstrs reverse
    tell [BasicBlock n is (Do t)]
    assign currentBlockLabel l
    assign currentBlockInstrs []

newAnonRegister :: Gen Name
newAnonRegister = fmap UnName (registerCount <<+= 1)

newName :: String -> Gen Name
newName = lift . newName'

newName' :: String -> Gen' Name
newName' s = fmap (mkName . (s ++) . show) (registerCount <<+= 1)

newCounted :: (Word -> a) -> Gen a
newCounted f = fmap f (registerCount <<+= 1)

condbr :: Operand -> Name -> Name -> Terminator
condbr c t f = CondBr c t f []

br :: Name -> Terminator
br = flip Br []

store :: Operand -> Operand -> Instruction
store srcVal destPtr = Store
    { volatile = False
    , address = destPtr
    , value = srcVal
    , maybeAtomicity = Nothing
    , alignment = 0
    , metadata = []
    }

phi :: [(Operand, Name)] -> FunInstruction
phi = \case
    [] -> ice "phi was given empty list of cases"
    cs@((op, _) : _) -> let t = typeOf op in WithRetType (Phi t cs []) t

call :: Operand -> Operand -> FunInstruction
call f a = WithRetType
    (Call
        { tailCallKind = Just Tail
        , callingConvention = callConv
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
