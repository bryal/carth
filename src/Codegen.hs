{-# LANGUAGE OverloadedStrings, LambdaCase, TemplateHaskell, TupleSections
  , FlexibleContexts #-}

module Codegen where

import LLVM.AST
import LLVM.AST.Typed
import LLVM.AST.Type
import qualified LLVM.AST.CallingConvention as LLCallConv
import qualified LLVM.AST.Linkage as LLLink
import qualified LLVM.AST.Visibility as LLVis
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Float as LLFloat
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.AddrSpace as LLAddr
import qualified Codec.Binary.UTF8.String as UTF8.String
import Data.String
import System.FilePath
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Char
import Data.Bool
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Functor
import Control.Applicative
import Data.Maybe
import Control.Lens
    (makeLenses, modifying, view, scribe, (<<+=), use, uses, assign)

import Misc
import qualified Annot as An
import qualified Mono

-- | An instruction that returns a value. The name refers to the fact that a
-- mathematical function always returns a value, but an imperative procedure may
-- only produce side effects.
data FunInstruction = WithRetType Instruction Type

type Env = Map Mono.MTypedVar Operand

data St = St
    { _currentBlockLabel :: Name
    , _currentBlockInstrs :: [Named Instruction]
    , _registerCount :: Word
    }
makeLenses ''St

type Gen' = StateT St (Reader Env)

-- | The output of generating a function
data Out = Out
    { _outBlocks :: [BasicBlock]
    , _outStrings :: [(Name, String)]}
makeLenses ''Out

instance Semigroup Out where
    Out bs1 ss1 <> Out bs2 ss2 = Out (bs1 <> bs2) (ss1 <> ss2)

instance Monoid Out where
    mempty = Out [] []

type Gen = WriterT Out Gen'

callConv :: LLCallConv.CallingConvention
callConv = LLCallConv.C

runGen' :: Gen' a -> a
runGen' g = runReader (evalStateT g initSt) Map.empty

semiRunGen :: Gen a -> Gen' Out
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
    , moduleDefinitions =
        TypeDefinition (Name "str") (Just (ptr i8))
        : runGen' (genMain main)
        : runGen' (genGlobDefs defs)
    }

genMain :: Mono.MExpr -> Gen' Definition
genMain main = semiRunGen (genExpr main) <&> \out -> GlobalDefinition
    (functionDefaults
        { LLGlob.name = "main"
        , LLGlob.parameters = ([], False)
        , LLGlob.returnType = VoidType
        , LLGlob.basicBlocks = view outBlocks out
        }
    )

genGlobDefs :: Mono.Defs -> Gen' [Definition]
genGlobDefs (Mono.Defs defs) =
    let defs' = Map.toList defs
    in withGlobDefSigs defs' (fmap join (mapM genGlobDef defs'))

genGlobDef :: (Mono.MTypedVar, Mono.MExpr) -> Gen' [Definition]
genGlobDef (Mono.TypedVar n t, e) = case (t, e) of
    (Mono.TFun _ rt, An.Fun p body) ->
        fmap (map GlobalDefinition) (genFunDef (mkName n) p rt body)
    _ -> undefined

genFunDef
    :: Name -> (String, Mono.Type) -> Mono.Type -> Mono.MExpr -> Gen' [Global]
genFunDef name (p, pt) rt body = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    Out basicBlocks globStrings <- semiRunGen (genExpr body)
    let f = simpleFunc name [toLlvmParameter p pt] (toLlvmType rt) basicBlocks
    let ss = map globStrVar globStrings
    pure (f : ss)

simpleFunc :: Name -> [Parameter] -> Type -> [BasicBlock] -> Global
simpleFunc n ps rt bs = Function
    { LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.callingConvention = callConv
    , LLGlob.returnAttributes = []
    , LLGlob.returnType = rt
    , LLGlob.name = n
    , LLGlob.parameters = (ps, False)
    , LLGlob.functionAttributes = []
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.garbageCollectorName = Nothing
    , LLGlob.prefix = Nothing
    , LLGlob.basicBlocks = bs
    , LLGlob.personalityFunction = Nothing
    , LLGlob.metadata = []
    }

globStrVar :: (Name, String) -> Global
globStrVar (name, str) =
    let bytes = UTF8.String.encode str
    in
        GlobalVariable
            { LLGlob.name = name
            , LLGlob.linkage = LLLink.External
            , LLGlob.visibility = LLVis.Default
            , LLGlob.dllStorageClass = Nothing
            , LLGlob.threadLocalMode = Nothing
            , LLGlob.addrSpace = LLAddr.AddrSpace 0
            , LLGlob.unnamedAddr = Nothing
            , LLGlob.isConstant = True
            , LLGlob.type' = ArrayType (fromIntegral (length bytes)) i8
            , LLGlob.initializer = Just (LLConst.Array i8 (map (litI8) bytes))
            , LLGlob.section = Nothing
            , LLGlob.comdat = Nothing
            , LLGlob.alignment = 0
            , LLGlob.metadata = []
            }

toLlvmParameter :: String -> Mono.Type -> LLGlob.Parameter
toLlvmParameter p pt = LLGlob.Parameter (toLlvmType pt) (mkName p) []

withGlobDefSigs
    :: MonadReader Env m => [(Mono.MTypedVar, Mono.MExpr)] -> m a -> m a
withGlobDefSigs = local . Map.union . Map.fromList . map
    (\(v@(Mono.TypedVar n t), _) -> (v, globRefOp (toLlvmType t) (mkName n)))
    where globRefOp t n = ConstantOperand (LLConst.GlobalReference t n)

genExpr :: Mono.MExpr -> Gen Operand
genExpr = \case
    An.Lit c -> fmap ConstantOperand (genConst c)
    An.Var (An.TypedVar x t) -> lookupVar (An.TypedVar x t)
    An.App f e -> emitAnon =<< liftA2 call (genExpr f) (genExpr e)
    An.If p c a -> genIf p c a
    An.Fun p b -> genLambda p b
    An.Let ds b -> genLet ds b

toLlvmType :: Mono.Type -> Type
toLlvmType = \case
    Mono.TConst "Unit" -> StructureType {isPacked = False, elementTypes = []}
    Mono.TConst "Int" -> i64
    Mono.TConst "Double" -> double
    Mono.TConst "Char" -> i32
    Mono.TConst "Str" -> NamedTypeReference (Name "str")
    Mono.TConst "Bool" -> i1
    Mono.TConst c -> ice $ "toLlvmType of undefined type " ++ c
    Mono.TFun a r -> FunctionType
        { resultType = toLlvmType r
        , argumentTypes = [toLlvmType a]
        , isVarArg = False
        }

genConst :: An.Const -> Gen LLConst.Constant
genConst = \case
    An.Unit -> pure $ litStruct []
    An.Int n -> pure $ litI64 n
    An.Double x -> pure $ litDouble x
    An.Char c -> pure $ litI32 (Data.Char.ord c)
    An.Str s -> do
        var <- newName "strlit"
        scribe outStrings [(var, s)]
        pure $ LLConst.GlobalReference (NamedTypeReference (Name "str")) var
    An.Bool b -> pure $ litBool b

lookupVar :: Mono.MTypedVar -> Gen Operand
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

withDefSigs :: [(Mono.MTypedVar, Name)] -> Gen a -> Gen a
withDefSigs = local . Map.union . Map.fromList . map
    (\(v@(Mono.TypedVar _ t), n') -> (v, LocalReference (toLlvmType t) n'))

genDef :: (Name, Type, Mono.MExpr) -> Gen ()
genDef (n, t, e) = genExpr e >>= genVar n t

genVar :: Name -> Type -> Operand -> Gen ()
genVar var t val = emitReg var (alloca t) >>= emit . store val

-- | A lambda is a pair of a captured environment and a function.
--   The first parameter of the function is an environment of captures
--   and the second parameter is the lambda parameter.
--   Inside of the function, first all the captured variables are extracted from
--   the environment, then the body of the function is run.
genLambda :: (String, Mono.Type) -> Mono.MExpr -> Gen Operand
genLambda (p, pt) b = do
    let fvs = Set.delete (An.TypedVar p pt) (freeVars b)
    captures <- undefined fvs
    undefined p pt b captures

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
    scribe outBlocks [BasicBlock n is (Do t)]
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

litI8 :: Integral n => n -> LLConst.Constant
litI8 = LLConst.Int 32 . toInteger

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
