{-# LANGUAGE OverloadedStrings, LambdaCase, TemplateHaskell, TupleSections
  , FlexibleContexts #-}

module Codegen (codegen) where

import LLVM.Prelude (ShortByteString)
import LLVM.AST
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.Context
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.CallingConvention as LLCallConv
import qualified LLVM.AST.Linkage as LLLink
import qualified LLVM.AST.Visibility as LLVis
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Float as LLFloat
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.AddrSpace as LLAddr
import qualified LLVM.AST.FunctionAttribute as LLFnAttr
import qualified Data.Text.Prettyprint.Doc as Prettyprint
import qualified Codec.Binary.UTF8.String as UTF8.String
import LLVM.Pretty ()
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
import Data.Word
import Data.Foldable
import Data.List
import Data.Composition
import Control.Applicative
import Control.Lens
    ( makeLenses
    , modifying
    , scribe
    , (<<+=)
    , use
    , uses
    , assign
    , view
    , views
    , locally
    )

import Misc
import FreeVars
import qualified MonoAst
import MonoAst hiding (Type, Const)
import qualified SizeOf

-- | An instruction that returns a value. The name refers to the fact that a
--   mathematical function always returns a value, but an imperative procedure
--   may only produce side effects.
data FunInstruction = WithRetType Instruction Type

-- TODO: Either treat globals and locals separately - Globals behing pointers,
--       locals not - or treat them the same - stack alloc space for locals.
data Env = Env
    { _localEnv :: Map TypedVar Operand
    , _globalEnv :: Map TypedVar Operand
    , _ctx :: Context
    }
makeLenses ''Env

data St = St
    { _currentBlockLabel :: Name
    , _currentBlockInstrs :: [Named Instruction]
    , _registerCount :: Word
    }
makeLenses ''St

type Gen' = StateT St (ReaderT Env IO)

-- | The output of generating a function
data Out = Out
    { _outBlocks :: [BasicBlock]
    , _outStrings :: [(Name, String)]
    , _outFuncs :: [(Name, [TypedVar], TypedVar, Expr)]
    }
makeLenses ''Out

type Gen = WriterT Out Gen'


instance Semigroup Out where
    Out bs1 ss1 fs1 <> Out bs2 ss2 fs2 =
        Out (bs1 <> bs2) (ss1 <> ss2) (fs1 <> fs2)
instance Monoid Out where
    mempty = Out [] [] []

instance Pretty Type where
    pretty' _ = show . Prettyprint.pretty
instance Pretty Name where
    pretty' _ = show . Prettyprint.pretty
instance Pretty Module where
    pretty' _ = show . Prettyprint.pretty


codegen :: Context -> FilePath -> Program -> IO Module
codegen context moduleFilePath (Program main (Defs defs) tdefs) = do
    let defs' = (TypedVar "main" mainType, main) : Map.toList defs
        genGlobDefs = withGlobDefSigs
            defs'
            (liftA2 (:) genOuterMain (fmap join (mapM genGlobDef defs')))
    globDefs <- runGen'
        context
        (liftA2 (++) (mapM genTypeDef tdefs) genGlobDefs)
    pure Module
        { moduleName = fromString ((takeBaseName moduleFilePath))
        , moduleSourceFileName = fromString moduleFilePath
        , moduleDataLayout = Just SizeOf.dataLayout
        , moduleTargetTriple = Nothing
        , moduleDefinitions = genBuiltins ++ globDefs
        }

runGen' :: Context -> Gen' a -> IO a
runGen' c g = runReaderT
    (evalStateT g initSt)
    Env { _localEnv = Map.empty, _globalEnv = Map.empty, _ctx = c }

initSt :: St
initSt = St
    { _currentBlockLabel = "entry"
    , _currentBlockInstrs = []
    , _registerCount = 0
    }

-- TODO: Will probably change type of variant-index. Update to reflect this.
-- | A data-type is a tagged union, and is represented in LLVM as a struct where
--   the first element is the variant-index as an i64, and the rest of the
--   elements are the field-types of the largest variant wrt allocation size.
genTypeDef :: (TConst, [[MonoAst.Type]]) -> Gen' Definition
genTypeDef (lhs, variants) = do
    let name = mkName (mangleTConst lhs)
    let ts = map toLlvmVariantType variants
    sizedTs <- mapM (\t -> fmap (, t) (sizeof t)) ts
    let (_, tmax) = maximum sizedTs
    pure (TypeDefinition name (Just tmax))

genBuiltins :: [Definition]
genBuiltins = map
    (GlobalDefinition . ($ []))
    [ simpleFunc
        (mkName "malloc")
        [parameter (mkName "size") i64]
        (LLType.ptr typeUnit)
    , simpleFunc' (mkName "abort") [] typeUnit [LLFnAttr.NoReturn]
    , simpleFunc (mkName "printInt") [parameter (mkName "n") i64] typeUnit
    ]

genOuterMain :: Gen' Definition
genOuterMain = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    (_, Out basicBlocks _ _) <- semiExecRetGen $ do
        f <- lookupVar (TypedVar "main" mainType)
        _ <- app f (ConstantOperand litUnit)
        pure (ConstantOperand (litI32 0))
    pure (GlobalDefinition (simpleFunc (mkName "main") [] i32 basicBlocks))

genGlobDef :: (TypedVar, Expr) -> Gen' [Definition]
genGlobDef (v, e) = case e of
    Fun p (body, _) ->
        fmap (map GlobalDefinition) (genClosureWrappedFunDef v p body)
    _ -> nyi $ "Global non-function defs: " ++ show e

genClosureWrappedFunDef :: TypedVar -> TypedVar -> Expr -> Gen' [Global]
genClosureWrappedFunDef var p body = do
    let name = mangleName var
    fName <- newName'' (unName name `mappend` fromString "_func")
    (f, gs) <- genFunDef' (fName, [], p, body)
    let fRef = LLConst.GlobalReference (LLType.ptr (typeOf f)) fName
    let capturesType = LLType.ptr typeUnit
    let captures = LLConst.Null capturesType
    let closure = litStruct [captures, fRef]
    let closureDef = simpleGlobVar name (typeOf closure) closure
    pure (closureDef : f : gs)

genFunDef :: (Name, [TypedVar], TypedVar, Expr) -> Gen' [Global]
genFunDef = fmap (uncurry (:)) . genFunDef'

genFunDef' :: (Name, [TypedVar], TypedVar, Expr) -> Gen' (Global, [Global])
genFunDef' (name, fvs, (TypedVar p pt), body) = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []

    capturesName <- newName' "captures"
    let capturesType = LLType.ptr typeUnit
    let capturesRef = LocalReference capturesType capturesName

    let ptv = TypedVar p pt
    let pt' = toLlvmType pt
    p' <- newName' p
    let pRef = LocalReference pt' p'

    (rt, Out basicBlocks globStrings lambdaFuncs) <- semiExecRetGen
        (withVar ptv pRef (genExtractCaptures capturesRef fvs (genExpr body)))

    let ss = map globStrVar globStrings
    ls <- concat <$> mapM genFunDef lambdaFuncs

    let fParams = [parameter capturesName capturesType, parameter p' pt']
    let f = simpleFunc name fParams rt basicBlocks

    pure (f, ss ++ ls)

genExtractCaptures :: Operand -> [TypedVar] -> Gen a -> Gen a
genExtractCaptures capturesPtrGeneric fvs ga = if null fvs
    then ga
    else do
        let capturesType = typeCaptures fvs
        capturesPtr <- emitAnon
            (bitcast capturesPtrGeneric (LLType.ptr capturesType))
        captures <- emitAnon (load capturesPtr)
        captureVals <- mapM
            (\(TypedVar x _, i) -> emitReg' x (extractvalue captures [i]))
            (zip fvs [0 ..])
        withVars (zip fvs captureVals) ga

genExpr :: Expr -> Gen Operand
genExpr = \case
    Lit c -> fmap ConstantOperand (genConst c)
    Var (TypedVar x t) -> lookupVar (TypedVar x t)
    App f e -> genApp f e
    If p c a -> genIf p c a
    Fun p b -> genLambda p b
    Let ds b -> genLet ds b
    Match e cs -> genMatch e cs
    Ction c -> genCtion c

toLlvmDataType :: MonoAst.TConst -> Type
toLlvmDataType = typeNamed . mangleTConst

toLlvmVariantType :: [MonoAst.Type] -> Type
toLlvmVariantType = typeStruct . (i64 :) . map toLlvmType

-- | Convert to the LLVM representation of a type in an expression-context.
toLlvmType :: MonoAst.Type -> Type
toLlvmType = \case
    TPrim tc -> case tc of
        TUnit -> typeUnit
        TInt -> i64
        TDouble -> double
        TChar -> i32
        TStr -> LLType.ptr i8
        TBool -> typeBool
    TFun a r -> typeStruct
        [ LLType.ptr typeUnit
        , LLType.ptr (typeClosureFun (toLlvmType a) (toLlvmType r))
        ]
    TConst t -> typeNamed (mangleTConst t)

genConst :: MonoAst.Const -> Gen LLConst.Constant
genConst = \case
    Unit -> pure litUnit
    Int n -> pure $ litI64 n
    Double x -> pure $ litDouble x
    Char c -> pure $ litI32 (Data.Char.ord c)
    Str s -> do
        var <- newName "strlit"
        scribe outStrings [(var, s)]
        pure $ LLConst.GlobalReference (LLType.ptr i8) var
    Bool b -> pure $ litBool b

lookupVar :: TypedVar -> Gen Operand
lookupVar x = do
    mayLocal <- views localEnv (Map.lookup x)
    mayGlobPtr <- views globalEnv (Map.lookup x)
    case (mayLocal, mayGlobPtr) of
        (Just local, _) -> pure local
        (Nothing, Just globPtr) -> emitAnon $ load globPtr
        (Nothing, Nothing) -> ice $ "Undefined variable " ++ show x

genApp :: Expr -> Expr -> Gen Operand
genApp fe ae = do
    a <- genExpr ae
    case fe of
        Var (TypedVar "printInt" _) ->
            emitAnon (callExtern "printInt" typeUnit [a])
        _ -> do
            closure <- genExpr fe
            app closure a

app :: Operand -> Operand -> Gen Operand
app closure arg = do
    captures <- emitReg' "captures" (extractvalue closure [0])
    f <- emitReg' "function" (extractvalue closure [1])
    emitAnon $ call f [captures, arg]

genIf :: Expr -> Expr -> Expr -> Gen Operand
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

genLet :: Defs -> Expr -> Gen Operand
genLet (Defs ds) b = do
    let (vs, es) = unzip (Map.toList ds)
    let (ns, ts) = unzip (map (\(TypedVar n t) -> (n, t)) vs)
    ns' <- mapM newName ns
    let ts' = map toLlvmType ts
    withDefSigs (zip vs ns') (mapM genDef (zip3 ns' ts' es) *> genExpr b)

genMatch :: Expr -> [(Pat, Expr)] -> Gen Operand
genMatch m cs = do
    m' <- genExpr m
    nextL <- newName "next"
    nextCaseLs <- replicateM (length cs - 1) (newName "next_case")
    noMatchL <- newName "no_match"
    cs' <- zipWithM (genCase m' nextL) (nextCaseLs ++ [noMatchL]) cs
    -- If we fell through the last case, the pattern was nonexhaustive and we're
    -- in a failure state. Only thing to do now is panic!
    genAbort
    commitToNewBlock unreachable nextL
    emitAnon (phi cs')

genCase :: Operand -> Name -> Name -> (Pat, Expr) -> Gen (Operand, Name)
genCase m nextL nextCaseL (p, b) = do
    defs <- genMatchPattern nextCaseL m p
    b' <- withDefSigs defs (genExpr b)
    l <- use currentBlockLabel
    commitToNewBlock (br nextL) nextCaseL
    pure (b', l)

genMatchPattern :: Name -> Operand -> Pat -> Gen [(TypedVar, Name)]
genMatchPattern nextCaseL m = \case
    PConstruction i ts ps -> do
        let tvariant = toLlvmVariantType ts
        let i' = litU64' i
        j <- emitReg' "found_variant_ix" (extractvalue m [0])
        isMatch <- emitReg' "is_match" (icmp LLIntPred.EQ i' j)
        subpatsL <- newName "subpats"
        commitToNewBlock (condbr isMatch subpatsL nextCaseL) subpatsL
        let tgeneric = typeOf m
        pGeneric <- emitReg' "ction_ptr_generic" (alloca tgeneric)
        emit (store m pGeneric)
        p <- emitReg' "ction_ptr" (bitcast pGeneric (LLType.ptr tvariant))
        m' <- emitReg' "ction" (load p)
        genMatchPatterns nextCaseL m' ps
    PVar var@(TypedVar x t) -> do
        n <- newName x
        genVar n (toLlvmType t) m
        pure [(var, n)]

genMatchPatterns :: Name -> Operand -> [Pat] -> Gen [(TypedVar, Name)]
genMatchPatterns nextCaseL m ps =
    let
        f vsAcc (i, p) = do
            sm <- emitReg' "submatchee" (extractvalue m [i])
            vs <- genMatchPattern nextCaseL sm p
            pure (vs ++ vsAcc)
    in foldM f [] (zip [1 ..] ps)

genCtion :: MonoAst.Ction -> Gen Operand
genCtion (i, tdef, as) = do
    let i' = litU64' i
    as' <- mapM genExpr as
    s <- genStruct (i' : as')
    let t = typeOf s
    let tgeneric = toLlvmDataType tdef
    pGeneric <- emitReg' "ction_ptr_generic" (alloca tgeneric)
    p <- emitReg' "ction_ptr" (bitcast pGeneric (LLType.ptr t))
    emit (store s p)
    emitReg' "ction_generic" (load pGeneric)

withDefSigs :: [(TypedVar, Name)] -> Gen a -> Gen a
withDefSigs = augment localEnv . Map.fromList . map
    (\(v@(TypedVar _ t), n') -> (v, LocalReference (toLlvmType t) n'))

-- TODO: Change global defs to a new type that can be generated by llvm.  As it
--       is now, global non-function variables can't be straight-forwardly
--       generated in general. Either, initialization is delayed until program
--       start, or an interpretation step is added between monomorphization and
--       codegen that evaluates all expressions in relevant contexts, like
--       constexprs.
genDef :: (Name, Type, Expr) -> Gen ()
genDef (n, t, e) = genExpr e >>= genVar n t

genVar :: Name -> Type -> Operand -> Gen ()
genVar var t val = emitReg var (alloca t) >>= emit . store val

-- | A lambda is a pair of a captured environment and a function.  The captured
--   environment must be on the heap, since the closure value needs to be of
--   some specific size, regardless of what the closure captures, so that
--   closures of same types but different captures can be used interchangeably.
--
--   The first parameter of the function is a pointer to an environment of
--   captures and the second parameter is the lambda parameter.
--
--   Inside of the function, first all the captured variables are extracted from
--   the environment, then the body of the function is run.
genLambda :: TypedVar -> (Expr, MonoAst.Type) -> Gen Operand
genLambda p@(TypedVar px pt) (b, bt) = do
    let fvs = Set.toList (Set.delete (TypedVar px pt) (freeVars b))
    captures <- genBoxGeneric =<< genStruct =<< sequence (map lookupVar fvs)
    fname <- newName "lambda_func"
    let ft = typeClosureFun (toLlvmType pt) (toLlvmType bt)
    let f = ConstantOperand (LLConst.GlobalReference (LLType.ptr ft) fname)
    scribe outFuncs [(fname, fvs, p, b)]
    genStruct [captures, f]

genStruct :: [Operand] -> Gen Operand
genStruct xs = do
    let t = typeStruct (map typeOf xs)
    foldlM
        (\s (i, x) -> emitReg' "acc" (insertvalue s x [i]))
        (ConstantOperand (LLConst.Undef t))
        (zip [0 ..] xs)

genBoxGeneric :: Operand -> Gen Operand
genBoxGeneric x = do
    let t = typeOf x
    ptrGeneric <- genMalloc =<< genSizeof t
    ptr <- emitAnon (bitcast ptrGeneric (LLType.ptr t))
    emit (store x ptr)
    pure ptrGeneric

genMalloc :: Operand -> Gen Operand
genMalloc size = emitAnon (callExtern "malloc" (LLType.ptr typeUnit) [size])

genAbort :: Gen ()
genAbort = emit (callExtern' "abort" [])

semiExecRetGen :: Gen Operand -> Gen' (Type, Out)
semiExecRetGen gx = runWriterT $ do
    x <- gx
    commitFinalFuncBlock (ret x)
    pure (typeOf x)

globStrVar :: (Name, String) -> Global
globStrVar (name, str) =
    let bytes = UTF8.String.encode str
    in
        simpleGlobVar
            name
            (ArrayType (fromIntegral (length bytes)) i8)
            (LLConst.Array i8 (map (litI8) bytes))

simpleFunc :: Name -> [Parameter] -> Type -> [BasicBlock] -> Global
simpleFunc = ($ []) .** simpleFunc'

simpleFunc'
    :: Name
    -> [Parameter]
    -> Type
    -> [LLFnAttr.FunctionAttribute]
    -> [BasicBlock]
    -> Global
simpleFunc' n ps rt fnAttrs bs = Function
    { LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.callingConvention = callConv
    , LLGlob.returnAttributes = []
    , LLGlob.returnType = rt
    , LLGlob.name = n
    , LLGlob.parameters = (ps, False)
    , LLGlob.functionAttributes = map Right fnAttrs
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.garbageCollectorName = Nothing
    , LLGlob.prefix = Nothing
    , LLGlob.basicBlocks = bs
    , LLGlob.personalityFunction = Nothing
    , LLGlob.metadata = []
    }

simpleGlobVar :: Name -> Type -> LLConst.Constant -> Global
simpleGlobVar name t init = GlobalVariable
    { LLGlob.name = name
    , LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.threadLocalMode = Nothing
    , LLGlob.addrSpace = LLAddr.AddrSpace 0
    , LLGlob.unnamedAddr = Nothing
    , LLGlob.isConstant = True
    , LLGlob.type' = t
    , LLGlob.initializer = Just init
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.metadata = []
    }

parameter :: Name -> Type -> LLGlob.Parameter
parameter p pt = LLGlob.Parameter pt p []

genSizeof :: Type -> Gen Operand
genSizeof = fmap litU64' . sizeof'

sizeof' :: Type -> Gen Word64
sizeof' = lift . sizeof

sizeof :: Type -> Gen' Word64
sizeof t = do
    c <- view ctx
    liftIO (SizeOf.sizeof c t)

withGlobDefSigs :: MonadReader Env m => [(TypedVar, Expr)] -> m a -> m a
withGlobDefSigs = augment globalEnv . Map.fromList . map
    (\(v@(TypedVar _ t), _) ->
        ( v
        , ConstantOperand
            (LLConst.GlobalReference (LLType.ptr (toLlvmType t)) (mangleName v))
        )
    )

withVars :: [(TypedVar, Operand)] -> Gen a -> Gen a
withVars = flip (foldr (uncurry withVar))

withVar :: TypedVar -> Operand -> Gen a -> Gen a
withVar x v = locally localEnv (Map.insert x v)

emit :: Instruction -> Gen ()
emit instr = emit' (Do instr)

emit' :: (Named Instruction) -> Gen ()
emit' = modifying currentBlockInstrs . (:)

emitReg :: Name -> FunInstruction -> Gen Operand
emitReg reg (WithRetType instr rt) = do
    emit' (reg := instr)
    pure (LocalReference rt reg)

emitReg' :: String -> FunInstruction -> Gen Operand
emitReg' s instr = newName s >>= flip emitReg instr

emitAnon :: FunInstruction -> Gen Operand
emitAnon instr = newAnonRegister >>= flip emitReg instr

commitFinalFuncBlock :: Terminator -> Gen ()
commitFinalFuncBlock t = commitToNewBlock
    t
    (ice "Continued gen after final block of function was already commited")

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

newName'' :: ShortByteString -> Gen' Name
newName'' s =
    fmap (Name . (mappend s) . fromString . show) (registerCount <<+= 1)

-- TODO: Shouldn't need a return type parameter. Should look at global list of
--       hidden builtins or something.
callExtern :: String -> Type -> [Operand] -> FunInstruction
callExtern f rt as = WithRetType (callExtern'' f rt as) rt

callExtern' :: String -> [Operand] -> Instruction
callExtern' f as = callExtern'' f typeUnit as

callExtern'' :: String -> Type -> [Operand] -> Instruction
callExtern'' f rt as = Call
    { tailCallKind = Just Tail
    , callingConvention = callConv
    , returnAttributes = []
    , function = Right $ ConstantOperand $ LLConst.GlobalReference
        (LLType.ptr (FunctionType rt (map typeOf as) False))
        (mkName f)
    , arguments = map (, []) as
    , functionAttributes = []
    , metadata = []
    }

condbr :: Operand -> Name -> Name -> Terminator
condbr c t f = CondBr c t f []

br :: Name -> Terminator
br = flip Br []

ret :: Operand -> Terminator
ret = flip Ret [] . Just

unreachable :: Terminator
unreachable = Unreachable []

bitcast :: Operand -> Type -> FunInstruction
bitcast x t = WithRetType (BitCast x t []) t

insertvalue :: Operand -> Operand -> [Word32] -> FunInstruction
insertvalue s e is = WithRetType (InsertValue s e is []) (typeOf s)

extractvalue :: Operand -> [Word32] -> FunInstruction
extractvalue struct is = WithRetType
    (ExtractValue { aggregate = struct, indices' = is, metadata = [] })
    (getIndexed (typeOf struct) is)

store :: Operand -> Operand -> Instruction
store srcVal destPtr = Store
    { volatile = False
    , address = destPtr
    , value = srcVal
    , maybeAtomicity = Nothing
    , alignment = 0
    , metadata = []
    }

load :: Operand -> FunInstruction
load p = WithRetType
    (Load
        { volatile = False
        , address = p
        , maybeAtomicity = Nothing
        , alignment = 0
        , metadata = []
        }
    )
    (getPointee (typeOf p))

phi :: [(Operand, Name)] -> FunInstruction
phi = \case
    [] -> ice "phi was given empty list of cases"
    cs@((op, _) : _) -> let t = typeOf op in WithRetType (Phi t cs []) t

call :: Operand -> [Operand] -> FunInstruction
call f as = WithRetType
    (Call
        { tailCallKind = Just Tail
        , callingConvention = callConv
        , returnAttributes = []
        , function = Right f
        , arguments = map (, []) as
        , functionAttributes = []
        , metadata = []
        }
    )
    (getFunRet (getPointee (typeOf f)))

alloca :: Type -> FunInstruction
alloca t = WithRetType (Alloca t Nothing 0 []) t

icmp :: LLIntPred.IntegerPredicate -> Operand -> Operand -> FunInstruction
icmp p a b = WithRetType (ICmp p a b []) typeBool

litU64' :: Word64 -> Operand
litU64' = ConstantOperand . litU64

litU64 :: Word64 -> LLConst.Constant
litU64 = litI64 . fromIntegral

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

litUnit :: LLConst.Constant
litUnit = litStruct []

typeClosureFun :: Type -> Type -> Type
typeClosureFun pt rt = FunctionType
    { resultType = rt
    , argumentTypes = [LLType.ptr (typeCaptures []), pt]
    , isVarArg = False
    }

typeCaptures :: [TypedVar] -> Type
typeCaptures = typeStruct . map (\(TypedVar _ t) -> toLlvmType t)

typeNamed :: String -> Type
typeNamed = NamedTypeReference . mkName

typeStruct :: [Type] -> Type
typeStruct ts = StructureType { isPacked = False, elementTypes = ts }

typeBool :: Type
typeBool = i1

typeUnit :: Type
typeUnit = StructureType { isPacked = False, elementTypes = [] }

getFunRet :: Type -> Type
getFunRet = \case
    FunctionType rt _ _ -> rt
    t -> ice $ "Tried to get return type of non-function type " ++ pretty t

getPointee :: Type -> Type
getPointee = \case
    LLType.PointerType t _ -> t
    t -> ice $ "Tried to get pointee of non-function type " ++ pretty t

getMembers :: Type -> [Type]
getMembers = \case
    StructureType _ members -> members
    t -> ice $ "Tried to get member types of non-struct type " ++ pretty t

getIndexed :: Type -> [Word32] -> Type
getIndexed = foldl' (\t i -> getMembers t !! (fromIntegral i))

mangleName :: TypedVar -> Name
mangleName (TypedVar x t) = mkName (x ++ ":" ++ mangleType t)

mangleType :: MonoAst.Type -> String
mangleType = \case
    TPrim c -> pretty c
    TFun p r -> mangleTConst ("->", [p, r])
    TConst tc -> mangleTConst tc

mangleTConst :: TConst -> String
mangleTConst (c, ts) =
    concat ["(", c, ",", intercalate "," (map mangleType ts), ")"]

unName :: Name -> ShortByteString
unName = \case
    Name s -> s
    UnName n -> fromString (show n)

callConv :: LLCallConv.CallingConvention
callConv = LLCallConv.C
