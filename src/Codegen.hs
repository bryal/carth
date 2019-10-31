{-# LANGUAGE OverloadedStrings, LambdaCase, TemplateHaskell, TupleSections
  , FlexibleContexts #-}

module Codegen (codegen) where

import LLVM.Prelude (ShortByteString)
import LLVM.AST
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.AST.DataLayout
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.CallingConvention as LLCallConv
import qualified LLVM.AST.Linkage as LLLink
import qualified LLVM.AST.Visibility as LLVis
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Float as LLFloat
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.AddrSpace as LLAddr
import qualified LLVM.AST.FunctionAttribute as LLFnAttr
import LLVM.Internal.DataLayout (withFFIDataLayout)
import LLVM.Internal.FFI.DataLayout (getTypeAllocSize)
import qualified LLVM.Internal.FFI.PtrHierarchy as LLPtrHierarchy
import LLVM.Internal.Coding (encodeM)
import LLVM.Internal.EncodeAST (EncodeAST, defineType)
import LLVM.Internal.Type (createNamedType, setNamedType)
import qualified Foreign.Ptr
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
    (makeLenses, modifying, scribe, (<<+=), use, uses, assign, views, locally)

import Misc
import FreeVars
import qualified MonoAst
import MonoAst hiding (Type, Const)
import Selections


type FFIType = Foreign.Ptr.Ptr LLPtrHierarchy.Type

-- | An instruction that returns a value. The name refers to the fact that a
--   mathematical function always returns a value, but an imperative procedure
--   may only produce side effects.
data FunInstruction = WithRetType Instruction Type

-- TODO: Either treat globals and locals separately - Globals behing pointers,
--       locals not - or treat them the same - stack alloc space for locals.
--       Update: They are both behind pointers now, right? So we could just have
--       a single map?
data Env = Env
    { _env :: Map TypedVar Operand
    , _dataLayout :: DataLayout
    }
makeLenses ''Env

data St = St
    { _currentBlockLabel :: Name
    , _currentBlockInstrs :: [Named Instruction]
    , _registerCount :: Word
    }
makeLenses ''St

type Gen' = StateT St (ReaderT Env EncodeAST)

-- | The output of generating a function
data Out = Out
    { _outBlocks :: [BasicBlock]
    , _outStrings :: [(Name, Word64, [Word8])]
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


codegen :: DataLayout -> FilePath -> Program -> EncodeAST Module
codegen layout moduleFilePath (Program main (Defs defs) tdefs externs) = do
    tdefs' <- defineDataTypes layout tdefs
    let defs' = (TypedVar "main" mainType, main) : Map.toList defs
        genGlobDefs = withExternSigs externs $ withGlobDefSigs
            defs'
            (liftA2 (:) genOuterMain (fmap join (mapM genGlobDef defs')))
    globDefs <- runGen' layout genGlobDefs
    pure Module
        { moduleName = fromString ((takeBaseName moduleFilePath))
        , moduleSourceFileName = fromString moduleFilePath
        , moduleDataLayout = Just layout
        , moduleTargetTriple = Nothing
        , moduleDefinitions =
            tdefs' ++ genBuiltins ++ genExterns externs ++ globDefs
        }

-- TODO: Consider separating sizeof calculations to a separate pass preceeding
--       Codegen, so that IO/EncodeAST may be limited to a more overviewable and
--       very self-contained module.
--
-- | Convert data-type definitions from `MonoAst` format to LLVM format, and
--   then both add them to the `EncodeAST` environment so `sizeof` can see them
--   later, and return them as `Definition`s so that they may be exported in the
--   Module AST.
--
--   Note that this method may be inefficient, since we define the data-types
--   twice. The first time manually within this module in order to be able to do
--   `sizeof`, and the second time implicitly within `withModuleFromAST`
--   somewhere when actually compiling the whole module with the LLVM library.
--
--   A data-type is a tagged union, and is represented in LLVM as a struct where
--   the first element is the variant-index as an i64, and the rest of the
--   elements are the field-types of the largest variant wrt allocation size.
defineDataTypes :: DataLayout -> TypeDefs -> EncodeAST [Definition]
defineDataTypes layout tds = do
    -- Forward declare to allow for recursion and unordered defs
    lhss <- forM tds $ \(tc, _) -> do
        let n = mkName (mangleTConst tc)
        (lhs, n') <- createNamedType n
        defineType n n' lhs
        pure (n, lhs)
    forM (zip lhss tds) $ \((n, lhs), (_, vs)) -> do
        let ts = map toLlvmVariantType vs
        sizedTs <- mapM (\t -> fmap (, t) (sizeof layout t)) ts
        let (_, tmax) = maximum sizedTs
        setNamedType lhs tmax
        pure (TypeDefinition n (Just tmax))

runGen' :: DataLayout -> Gen' a -> EncodeAST a
runGen' layout g = runReaderT
    (evalStateT g initSt)
    Env { _env = Map.empty, _dataLayout = layout }

initSt :: St
initSt = St
    { _currentBlockLabel = "entry"
    , _currentBlockInstrs = []
    , _registerCount = 0
    }

genBuiltins :: [Definition]
genBuiltins = map
    (GlobalDefinition . ($ []))
    [ simpleFunc
        (mkName "malloc")
        [parameter (mkName "size") i64]
        (LLType.ptr typeUnit)
    ]

genExterns :: [(String, MonoAst.Type)] -> [Definition]
genExterns = map (uncurry genExtern)

genExtern :: String -> MonoAst.Type -> Definition
genExtern name t = GlobalDefinition $ GlobalVariable
    { LLGlob.name = mkName name
    , LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.threadLocalMode = Nothing
    , LLGlob.unnamedAddr = Nothing
    , LLGlob.isConstant = True
    , LLGlob.type' = toLlvmType t
    , LLGlob.addrSpace = LLAddr.AddrSpace 0
    , LLGlob.initializer = Nothing
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.metadata = []
    }

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
        (withLocal ptv pRef (genExtractCaptures capturesRef fvs (genExpr body)))

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
        withLocals (zip fvs captureVals) ga

genExpr :: Expr -> Gen Operand
genExpr = \case
    Lit c -> fmap ConstantOperand (genConst c)
    Var (TypedVar x t) -> lookupVar (TypedVar x t)
    App f e -> genApp f e
    If p c a -> genIf p c a
    Fun p b -> genLambda p b
    Let ds b -> genLet ds b
    Match e cs tbody -> genMatch e cs (toLlvmType tbody)
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
        TNat8 -> i8
        TNat16 -> i16
        TNat32 -> i32
        TNat -> i64
        TInt8 -> i8
        TInt16 -> i16
        TInt32 -> i32
        TInt -> i64
        TDouble -> double
        TChar -> i32
        TBool -> typeBool
    TFun a r -> typeStruct
        [ LLType.ptr typeUnit
        , LLType.ptr (typeClosureFun (toLlvmType a) (toLlvmType r))
        ]
    TPtr t -> LLType.ptr (toLlvmType t)
    TConst t -> typeNamed (mangleTConst t)

genConst :: MonoAst.Const -> Gen LLConst.Constant
genConst = \case
    Unit -> pure litUnit
    Int n -> pure $ litI64 n
    Double x -> pure $ litDouble x
    Char c -> pure $ litI32 (Data.Char.ord c)
    Str s -> do
        var <- newName "strlit"
        let bytes = UTF8.String.encode s
        let len = fromIntegral (length bytes)
        let t = ArrayType len i8
        scribe outStrings [(var, len, bytes)]
        let llArrayVal = LLConst.GlobalReference (LLType.ptr t) var
        let ptrVal = LLConst.BitCast llArrayVal (LLType.ptr i8)
        let arrayVal = litStructOfType
                ("Array", [TPrim TNat8])
                [litI64 0, ptrVal, litU64 len]
        let strVal = litStructOfType ("Str", []) [litI64 0, arrayVal]
        pure strVal
    Bool b -> pure $ litBool b

lookupVar :: TypedVar -> Gen Operand
lookupVar x = do
    views env (Map.lookup x) >>= \case
        Just var -> emitAnon $ load var
        Nothing -> ice $ "Undefined variable " ++ show x

genApp :: Expr -> Expr -> Gen Operand
genApp fe ae = do
    closure <- genExpr fe
    a <- genExpr ae
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

-- TODO: Change global defs to a new type that can be generated by llvm.  As it
--       is now, global non-function variables can't be straight-forwardly
--       generated in general. Either, initialization is delayed until program
--       start, or an interpretation step is added between monomorphization and
--       codegen that evaluates all expressions in relevant contexts, like
--       constexprs.
genDef :: (Name, Type, Expr) -> Gen Operand
genDef (n, t, e) = genVar n t (genExpr e)

genMatch :: Expr -> DecisionTree -> Type -> Gen Operand
genMatch m dt tbody = do
    m' <- genExpr m
    genDecisionTree tbody dt (newSelections m')

genDecisionTree :: Type -> DecisionTree -> Selections Operand -> Gen Operand
genDecisionTree tbody = \case
    MonoAst.DSwitch selector cs def -> genDecisionSwitch selector cs def tbody
    MonoAst.DLeaf l -> genDecisionLeaf l

genDecisionSwitch
    :: MonoAst.Access
    -> Map VariantIx DecisionTree
    -> DecisionTree
    -> Type
    -> Selections Operand
    -> Gen Operand
genDecisionSwitch selector cs def tbody selections = do
    let (variantIxs, variantDts) = unzip (Map.toAscList cs)
    variantLs <- mapM (newName . (++ "_") . ("variant_" ++) . show) variantIxs
    let dests = zip (map litU64 variantIxs) variantLs
    defaultL <- newName "default"
    nextL <- newName "next"
    (m, selections') <- genSelect selector selections
    mVariantIx <- emitReg' "found_variant_ix" (extractvalueFromNamed m i64 [0])
    commitToNewBlock (switch mVariantIx defaultL dests) defaultL
    v <- genDecisionTree tbody def selections'
    let genCase l dt = do
            commitToNewBlock (br nextL) l
            genDecisionTree tbody dt selections'
    vs <- zipWithM genCase variantLs variantDts
    commitToNewBlock (br nextL) nextL
    emitAnon (phi (zip (v : vs) (defaultL : variantLs)))

genDecisionLeaf
    :: (MonoAst.VarBindings, Expr) -> Selections Operand -> Gen Operand
genDecisionLeaf (bs, e) selections =
    flip withLocals (genExpr e) =<< genSelectVarBindings selections bs

genSelect :: Access -> Selections Operand -> Gen (Operand, Selections Operand)
genSelect = select genAs genSub

genSelectVarBindings
    :: Selections Operand -> VarBindings -> Gen [(TypedVar, Operand)]
genSelectVarBindings = selectVarBindings genAs genSub

genAs :: [MonoAst.Type] -> Operand -> Gen Operand
genAs ts matchee = do
    let tvariant = toLlvmVariantType ts
    let tgeneric = typeOf matchee
    pGeneric <- emitReg' "ction_ptr_generic" (alloca tgeneric)
    emit (store matchee pGeneric)
    p <- emitReg' "ction_ptr" (bitcast pGeneric (LLType.ptr tvariant))
    emitReg' "ction" (load p)

genSub :: Word32 -> Operand -> Gen Operand
genSub i matchee = emitReg' "submatchee" (extractvalue matchee (pure (i + 1)))

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
        (undef t)
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

semiExecRetGen :: Gen Operand -> Gen' (Type, Out)
semiExecRetGen gx = runWriterT $ do
    x <- gx
    commitFinalFuncBlock (ret x)
    pure (typeOf x)
globStrVar :: (Name, Word64, [Word8]) -> Global
globStrVar (name, len, bytes) =
    simpleGlobVar name (ArrayType len i8) (LLConst.Array i8 (map litI8 bytes))


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
    , LLGlob.callingConvention = cfg_callConv
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
simpleGlobVar name t = simpleGlobVar' name t . Just

simpleGlobVar' :: Name -> Type -> Maybe LLConst.Constant -> Global
simpleGlobVar' name t init = GlobalVariable
    { LLGlob.name = name
    , LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.threadLocalMode = Nothing
    , LLGlob.addrSpace = LLAddr.AddrSpace 0
    , LLGlob.unnamedAddr = Nothing
    , LLGlob.isConstant = True
    , LLGlob.type' = t
    , LLGlob.initializer = init
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.metadata = []
    }

parameter :: Name -> Type -> LLGlob.Parameter
parameter p pt = LLGlob.Parameter pt p []

genSizeof :: Type -> Gen Operand
genSizeof t = do
    layout <- view dataLayout
    fmap litU64' (lift (lift (lift (sizeof layout t))))

withExternSigs :: MonadReader Env m => [(String, MonoAst.Type)] -> m a -> m a
withExternSigs = augment env . Map.fromList . map
    (\(name, t) ->
        ( TypedVar name t
        , ConstantOperand
            (LLConst.GlobalReference (LLType.ptr (toLlvmType t)) (mkName name))
        )
    )

withGlobDefSigs :: MonadReader Env m => [(TypedVar, Expr)] -> m a -> m a
withGlobDefSigs = augment env . Map.fromList . map
    (\(v@(TypedVar _ t), _) ->
        ( v
        , ConstantOperand
            (LLConst.GlobalReference (LLType.ptr (toLlvmType t)) (mangleName v))
        )
    )

withDefSigs :: [(TypedVar, Name)] -> Gen a -> Gen a
withDefSigs = augment env . Map.fromList . map
    (\(v@(TypedVar _ t), n') ->
        (v, LocalReference (LLType.ptr (toLlvmType t)) n')
    )

withLocals :: [(TypedVar, Operand)] -> Gen a -> Gen a
withLocals = flip (foldr (uncurry withLocal))

-- | Takes a local value, allocates a variable for it, and runs a generator in
--   the environment with the variable
withLocal :: TypedVar -> Operand -> Gen a -> Gen a
withLocal x v gen = do
    vPtr <- genVar' x (pure v)
    withVar x vPtr gen

-- | Takes a local, stack allocated value, and runs a generator in the
--   environment with the variable
withVar :: TypedVar -> Operand -> Gen a -> Gen a
withVar x v = locally env (Map.insert x v)

genVar :: Name -> Type -> Gen Operand -> Gen Operand
genVar n t gen = do
    ptr <- emitReg n (alloca t)
    val <- gen
    emit (store val ptr)
    pure ptr

genVar' :: TypedVar -> Gen Operand -> Gen Operand
genVar' (TypedVar x t) gen = do
    n <- newName x
    ptr <- genVar n (toLlvmType t) gen
    pure ptr

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

callExtern'' :: String -> Type -> [Operand] -> Instruction
callExtern'' f rt as = Call
    { tailCallKind = Just Tail
    , callingConvention = cfg_callConv
    , returnAttributes = []
    , function = Right $ ConstantOperand $ LLConst.GlobalReference
        (LLType.ptr (FunctionType rt (map typeOf as) False))
        (mkName f)
    , arguments = map (, []) as
    , functionAttributes = []
    , metadata = []
    }

undef :: Type -> Operand
undef = ConstantOperand . LLConst.Undef

condbr :: Operand -> Name -> Name -> Terminator
condbr c t f = CondBr c t f []

br :: Name -> Terminator
br = flip Br []

ret :: Operand -> Terminator
ret = flip Ret [] . Just

switch :: Operand -> Name -> [(LLConst.Constant, Name)] -> Terminator
switch x def cs = Switch x def cs []

bitcast :: Operand -> Type -> FunInstruction
bitcast x t = WithRetType (BitCast x t []) t

insertvalue :: Operand -> Operand -> [Word32] -> FunInstruction
insertvalue s e is = WithRetType (InsertValue s e is []) (typeOf s)

extractvalue :: Operand -> [Word32] -> FunInstruction
extractvalue struct is = WithRetType
    (ExtractValue { aggregate = struct, indices' = is, metadata = [] })
    (getIndexed (typeOf struct) is)

extractvalueFromNamed :: Operand -> Type -> [Word32] -> FunInstruction
extractvalueFromNamed struct t is = WithRetType
    (ExtractValue { aggregate = struct, indices' = is, metadata = [] })
    t

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
        , callingConvention = cfg_callConv
        , returnAttributes = []
        , function = Right f
        , arguments = map (, []) as
        , functionAttributes = []
        , metadata = []
        }
    )
    (getFunRet (getPointee (typeOf f)))

alloca :: Type -> FunInstruction
alloca t = WithRetType (Alloca t Nothing 0 []) (LLType.ptr t)

litU64' :: Word64 -> Operand
litU64' = ConstantOperand . litU64

litU64 :: Word64 -> LLConst.Constant
litU64 = litI64 . fromIntegral

litI64 :: Int -> LLConst.Constant
litI64 = LLConst.Int 64 . toInteger

litI32 :: Int -> LLConst.Constant
litI32 = LLConst.Int 32 . toInteger

litI8 :: Integral n => n -> LLConst.Constant
litI8 = LLConst.Int 8 . toInteger

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
    TPtr t -> mangleTConst ("*", [t])
    TConst tc -> mangleTConst tc

mangleTConst :: TConst -> String
mangleTConst (c, ts) =
    concat ["(", c, ";", intercalate "," (map mangleType ts), ")"]

unName :: Name -> ShortByteString
unName = \case
    Name s -> s
    UnName n -> fromString (show n)

sizeof :: DataLayout -> Type -> EncodeAST Word64
sizeof layout t = do
    t' <- toFFIType t
    liftIO (withFFIDataLayout layout $ \dl -> getTypeAllocSize dl t')

-- Note: encodeM requires named-types to be defined in the EncodeAST monad
--       already, which makes sense as e.g. getTypeAllocSize wouldn't make sense
--       to run before all types are defined. As such, make sure to define
--       all type-definitions in the EncodeAST monad first via llvm-hs internal
--       functions createNamedType => defineType => setNamedType.
toFFIType :: Type -> EncodeAST FFIType
toFFIType = encodeM

-- TODO: Use "tailcc" - Tail callable calling convention. It looks like exactly
--       what I want!
cfg_callConv :: LLCallConv.CallingConvention
cfg_callConv = LLCallConv.C
