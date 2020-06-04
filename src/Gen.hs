{-# LANGUAGE OverloadedStrings, LambdaCase, TupleSections, FlexibleContexts
           , TemplateHaskell #-}

-- | Code generation operations, generally not restricted to be used with AST
--   inputs. Basically an abstraction over llvm-hs. Reusable operations that can
--   be used both in Codegen and for manually generating LLVM code in other
--   situations.
module Gen where

import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Applicative
import qualified Codec.Binary.UTF8.String as UTF8.String
import Data.Map (Map)
import Data.Word
import Data.Foldable
import Data.Bifunctor
import Data.Functor
import Data.List
import Data.String
import Data.Maybe
import qualified Data.Map as Map
import Lens.Micro.Platform (makeLenses, modifying, use, view, assign, to)
import System.FilePath
import LLVM.AST
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.AST.ParameterAttribute
import LLVM.Prelude (ShortByteString)
import qualified LLVM.AST.CallingConvention as LLCallConv
import qualified LLVM.AST.Operand as LLOp
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Float as LLFloat
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.AddrSpace as LLAddr
import qualified LLVM.AST.Linkage as LLLink
import qualified LLVM.AST.Visibility as LLVis
import qualified LLSubprog

import Misc
import Pretty
import qualified Monomorphic as M
import Monomorphic (TypedVar(..), TPrim(..))
import qualified Monomorphize
import SrcPos


data GenErr
    = TransmuteErr SrcPos (M.Type, Word64) (M.Type, Word64)

type Instr = InstructionMetadata -> Instruction

-- | An instruction that returns a value. The name refers to the fact that a
--   mathematical function always returns a value, but an imperative procedure
--   may only produce side effects.
data FunInstr = WithRetType Instr Type

data Env = Env
    -- TODO: Could operands in env be Val instead? I.e., either stack-allocated
    --       or local?
    { _env :: Map TypedVar Operand -- ^ Environment of stack allocated variables
    , _enumTypes :: Map Name Word32
    , _dataTypes :: Map Name [Type]
    , _builtins :: Map String ([Parameter], Type)
    , _srcPos :: Maybe SrcPos
    }

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

type Gen'T m = StateT St (ReaderT Env m)
type Gen' = Gen'T (Except GenErr)

-- | The output of generating a function. Dependencies of stuff within the
--   function that must be generated at the top-level.
data Out = Out
    { _outBlocks :: [BasicBlock]
    , _outStrings :: [(Name, String)]
    , _outFuncs :: [(Name, [TypedVar], SrcPos, TypedVar, Gen Type)]
    , _outSrcPos :: [(SrcPos, MetadataNodeID)]
    }

type Gen = WriterT Out Gen'

data Val
    = VVar Operand
    | VLocal Operand

makeLenses ''Env
makeLenses ''St
makeLenses ''Out


instance Semigroup Out where
    Out bs1 ss1 fs1 ps1 <> Out bs2 ss2 fs2 ps2 =
        Out (bs1 <> bs2) (ss1 <> ss2) (fs1 <> fs2) (ps1 <> ps2)
instance Monoid Out where
    mempty = Out [] [] [] []

instance Typed Val where
    typeOf = \case
        VVar x -> getPointee (typeOf x)
        VLocal x -> typeOf x


-- | Generates a function definition
--
--   The signature definition, the parameter-loading, and the result return are
--   all done according to the calling convention.
genFunDef :: (Name, [TypedVar], SrcPos, TypedVar, Gen Type) -> Gen' (Global, [Definition])
genFunDef (name, fvs, dpos, ptv@(TypedVar px pt), genBody) = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    ((rt, fParams), Out basicBlocks globStrings lambdaFuncs srcPoss) <- runWriterT $ do
            -- Two equal SrcPos's in different scopes are not equal at the
            -- metadata level. Reset cache every scope.
        assign srcPosToMetadata Map.empty
        (capturesParam, captureLocals) <- genExtractCaptures
        pt' <- genType pt
        px' <- newName px
        let pRef = LocalReference pt' px'
        rt' <- locallySet srcPos (Just dpos)
            $ withLocal ptv pRef (withLocals captureLocals genBody)
        let fParams' = [uncurry Parameter capturesParam [], Parameter pt' px' []]
        pure (rt', fParams')
    (funScopeMdId, funScopeMdDef) <- defineFunScopeMetadata
    ss <- mapM globStrVar globStrings
    ls <- fmap
        concat
        (mapM (fmap (uncurry ((:) . GlobalDefinition)) . genFunDef) lambdaFuncs)
    ps <- mapM (defineSrcPos (MDRef funScopeMdId)) srcPoss
    let f = internFunc name fParams rt basicBlocks [("dbg", MDRef funScopeMdId)]
    pure (f, concat ss ++ ls ++ (funScopeMdDef : ps))
  where
    globStrVar (strName, s) = do
        name_inner <- newName' "strlit_inner"
        let bytes = UTF8.String.encode s
            len = length bytes
            tInner = ArrayType (fromIntegral len) i8
            defInner =
                simpleGlobConst name_inner tInner (LLConst.Array i8 (map litI8' bytes))
            inner = LLConst.GlobalReference (LLType.ptr tInner) name_inner
            ptrBytes = LLConst.BitCast inner (LLType.ptr i8)
            array = litStructNamed ("Array", [M.TPrim TNat8]) [ptrBytes, litI64' len]
            str = litStructNamed ("Str", []) [array]
            defStr = simpleGlobConst strName typeStr str
        pure (map GlobalDefinition [defInner, defStr])
    genExtractCaptures = do
        capturesName <- newName "captures"
        let capturesPtrGenericType = LLType.ptr typeUnit
        let capturesPtrGeneric = LocalReference capturesPtrGenericType capturesName
        let capturesParam = (capturesPtrGenericType, capturesName)
        fmap (capturesParam, ) $ if null fvs
            then pure []
            else do
                capturesType <- genCapturesType fvs
                capturesPtr <- emitAnonReg
                    (bitcast capturesPtrGeneric (LLType.ptr capturesType))
                captures <- emitAnonReg (load capturesPtr)
                captureVals <- mapM
                    (\(TypedVar x _, i) -> emitReg x =<< extractvalue captures [i])
                    (zip fvs [0 ..])
                pure (zip fvs captureVals)
    defineSrcPos funScopeMdRef (SrcPos _ line col, mdId) = do
        let loc =
                LLOp.DILocation
                    $ LLOp.Location (fromIntegral line) (fromIntegral col)
                    $ funScopeMdRef
        pure (MetadataNodeDefinition mdId loc)
    defineFunScopeMetadata :: Gen' (MetadataNodeID, Definition)
    defineFunScopeMetadata = do
        mdId <- newMetadataId'
        pure
            ( mdId
            , MetadataNodeDefinition
                mdId
                (DINode $ LLOp.DIScope $ LLOp.DILocalScope
                    (LLOp.DISubprogram funMetadataSubprog)
                )
            )
    funMetadataSubprog =
        let SrcPos path line _ = dpos
            -- TODO: Maybe only define this once and cache MDRef somewhere?
            fileNode =
                    let (dir, file) = splitFileName path
                    in  LLSubprog.File { LLSubprog.filename = fromString file
                                       , LLSubprog.directory = fromString dir
                                       , LLSubprog.checksum = Nothing
                                       }
        in  LLOp.Subprogram
                { LLSubprog.scope = Just (MDInline (LLOp.DIFile fileNode))
                , LLSubprog.name = nameSBString name
                , LLSubprog.linkageName = nameSBString name
                , LLSubprog.file = Just (MDInline fileNode)
                , LLSubprog.line = fromIntegral line
                , LLSubprog.type' = Just (MDInline (LLOp.SubroutineType [] 0 []))
                , LLSubprog.localToUnit = True
                , LLSubprog.definition = True
                , LLSubprog.scopeLine = fromIntegral line
                , LLSubprog.containingType = Nothing
                , LLSubprog.virtuality = LLOp.NoVirtuality
                , LLSubprog.virtualityIndex = 0
                , LLSubprog.thisAdjustment = 0
                , LLSubprog.flags = []
                , LLSubprog.optimized = False
                , LLSubprog.unit = Just compileUnitRef
                , LLSubprog.templateParams = []
                , LLSubprog.declaration = Nothing
                , LLSubprog.retainedNodes = []
                , LLSubprog.thrownTypes = []
                }
    nameSBString = \case
        Name s -> s
        UnName n -> fromString (show n)

-- TODO: Eta-conversion
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
genLambda :: [TypedVar] -> TypedVar -> (Gen (), Type) -> Gen Val
genLambda fvXs p body = do
    captures <- if null fvXs
        then pure (null' (LLType.ptr typeUnit))
        else do
            tcaptures <- fmap typeStruct (mapM (\(TypedVar _ t) -> genType t) fvXs)
            captures' <- genHeapAllocGeneric tcaptures
            populateCaptures captures' fvXs
            pure captures'
    genLambda' p body (VLocal captures) fvXs

populateCaptures :: Operand -> [TypedVar] -> Gen ()
populateCaptures ptrGeneric fvXs = do
    captures <- getLocal =<< genStruct =<< mapM lookupVar fvXs
    ptr <- emitAnonReg (bitcast ptrGeneric (LLType.ptr (typeOf captures)))
    emitDo (store captures ptr)

genLambda' :: TypedVar -> (Gen (), Type) -> Val -> [TypedVar] -> Gen Val
genLambda' p@(TypedVar _ pt) (b, bt) captures fvXs = do
    fname <- use lambdaParentFunc >>= \case
        Just s -> fmap (mkName . ((s ++ "_func_") ++) . show) (outerLambdaN <<+= 1)
        Nothing -> newName "func"
    ft <- genType pt <&> \pt' -> closureFunType pt' bt
    let f = VLocal $ ConstantOperand $ LLConst.GlobalReference (LLType.ptr ft) fname
    pos <- view (srcPos . to (fromMaybe (ice "srcPos is Nothing in genLambda")))
    scribe outFuncs [(fname, fvXs, pos, p, b $> bt)]
    genStruct [captures, f]

compileUnitRef :: MDRef LLOp.DICompileUnit
compileUnitRef = MDRef compileUnitId

compileUnitId :: MetadataNodeID
compileUnitId = MetadataNodeID 0

runGen' :: Monad m => StateT St (ReaderT Env m) a -> m a
runGen' g = runReaderT (evalStateT g initSt) initEnv
  where
    initEnv = Env { _env = Map.empty
                  , _enumTypes = Map.empty
                  , _dataTypes = Map.empty
                  , _builtins = Map.empty
                  , _srcPos = Nothing
                  }
    initSt = St { _currentBlockLabel = "entry"
                , _currentBlockInstrs = []
                , _registerCount = 0
                , _metadataCount = 3
                , _lambdaParentFunc = Nothing
                , _outerLambdaN = 1
             -- TODO: Maybe add a pass before this that just generates all
             --       SrcPos:s, separately and more cleanly?
                , _srcPosToMetadata = Map.empty
                }

internFunc
    :: Name
    -> [Parameter]
    -> Type
    -> [BasicBlock]
    -> [(ShortByteString, MDRef MDNode)]
    -> Global
internFunc n ps rt bs meta = Function { LLGlob.linkage = LLLink.External
                                      , LLGlob.visibility = LLVis.Hidden
                                      , LLGlob.dllStorageClass = Nothing
                                      , LLGlob.callingConvention = LLCallConv.Fast
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
                                      , LLGlob.metadata = meta
                                      }

externFunc
    :: Name
    -> [Parameter]
    -> Type
    -> [BasicBlock]
    -> [(ShortByteString, MDRef MDNode)]
    -> Global
externFunc n ps rt bs meta = Function { LLGlob.linkage = LLLink.External
                                      , LLGlob.visibility = LLVis.Default
                                      , LLGlob.dllStorageClass = Nothing
                                      , LLGlob.callingConvention = LLCallConv.C
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
                                      , LLGlob.metadata = meta
                                      }

simpleGlobVar :: Name -> Type -> LLConst.Constant -> Global
simpleGlobVar name t = simpleGlobVar' False name t . Just

simpleGlobConst :: Name -> Type -> LLConst.Constant -> Global
simpleGlobConst name t = simpleGlobVar' True name t . Just

simpleGlobVar' :: Bool -> Name -> Type -> Maybe LLConst.Constant -> Global
simpleGlobVar' isconst name t initializer = GlobalVariable
    { LLGlob.name = name
    , LLGlob.linkage = LLLink.External
    , LLGlob.visibility = LLVis.Default
    , LLGlob.dllStorageClass = Nothing
    , LLGlob.threadLocalMode = Nothing
    , LLGlob.addrSpace = LLAddr.AddrSpace 0
    , LLGlob.unnamedAddr = Nothing
    , LLGlob.isConstant = isconst
    , LLGlob.type' = t
    , LLGlob.initializer = initializer
    , LLGlob.section = Nothing
    , LLGlob.comdat = Nothing
    , LLGlob.alignment = 0
    , LLGlob.metadata = []
    }

getVar :: Val -> Gen Operand
getVar = \case
    VVar x -> pure x
    VLocal x -> genStackAllocated x

getLocal :: Val -> Gen Operand
getLocal = \case
    VVar x -> emitAnonReg (load x)
    VLocal x -> pure x

withLocals :: [(TypedVar, Operand)] -> Gen a -> Gen a
withLocals = withXs withLocal

-- | Takes a local value, allocates a variable for it, and runs a generator in
--   the environment with the variable
withLocal :: TypedVar -> Operand -> Gen a -> Gen a
withLocal x v gen = do
    vPtr <- genStackAllocated v
    withVar x vPtr gen

withVars :: [(TypedVar, Operand)] -> Gen a -> Gen a
withVars = withXs withVar

-- | Takes a local, stack allocated value, and runs a generator in the
--   environment with the variable
withVar :: TypedVar -> Operand -> Gen a -> Gen a
withVar x v = locally env (Map.insert x v)

withVals :: [(TypedVar, Val)] -> Gen a -> Gen a
withVals = withXs withVal

withVal :: TypedVar -> Val -> Gen a -> Gen a
withVal x v ga = do
    var <- getVar v
    withVar x var ga

withXs :: (TypedVar -> x -> Gen a -> Gen a) -> [(TypedVar, x)] -> Gen a -> Gen a
withXs f = flip (foldr (uncurry f))

genStruct :: [Val] -> Gen Val
genStruct xs = do
    xs' <- mapM getLocal xs
    let t = typeStruct (map typeOf xs')
    fmap VLocal $ foldlM (\s (i, x) -> emitAnonReg (insertvalue s x [i]))
                         (undef t)
                         (zip [0 ..] xs')

genHeapAllocGeneric :: Type -> Gen Operand
genHeapAllocGeneric t = do
    size <- fmap (litI64 . fromIntegral) (lift (sizeof t))
    emitAnonReg =<< callBuiltin "GC_malloc" [size]

genStackAllocated :: Operand -> Gen Operand
genStackAllocated v = do
    ptr <- emitAnonReg (alloca (typeOf v))
    emitDo (store v ptr)
    pure ptr

lookupVar :: MonadReader Env m => TypedVar -> m Val
lookupVar x = do
    view (env . to (Map.lookup x)) >>= \case
        Just var -> pure (VVar var)
        Nothing -> ice $ "Undefined variable " ++ show x

callBuiltin :: String -> [Operand] -> Gen FunInstr
callBuiltin f as = do
    (_, rt) <- view (builtins . to (Map.lookup f)) <&> \case
        Just b' -> b'
        Nothing -> ice $ "callBuiltin on '" ++ f ++ "' not in builtins"
    let f' = ConstantOperand $ LLConst.GlobalReference
            (LLType.ptr (FunctionType rt (map typeOf as) False))
            (mkName f)
    pure $ flip WithRetType rt $ callExtern f' (map (, []) as)

callIntern
    :: Maybe TailCallKind
    -> Operand
    -> [(Operand, [LLVM.AST.ParameterAttribute.ParameterAttribute])]
    -> InstructionMetadata
    -> Instruction
callIntern = call LLCallConv.Fast

callExtern
    :: Operand
    -> [(Operand, [LLVM.AST.ParameterAttribute.ParameterAttribute])]
    -> InstructionMetadata
    -> Instruction
callExtern = call LLCallConv.C Nothing

call
    :: LLCallConv.CallingConvention
    -> Maybe TailCallKind
    -> Operand
    -> [(Operand, [LLVM.AST.ParameterAttribute.ParameterAttribute])]
    -> InstructionMetadata
    -> Instruction
call callconv tailkind f as meta = Call { tailCallKind = tailkind
                                        , callingConvention = callconv
                                        , returnAttributes = []
                                        , function = Right f
                                        , arguments = as
                                        , functionAttributes = []
                                        , metadata = meta
                                        }

withBuiltins :: Gen' a -> Gen' a
withBuiltins ga = builtinExterns
    >>= \es -> augment builtins (Map.union builtinsHidden es) ga
    where builtinExterns = mapM (fmap snd . genExternTypeSig) Monomorphize.builtinExterns

defineBuiltinsHidden :: [Definition]
defineBuiltinsHidden = map
    (\(x, (ps, tr)) -> GlobalDefinition (externFunc (mkName x) ps tr [] []))
    (Map.toList builtinsHidden)

builtinsHidden :: Map String ([Parameter], Type)
builtinsHidden = Map.fromList
    [ ( "carth_str_eq"
      , ( [Parameter typeStr (mkName "s1") [], Parameter typeStr (mkName "s2") []]
        , typeBool
        )
      )
    , ("install_stackoverflow_handler", ([], LLType.void))
    ]

genExternTypeSig :: M.Type -> Gen' (([M.Type], Type), ([Parameter], Type))
genExternTypeSig t = do
    let (pts, rt) = uncurryType t
    when (null pts) $ ice "genExternTypeSig of non-function"
    let anon = mkName ""
    pts' <- mapM genType' pts
    ps <- forM pts' $ \pt' -> passByRef' pt' <&> \case
        True -> Parameter (LLType.ptr pt') anon [ByVal]
        False -> Parameter pt' anon []
    rt' <- genRetType' rt
    (rt'', ps') <- passByRef' rt' <&> \case
        True -> (LLType.void, Parameter (LLType.ptr rt') anon [SRet] : ps)
        False -> (rt', ps)
    pure ((pts, rt'), (ps', rt''))
  where

    uncurryType :: M.Type -> ([M.Type], M.Type)
    uncurryType = \case
        M.TFun a b -> first (a :) (uncurryType b)
        x -> ([], x)

passByRef :: Type -> Gen Bool
passByRef = lift . passByRef'

-- NOTE: This post is helpful:
--       https://stackoverflow.com/questions/42411819/c-on-x86-64-when-are-structs-classes-passed-and-returned-in-registers
--       Also, official docs:
--       https://software.intel.com/sites/default/files/article/402129/mpx-linux64-abi.pdf
--       particularly section 3.2.3 Parameter Passing (p18).
passByRef' :: Type -> Gen' Bool
passByRef' = \case
    NamedTypeReference x -> view (dataTypes . to (Map.lookup x)) >>= \case
        Just ts -> passByRef' (typeStruct ts)
        Nothing -> ice $ "passByRef': No dataType for NamedTypeReference " ++ show x
    -- Simple scalar types. They go in registers.
    VoidType -> pure False
    IntegerType _ -> pure False
    PointerType _ _ -> pure False
    FloatingPointType _ -> pure False
    -- Functions are not POD (Plain Ol' Data), so they are passed on the
    -- stack.
    FunctionType _ _ _ -> pure True
    -- TODO: Investigate how exactly SIMD vectors are to be passed when/if
    --       we ever add support for that in the rest of the compiler.
    VectorType _ _ -> pure True
    -- Aggregate types can either be passed on stack or in regs, depending
    -- on what they contain.
    t@(StructureType _ us) -> do
        size <- sizeof t
        if size > 16 then pure True else fmap or (mapM passByRef' us)
    ArrayType _ u -> do
        size <- sizeof u
        if size > 16 then pure True else passByRef' u
    -- N/A
    MetadataType -> ice "passByRef of MetadataType"
    LabelType -> ice "passByRef of LabelType"
    TokenType -> ice "passByRef of TokenTyp"

genRetType :: M.Type -> Gen Type
genRetType = lift . genRetType'

genRetType' :: Monad m => M.Type -> Gen'T m Type
genRetType' = fmap (\t -> if t == typeUnit then LLType.void else t) . genType'

genType :: M.Type -> Gen Type
genType = lift . genType'

-- | Convert to the LLVM representation of a type in an expression-context.
genType' :: Monad m => M.Type -> Gen'T m Type
genType' = \case
    M.TPrim tc -> pure $ case tc of
        M.TNat8 -> i8
        M.TNat16 -> i16
        M.TNat32 -> i32
        M.TNat -> i64
        M.TInt8 -> i8
        M.TInt16 -> i16
        M.TInt32 -> i32
        M.TInt -> i64
        M.TF64 -> double
    M.TFun a r -> liftA2 closureType (genType' a) (genRetType' r)
    M.TBox t -> fmap LLType.ptr (genType' t)
    M.TConst tc -> lookupEnum tc <&> \case
        Just 0 -> typeUnit
        Just w -> IntegerType w
        Nothing -> genDatatypeRef tc

genDatatypeRef :: M.TConst -> Type
genDatatypeRef = NamedTypeReference . mkName . mangleTConst

-- | A `Fun` is a closure, and follows a certain calling convention
--
--   A closure is represented as a pair where the first element is the pointer
--   to the structure of captures, and the second element is a pointer to the
--   actual function, which takes as first parameter the captures-pointer, and
--   as second parameter the argument.
closureType :: Type -> Type -> Type
closureType a r = typeStruct [LLType.ptr typeUnit, LLType.ptr (closureFunType a r)]

-- The type of the function itself within the closure
closureFunType :: Type -> Type -> Type
closureFunType a r = FunctionType { resultType = r
                                  , argumentTypes = [LLType.ptr typeUnit, a]
                                  , isVarArg = False
                                  }

genCapturesType :: [M.TypedVar] -> Gen Type
genCapturesType = fmap typeStruct . mapM (\(M.TypedVar _ t) -> genType t)

genVariantType :: Monad m => M.Span -> [M.Type] -> Gen'T m [Type]
genVariantType totVariants =
    fmap (maybe id ((:) . IntegerType) (tagBitWidth totVariants)) . mapM genType'

tagBitWidth :: M.Span -> Maybe Word32
tagBitWidth span' | span' <= 2 ^ (0 :: Integer) = Nothing
                  | span' <= 2 ^ (8 :: Integer) = Just 8
                  | span' <= 2 ^ (16 :: Integer) = Just 16
                  | span' <= 2 ^ (32 :: Integer) = Just 32
                  | span' <= 2 ^ (64 :: Integer) = Just 64
                  | otherwise = ice $ "tagBitWidth: span' = " ++ show span'

-- TODO: Handle different data layouts. Check out LLVMs DataLayout class and
--       impl of `getTypeAllocSize`.
--       https://llvm.org/doxygen/classllvm_1_1DataLayout.html
--
-- | Haskell-native implementation of `sizeof`, in contrast to
--   `getTypeAllocSize` of `llvm-hs`.
--
--   The problem with `getTypeAllocSize` is that it requires an `EncodeAST`
--   monad and messy manipulations. Specifically, I had some recursive bindings
--   going on, but to represent them in a monad I needed `mfix`, but `EncodeAST`
--   didn't have `mfix`!
--
--   See the [System V ABI docs](https://software.intel.com/sites/default/files/article/402129/mpx-linux64-abi.pdf)
--   for more info.
sizeof :: Monad m => Type -> Gen'T m Word64
sizeof = \case
    NamedTypeReference x -> sizeof =<< lookupDatatype x
    IntegerType bits -> pure (fromIntegral (toBytesCeil bits))
    PointerType _ _ -> pure 8
    FloatingPointType HalfFP -> pure 2
    FloatingPointType FloatFP -> pure 4
    FloatingPointType DoubleFP -> pure 8
    FloatingPointType FP128FP -> pure 16
    FloatingPointType X86_FP80FP -> pure 16
    FloatingPointType PPC_FP128FP -> pure 16
    StructureType _ us -> foldlM addMember 0 us
    VectorType n u -> fmap (fromIntegral n *) (sizeof u)
    ArrayType n u -> fmap (n *) (sizeof u)
    VoidType -> ice "sizeof VoidType"
    FunctionType _ _ _ -> ice "sizeof FunctionType"
    MetadataType -> ice "sizeof MetadataType"
    LabelType -> ice "sizeof LabelType"
    TokenType -> ice "sizeof TokenType"
  where
    toBytesCeil nbits = div (nbits + 7) 8
    addMember accSize u = do
        align <- alignmentof u
        let padding = if align == 0 then 0 else mod (align - accSize) align
        size <- sizeof u
        pure (accSize + padding + size)

alignmentof :: Monad m => Type -> Gen'T m Word64
alignmentof = \case
    NamedTypeReference x -> alignmentof =<< lookupDatatype x
    StructureType _ [] -> pure 0
    t@(StructureType _ us) -> do
        as <- traverse alignmentof us
        if null as
            then ice ("alignmentof: alignments empty for struct " ++ show t)
            else pure (maximum as)
    VectorType _ u -> alignmentof u
    ArrayType _ u -> alignmentof u
    t -> sizeof t

emitDo' :: FunInstr -> Gen ()
emitDo' (WithRetType instr _) = emitDo instr

emitDo :: Instr -> Gen ()
emitNamedReg :: Name -> FunInstr -> Gen Operand
(emitDo, emitNamedReg) =
    ( emit' Do
    , \reg (WithRetType instr rt) -> emit' (reg :=) instr $> LocalReference rt reg
    )
  where
    emit' :: (Instruction -> Named Instruction) -> Instr -> Gen ()
    emit' nameInstruction instr = do
        meta <- view srcPos >>= \case
            Just pos -> do
                loc <- genSrcPos pos
                pure [("dbg", loc)]
            Nothing -> pure []
        modifying currentBlockInstrs (nameInstruction (instr meta) :)
    genSrcPos :: SrcPos -> Gen (MDRef MDNode)
    genSrcPos pos = do
        use (srcPosToMetadata . to (Map.lookup pos)) >>= \case
            Just mdRef -> pure mdRef
            Nothing -> do
                mdId <- newMetadataId
                let mdRef = MDRef mdId
                scribe outSrcPos [(pos, mdId)]
                modifying srcPosToMetadata (Map.insert pos mdRef)
                pure (mdRef)

emitReg :: String -> FunInstr -> Gen Operand
emitReg s instr = newName s >>= flip emitNamedReg instr

emitAnonReg :: FunInstr -> Gen Operand
emitAnonReg instr = newAnonRegister >>= flip emitNamedReg instr
    where newAnonRegister = fmap UnName (registerCount <<+= 1)

commitFinalFuncBlock :: Terminator -> Gen ()
commitFinalFuncBlock t = commitToNewBlock
    t
    (ice "Continued gen after final block of function was already commited")

commitToNewBlock :: Terminator -> Name -> Gen ()
commitToNewBlock t l = do
    n <- use currentBlockLabel
    is <- use (currentBlockInstrs . to reverse)
    scribe outBlocks [BasicBlock n is (Do t)]
    assign currentBlockLabel l
    assign currentBlockInstrs []

newName :: String -> Gen Name
newName = lift . newName'

newName' :: String -> Gen' Name
newName' s = fmap (mkName . (s ++) . show) (registerCount <<+= 1)

newMetadataId :: Gen MetadataNodeID
newMetadataId = lift newMetadataId'

newMetadataId' :: Gen' MetadataNodeID
newMetadataId' = fmap MetadataNodeID (metadataCount <<+= 1)

lookupEnum :: Monad m => M.TConst -> Gen'T m (Maybe Word32)
lookupEnum tc = view (enumTypes . to (tconstLookup tc))

tconstLookup :: M.TConst -> Map Name a -> Maybe a
tconstLookup = Map.lookup . mkName . mangleTConst

lookupDatatype :: Monad m => Name -> Gen'T m Type
lookupDatatype x = view (enumTypes . to (Map.lookup x)) >>= \case
    Just 0 -> pure typeUnit
    Just w -> pure (IntegerType w)
    Nothing -> fmap (maybe (ice ("Undefined datatype " ++ show x)) typeStruct)
                    (view (dataTypes . to (Map.lookup x)))

extractvalue :: Operand -> [Word32] -> Gen FunInstr
extractvalue struct is = fmap (WithRetType (ExtractValue struct is))
                              (getIndexed (typeOf struct) (map fromIntegral is))
  where
    getIndexed = foldlM $ \t i -> getMembers t <&> \us -> if i < length us
        then us !! i
        else
            ice
            $ "extractvalue: index out of bounds: "
            ++ (show (typeOf struct) ++ ", " ++ show is)
    getMembers = \case
        NamedTypeReference x -> getMembers =<< lift (lookupDatatype x)
        StructureType _ members -> pure members
        t -> ice $ "Tried to get member types of non-struct type " ++ show t

undef :: Type -> Operand
undef = ConstantOperand . LLConst.Undef

null' :: Type -> Operand
null' = ConstantOperand . LLConst.Null

condbr :: Operand -> Name -> Name -> Terminator
condbr c t f = CondBr c t f []

br :: Name -> Terminator
br = flip Br []

ret :: Operand -> Terminator
ret = flip Ret [] . Just

retVoid :: Terminator
retVoid = Ret Nothing []

switch :: Operand -> Name -> [(LLConst.Constant, Name)] -> Terminator
switch x def cs = Switch x def cs []

bitcast :: Operand -> Type -> FunInstr
bitcast x t = WithRetType (BitCast x t) t

inttoptr :: Operand -> Type -> FunInstr
inttoptr x t = WithRetType (IntToPtr x t) t

ptrtoint :: Operand -> Type -> FunInstr
ptrtoint x t = WithRetType (PtrToInt x t) t

trunc :: Operand -> Type -> FunInstr
trunc x t = WithRetType (Trunc x t) t

insertvalue :: Operand -> Operand -> [Word32] -> FunInstr
insertvalue s e is = WithRetType (InsertValue s e is) (typeOf s)

store :: Operand -> Operand -> Instr
store srcVal destPtr meta = Store { volatile = False
                                  , address = destPtr
                                  , value = srcVal
                                  , maybeAtomicity = Nothing
                                  , alignment = 0
                                  , metadata = meta
                                  }

load :: Operand -> FunInstr
load p = WithRetType
    (\meta -> Load { volatile = False
                   , address = p
                   , maybeAtomicity = Nothing
                   , alignment = 0
                   , metadata = meta
                   }
    )
    (getPointee (typeOf p))

phi :: [(Operand, Name)] -> FunInstr
phi = \case
    [] -> ice "phi was given empty list of cases"
    cs@((op, _) : _) -> let t = typeOf op in WithRetType (Phi t cs) t

alloca :: Type -> FunInstr
alloca t = WithRetType (Alloca t Nothing 0) (LLType.ptr t)

litF64 :: Double -> Operand
litF64 = ConstantOperand . LLConst.Float . LLFloat.Double

litI64 :: Int -> Operand
litI64 = ConstantOperand . litI64'

litI64' :: Int -> LLConst.Constant
litI64' = LLConst.Int 64 . toInteger

litI32 :: Int -> Operand
litI32 = ConstantOperand . LLConst.Int 32 . toInteger

litI8' :: Integral n => n -> LLConst.Constant
litI8' = LLConst.Int 8 . toInteger

litDouble :: Double -> Operand
litDouble = ConstantOperand . LLConst.Float . LLFloat.Double

litStruct :: [LLConst.Constant] -> LLConst.Constant
litStruct = LLConst.Struct Nothing False

-- NOTE: typeOf Struct does not return NamedTypeReference of the structName, so
--       sometimes, an expression created from this will have the wrong
--       type. Specifically, I have observed this behaviour i phi-nodes. To
--       guard against it (until fixed upstream, hopefully), store the value in
--       a variable beforehand.
litStructNamed :: M.TConst -> [LLConst.Constant] -> LLConst.Constant
litStructNamed t xs =
    let tname = mkName (mangleTConst t) in LLConst.Struct (Just tname) False xs

litUnit :: Operand
litUnit = ConstantOperand (litStruct [])

typeStr :: Type
typeStr = NamedTypeReference (mkName (mangleTConst ("Str", [])))

typeBool :: Type
typeBool = i8

typeUnit :: Type
typeUnit = typeStruct []

typeStruct :: [Type] -> Type
typeStruct ts = StructureType { isPacked = False, elementTypes = ts }

getFunRet :: Type -> Type
getFunRet = \case
    FunctionType rt _ _ -> rt
    t -> ice $ "Tried to get return type of non-function type " ++ show t

getPointee :: Type -> Type
getPointee = \case
    LLType.PointerType t _ -> t
    t -> ice $ "Tried to get pointee of non-function type " ++ show t

getIntBitWidth :: Type -> Word32
getIntBitWidth = \case
    LLType.IntegerType w -> w
    t -> ice $ "Tried to get bit width of non-integer type " ++ show t

mangleName :: (String, [M.Type]) -> String
mangleName = \case
    -- Instead of dealing with changing entrypoint name and startfiles, just
    -- call the outermost, compiler generated main `main`, and the user-defined
    -- main `_main`, via this `mangleName` mechanic.
    ("main", []) -> "_main"
    ("main", _) -> ice "mangleName of `main` of non-empty instantiation"
    (x, us) -> x ++ mangleInst us

mangleInst :: [M.Type] -> String
mangleInst ts =
    if not (null ts) then "<" ++ intercalate ", " (map mangleType ts) ++ ">" else ""

mangleType :: M.Type -> String
mangleType = \case
    M.TPrim c -> pretty c
    M.TFun p r -> mangleTConst ("Fun", [p, r])
    M.TBox t -> mangleTConst ("Box", [t])
    M.TConst tc -> mangleTConst tc

mangleTConst :: M.TConst -> String
mangleTConst (c, ts) = c ++ mangleInst ts
