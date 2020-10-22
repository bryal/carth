{-# LANGUAGE OverloadedStrings, LambdaCase, TupleSections, FlexibleContexts
           , TemplateHaskell, DuplicateRecordFields #-}

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
import qualified LLVM.AST.IntegerPredicate as LLIPred
import qualified LLVM.AST.FloatingPointPredicate as LLFPred

import Misc
import Pretty
import qualified TypeAst
import qualified Optimized as Ast
import Optimized (TypedVar(..), TPrim(..))
import qualified Monomorphize
import SrcPos


data GenErr
    = TransmuteErr SrcPos (Ast.Type, Word64) (Ast.Type, Word64)
    | CastErr SrcPos Ast.Type Ast.Type
    | NoBuiltinVirtualInstance SrcPos String Ast.Type

type Instr = InstructionMetadata -> Instruction

-- | An instruction that returns a value. The name refers to the fact that a
--   mathematical function always returns a value, but an imperative procedure
--   may only produce side effects.
data FunInstr = WithRetType Instr Type

data Env = Env
    -- TODO: Could operands in env be Val instead? I.e., either stack-allocated
    --       or local?
    { _localEnv :: Map TypedVar Operand -- ^ Environment of stack allocated variables
    , _globalEnv :: Map TypedVar Operand
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
            ptrBytes = LLConst.BitCast inner typeGenericPtr
            array =
                litStructNamed ("Array", [Ast.TPrim (TNat 8)]) [ptrBytes, litI64' len]
            str = litStructNamed ("Str", []) [array]
            defStr = simpleGlobConst strName typeStr str
        pure (map GlobalDefinition [defInner, defStr])
    genExtractCaptures = do
        capturesName <- newName "captures"
        let capturesPtrGeneric = LocalReference typeGenericPtr capturesName
        let capturesParam = (typeGenericPtr, capturesName)
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
    defineSrcPos funScopeMdRef (SrcPos _ line col _, mdId) = do
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
        let SrcPos path line _ _ = dpos
            -- TODO: Maybe only define this once and cache MDRef somewhere?
            fileNode =
                    let (dir, file) = splitFileName path
                    in  LLOp.File { LLOp.filename = fromString file
                                  , LLOp.directory = fromString dir
                                  , LLOp.checksum = Nothing
                                  }
        in  LLOp.Subprogram { LLOp.scope = Just (MDInline (LLOp.DIFile fileNode))
                            , LLOp.name = nameSBString name
                            , LLOp.linkageName = nameSBString name
                            , LLOp.file = Just (MDInline fileNode)
                            , LLOp.line = fromIntegral line
                            , LLOp.type' = Just (MDInline (LLOp.SubroutineType [] 0 []))
                            , LLOp.localToUnit = True
                            , LLOp.definition = True
                            , LLOp.scopeLine = fromIntegral line
                            , LLOp.containingType = Nothing
                            , LLOp.virtuality = LLOp.NoVirtuality
                            , LLOp.virtualityIndex = 0
                            , LLOp.thisAdjustment = 0
                            , LLOp.flags = []
                            , LLOp.optimized = False
                            , LLOp.unit = Just compileUnitRef
                            , LLOp.templateParams = []
                            , LLOp.declaration = Nothing
                            , LLOp.retainedNodes = []
                            , LLOp.thrownTypes = []
                            }
    nameSBString = \case
        Name s -> s
        UnName n -> fromString (show n)

genTailWrapInLambdas
    :: Type -> [TypedVar] -> [Ast.Type] -> ([TypedVar] -> Gen Val) -> Gen Type
genTailWrapInLambdas rt fvs ps genBody =
    genWrapInLambdas rt fvs ps genBody >>= getLocal >>= \r ->
        commitFinalFuncBlock (ret r) $> typeOf r

genWrapInLambdas :: Type -> [TypedVar] -> [Ast.Type] -> ([TypedVar] -> Gen Val) -> Gen Val
genWrapInLambdas rt fvs pts genBody = case pts of
    [] -> genBody fvs
    (pt : pts') -> do
        let p = TypedVar ("x" ++ show (length fvs)) pt
        bt <- foldr closureType rt <$> mapM genType pts'
        genLambda fvs p (genTailWrapInLambdas rt (fvs ++ [p]) pts' genBody $> (), bt)

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
        then pure (null' typeGenericPtr)
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
genLambda' p@(TypedVar _ pt) (genBody, bt) captures fvXs = do
    fname <- use lambdaParentFunc >>= \case
        Just s -> fmap (mkName . ((s ++ "_func_") ++) . show) (outerLambdaN <<+= 1)
        Nothing -> newName "func"
    ft <- genType pt <&> \pt' -> closureFunType pt' bt
    let f = VLocal $ ConstantOperand $ LLConst.GlobalReference (LLType.ptr ft) fname
    pos <- view (srcPos . to (fromMaybe (ice "srcPos is Nothing in genLambda")))
    scribe outFuncs [(fname, fvXs, pos, p, genBody $> bt)]
    genStruct [captures, f]

compileUnitRef :: MDRef LLOp.DICompileUnit
compileUnitRef = MDRef compileUnitId

compileUnitId :: MetadataNodeID
compileUnitId = MetadataNodeID 0

runGen' :: Monad m => StateT St (ReaderT Env m) a -> m a
runGen' g = runReaderT (evalStateT g initSt) initEnv
  where
    initEnv = Env { _localEnv = Map.empty
                  , _globalEnv = Map.empty
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
withVar x v = locally localEnv (Map.insert x v)

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

-- | Must be used on globals when running in JIT, as Boehm GC only detects global var
--   roots when it can scan some segment in the ELF.
genGcAddRoot :: LLConst.Constant -> Gen ()
genGcAddRoot globRef =
    let p0 = LLConst.BitCast globRef (LLType.ptr i8)
        ptrSize = litI64' 8
        p1 = LLConst.GetElementPtr False p0 [ptrSize]
    in  emitDo' =<< callBuiltin "GC_add_roots" [ConstantOperand p0, ConstantOperand p1]

lookupVar :: TypedVar -> Gen Val
lookupVar x = lookupVar' x >>= \case
    Just y -> pure y
    Nothing -> genAppBuiltinVirtual x []

lookupVar' :: MonadReader Env m => TypedVar -> m (Maybe Val)
lookupVar' x =
    ask <&> \e -> fmap VVar (Map.lookup x (_localEnv e) <|> Map.lookup x (_globalEnv e))

genAppBuiltinVirtual :: TypedVar -> [Gen Val] -> Gen Val
genAppBuiltinVirtual (TypedVar g t) aes = do
    -- TODO: The arguments are not generated in the same scope as the application if the
    --       builtin virtual is partially applied. If it's fully applied, there's no
    --       problem, as no additional wrapping lambda scope will be created, and the
    --       local references to the argument values will be valid. If it's not applied
    --       at all, there's no problem, as there are no generated arguments to try to
    --       reach in the first place. Only partial application is a problem.
    --
    --       Currently, we fully wrap the virtual in lambdas, and then immediately apply
    --       with the generated arguments in the local scope. This is inefficient, as
    --       we'll be generating a ton of identical functions for all the times the same
    --       builtin virtual is used.
    --
    --       One better solution could be to generate functions with all parameters,
    --       i.e. not partially applied, and do that only once. Either at start for all
    --       possible types, or here, and use some kind of caching/memoization. Then,
    --       partial application is as simple as looking up the global, single function
    --       definition, and partially apply it. The normal function generation logic will
    --       handle variable capturing and closure generation. Only full application would
    --       be a special case. Sort of the same thinking as for normal function calls,
    --       see https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/haskell-execution/function-calls
    as <- sequence aes
    pos <- view srcPos
    let wrap xts genRt op = do
            rt' <- genRt
            if length as == length xts
                then op as
                else do
                    f <- genWrapInLambdas rt' [] xts (op <=< mapM lookupVar)
                    apps Nothing f as
    let wrap1 (xt, rt, f) = wrap [xt] rt (\xs -> f (xs !! 0))
    let wrap2 (x0t, x1t, rt, f) = wrap [x0t, x1t] rt (\xs -> f (xs !! 0) (xs !! 1))
    let noInst = throwError $ NoBuiltinVirtualInstance
            (fromMaybe
                (ice "genAppBuiltinVirtual: no srcpos when throwing noInst error!")
                pos
            )
            g
            t
    let arithm u s f = \case
            Ast.TFun a@(Ast.TPrim p) (Ast.TFun b c) | a == b && a == c -> pure
                ( a
                , a
                , genType a
                , \x y ->
                    let op = if isInt' p then s else if isFloat p then f else u
                    in  fmap VLocal . emitAnonReg =<< liftA2 op (getLocal x) (getLocal y)
                )
            _ -> noInst
    let bitwise u s = \case
            Ast.TFun a@(Ast.TPrim p) (Ast.TFun b c)
                | a == b && a == c && (isInt' p || isNat p) -> pure
                    ( a
                    , a
                    , genType a
                    , \x y -> fmap VLocal . emitAnonReg =<< if isNat p
                        then liftA2 u (getLocal x) (getLocal y)
                        else liftA2 s (getLocal x) (getLocal y)
                    )
            _ -> noInst
    let rel u s f = \case
            Ast.TFun a@(Ast.TPrim p) (Ast.TFun b _) | a == b -> pure
                ( a
                , a
                , pure typeBool
                , \x y ->
                    let op = if isInt' p
                            then icmp s
                            else if isFloat p then fcmp f else icmp u
                    in  fmap VLocal
                            . emitAnonReg
                            . flip zext i8
                            =<< emitAnonReg
                            =<< liftA2 op (getLocal x) (getLocal y)
                )
            _ -> noInst
    case g of
        "+" -> wrap2 =<< arithm add add fadd t
        "-" -> wrap2 =<< arithm sub sub fsub t
        "*" -> wrap2 =<< arithm mul mul fmul t
        "/" -> wrap2 =<< arithm udiv sdiv fdiv t
        "rem" -> wrap2 =<< arithm urem srem frem t
        "shift-l" -> wrap2 =<< bitwise shl shl t
        "shift-r" -> wrap2 =<< bitwise lshr ashr t
        "ashift-r" -> wrap2 =<< bitwise ashr ashr t
        "bit-and" -> wrap2 =<< bitwise and' and' t
        "bit-or" -> wrap2 =<< bitwise or' or' t
        "bit-xor" -> wrap2 =<< bitwise xor xor t
        -- NOTE: When comparing floats, one or both operands may be NaN. We can use either
        -- the `o` or `u` prefix to change how NaNs are treated by `fcmp`. I'm not sure,
        -- but I think that always using `o` will result in the most predictable code.
        "=" -> wrap2 =<< rel LLIPred.EQ LLIPred.EQ LLFPred.OEQ t
        "/=" -> wrap2 =<< rel LLIPred.NE LLIPred.NE LLFPred.ONE t
        ">" -> wrap2 =<< rel LLIPred.UGT LLIPred.SGT LLFPred.OGT t
        ">=" -> wrap2 =<< rel LLIPred.UGE LLIPred.SGE LLFPred.OGE t
        "<" -> wrap2 =<< rel LLIPred.ULT LLIPred.SLT LLFPred.OLT t
        "<=" -> wrap2 =<< rel LLIPred.ULE LLIPred.SLE LLFPred.OLE t
        "transmute" -> wrap1 =<< case t of
            Ast.TFun a b -> case pos of
                Just p -> pure (a, genType b, \x -> genTransmute p x a b)
                Nothing -> ice "genAppBuiltinVirtual: transmute: srcPos is Nothing"
            _ -> noInst
        "cast" -> wrap1 =<< case t of
            Ast.TFun a b -> case pos of
                Just p -> pure (a, genType b, \x -> genCast p x a b)
                Nothing -> ice "genAppBuiltinVirtual: cast: srcPos is Nothing"
            _ -> noInst
        "deref" -> wrap1 =<< case t of
            Ast.TFun a b -> pure (a, genType b, genDeref)
            _ -> noInst
        "store" -> wrap2 =<< case t of
            Ast.TFun a (Ast.TFun b c) -> pure (a, b, genType c, genStore)
            _ -> noInst
        _ -> ice $ "genAppBuiltinVirtual: No builtin virtual function `" ++ g ++ "`"
  where
    genTransmute :: SrcPos -> Val -> Ast.Type -> Ast.Type -> Gen Val
    genTransmute pos x a b = do
        a' <- genType a
        b' <- genType b
        sa <- lift (sizeof a')
        sb <- lift (sizeof b')
        if sa == sb
            then transmute a' b' x
            else throwError (TransmuteErr pos (a, sa) (b, sb))
    genCast :: SrcPos -> Val -> Ast.Type -> Ast.Type -> Gen Val
    genCast pos x a b = do
        a' <- genType a
        b' <- genType b
        let emit' instr = getLocal x >>= \x' -> emitAnonReg (instr x' b') <&> VLocal
        case (a', b') of
            _ | a' == b' -> pure x
            (IntegerType w1, IntegerType w2) ->
                emit' $ if w2 < w1 then trunc else if isInt a then sext else zext
            (FloatingPointType f1, FloatingPointType f2) -> case (f1, f2) of
                (HalfFP, _) -> emit' fpext
                (_, HalfFP) -> emit' fptrunc
                (FloatFP, _) -> emit' fpext
                (_, FloatFP) -> emit' fptrunc
                (DoubleFP, _) -> emit' fpext
                (_, DoubleFP) -> emit' fptrunc
                _ -> throwError (CastErr pos a b)
            (IntegerType _, FloatingPointType _) ->
                emit' $ if isInt a then sitofp else uitofp
            (FloatingPointType _, IntegerType _) ->
                emit' $ if isInt b then fptosi else fptoui
            _ -> throwError (CastErr pos a b)
    genDeref :: Val -> Gen Val
    genDeref = \case
        VVar x -> fmap VVar (selDeref x)
        VLocal x -> pure (VVar x)
    genStore :: Val -> Val -> Gen Val
    genStore x p = do
        x' <- getLocal x
        p' <- getLocal p
        emitDo (store x' p')
        pure p
    isNat = \case
        TNat _ -> True
        TNatSize -> True
        _ -> False
    isInt = \case
        Ast.TPrim p -> isInt' p
        _ -> False
    isInt' = \case
        TInt _ -> True
        TIntSize -> True
        _ -> False
    isFloat = \case
        TF16 -> True
        TF32 -> True
        TF64 -> True
        TF128 -> True
        _ -> False

apps :: Maybe TailCallKind -> Val -> [Val] -> Gen Val
apps tailkind f = \case
    [] -> pure f
    a : [] -> app tailkind f a
    a : as -> app (Just NoTail) f a >>= \f' -> apps tailkind f' as

app :: Maybe TailCallKind -> Val -> Val -> Gen Val
app tailkind closure a = do
    -- TODO: Cache the loaded & extracted closure components for the next time the
    --       function is called in the same scope! Probably just a Reader with `closure`
    --       as key and `(captures, f)` as value.
    closure' <- getLocal closure
    captures <- emitReg "captures" =<< extractvalue closure' [0]
    f <- emitReg "function" =<< extractvalue closure' [1]
    a' <- getLocal a
    let as = [(captures, []), (a', [])]
    let rt = getFunRet (getPointee (typeOf f))
    let returnsViaParam = rt == LLType.void
    fmap VLocal $ if returnsViaParam
        then emitDo (callIntern tailkind f as) $> litUnit
        else emitAnonReg $ WithRetType (callIntern tailkind f as) rt

selDeref :: Operand -> Gen Operand
selDeref x = emitAnonReg (load x)

-- | Assumes that the from-type and to-type are of the same size.
transmute :: Type -> Type -> Val -> Gen Val
transmute t u x = case (t, u) of
    (FunctionType _ _ _, _) -> transmuteIce
    (_, FunctionType _ _ _) -> transmuteIce
    (MetadataType, _) -> transmuteIce
    (_, MetadataType) -> transmuteIce
    (LabelType, _) -> transmuteIce
    (_, LabelType) -> transmuteIce
    (TokenType, _) -> transmuteIce
    (_, TokenType) -> transmuteIce
    (VoidType, _) -> transmuteIce
    (_, VoidType) -> transmuteIce

    (IntegerType _, IntegerType _) -> bitcast'
    (IntegerType _, PointerType _ _) ->
        getLocal x >>= \x' -> emitAnonReg (inttoptr x' u) <&> VLocal
    (IntegerType _, FloatingPointType _) -> bitcast'
    (IntegerType _, VectorType _ _) -> bitcast'

    (PointerType pt _, PointerType pu _) | pt == pu -> pure x
                                         | otherwise -> bitcast'
    (PointerType _ _, IntegerType _) ->
        getLocal x >>= \x' -> emitAnonReg (ptrtoint x' u) <&> VLocal
    (PointerType _ _, _) -> stackCast
    (_, PointerType _ _) -> stackCast

    (FloatingPointType _, FloatingPointType _) -> pure x
    (FloatingPointType _, IntegerType _) -> bitcast'
    (FloatingPointType _, VectorType _ _) -> bitcast'

    (VectorType _ vt, VectorType _ vu) | vt == vu -> pure x
                                       | otherwise -> bitcast'
    (VectorType _ _, IntegerType _) -> bitcast'
    (VectorType _ _, FloatingPointType _) -> bitcast'

    (StructureType _ _, _) -> stackCast
    (_, StructureType _ _) -> stackCast
    (ArrayType _ _, _) -> stackCast
    (_, ArrayType _ _) -> stackCast
    (NamedTypeReference _, _) -> stackCast
    (_, NamedTypeReference _) -> stackCast
  where
    transmuteIce = ice $ "transmute " ++ show t ++ " to " ++ show u
    bitcast' = getLocal x >>= \x' -> emitAnonReg (bitcast x' u) <&> VLocal
    stackCast = getVar x >>= \x' -> emitAnonReg (bitcast x' (LLType.ptr u)) <&> VVar

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
callExtern = call LLCallConv.C (Just NoTail)

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
    , ( "GC_add_roots"
      , ( [ Parameter (LLType.ptr i8) (mkName "low_address") []
          , Parameter (LLType.ptr i8) (mkName "high_address_plus_1") []
          ]
        , LLType.void
        )
      )
    ]

genExternTypeSig :: Ast.Type -> Gen' (([Ast.Type], Type), ([Parameter], Type))
genExternTypeSig t = do
    let (pts, rt) = uncurryType t
    when (null pts) $ ice "genExternTypeSig of non-function"
    let anon = mkName ""
    pts' <- mapM genType' pts
    ps <- forM pts' $ \pt' -> passByRef' pt' <&> \case
        True -> Parameter (LLType.ptr pt') anon [ByVal]
        False -> Parameter pt' anon []
    rt' <- genType' rt
    (rt'', ps') <- passByRef' rt' <&> \case
        True -> (LLType.void, Parameter (LLType.ptr rt') anon [SRet] : ps)
        False -> (rt', ps)
    pure ((pts, rt'), (ps', rt''))
  where
    uncurryType :: Ast.Type -> ([Ast.Type], Ast.Type)
    uncurryType = \case
        Ast.TFun a b -> first (a :) (uncurryType b)
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

genType :: Ast.Type -> Gen Type
genType = lift . genType'

-- | Convert to the LLVM representation of a type in an expression-context.
genType' :: MonadReader Env m => Ast.Type -> m Type
genType' = \case
    Ast.TPrim tc -> pure $ case tc of
        Ast.TNat w -> IntegerType w
        Ast.TNatSize -> i64
        Ast.TInt w -> IntegerType w
        Ast.TIntSize -> i64
        Ast.TF16 -> half
        Ast.TF32 -> float
        Ast.TF64 -> double
        Ast.TF128 -> fp128
    Ast.TFun a r -> liftA2 closureType (genType' a) (genType' r)
    Ast.TBox t -> fmap LLType.ptr (genType' t)
    Ast.TConst tc -> lookupEnum tc <&> \case
        Just 0 -> typeUnit
        Just w -> IntegerType w
        Nothing -> genDatatypeRef tc

genDatatypeRef :: Ast.TConst -> Type
genDatatypeRef = NamedTypeReference . mkName . mangleTConst

-- | A `Fun` is a closure, and follows a certain calling convention
--
--   A closure is represented as a pair where the first element is the pointer
--   to the structure of captures, and the second element is a pointer to the
--   actual function, which takes as first parameter the captures-pointer, and
--   as second parameter the argument.
closureType :: Type -> Type -> Type
closureType a r = typeStruct [typeGenericPtr, LLType.ptr (closureFunType a r)]

-- The type of the function itself within the closure
closureFunType :: Type -> Type -> Type
closureFunType a r =
    FunctionType { resultType = r, argumentTypes = [typeGenericPtr, a], isVarArg = False }

genCapturesType :: [Ast.TypedVar] -> Gen Type
genCapturesType = fmap typeStruct . mapM (\(Ast.TypedVar _ t) -> genType t)

genVariantType :: MonadReader Env m => Ast.Span -> [Ast.Type] -> m [Type]
genVariantType totVariants =
    fmap (maybe id ((:) . IntegerType) (tagBitWidth totVariants)) . mapM genType'

tagBitWidth :: Ast.Span -> Maybe Word32
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
sizeof :: MonadReader Env m => Type -> m Word64
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

alignmentof :: MonadReader Env m => Type -> m Word64
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

lookupEnum :: MonadReader Env m => Ast.TConst -> m (Maybe Word32)
lookupEnum tc = view (enumTypes . to (tconstLookup tc))

tconstLookup :: Ast.TConst -> Map Name a -> Maybe a
tconstLookup = Map.lookup . mkName . mangleTConst

lookupDatatype :: MonadReader Env m => Name -> m Type
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

add :: Operand -> Operand -> FunInstr
add a b = WithRetType (Add False False a b) (typeOf a)

fadd :: Operand -> Operand -> FunInstr
fadd a b = WithRetType (FAdd noFastMathFlags a b) (typeOf a)

sub :: Operand -> Operand -> FunInstr
sub a b = WithRetType (Sub False False a b) (typeOf a)

fsub :: Operand -> Operand -> FunInstr
fsub a b = WithRetType (FSub noFastMathFlags a b) (typeOf a)

mul :: Operand -> Operand -> FunInstr
mul a b = WithRetType (Mul False False a b) (typeOf a)

fmul :: Operand -> Operand -> FunInstr
fmul a b = WithRetType (FMul noFastMathFlags a b) (typeOf a)

udiv :: Operand -> Operand -> FunInstr
udiv a b = WithRetType (UDiv False a b) (typeOf a)

sdiv :: Operand -> Operand -> FunInstr
sdiv a b = WithRetType (SDiv False a b) (typeOf a)

fdiv :: Operand -> Operand -> FunInstr
fdiv a b = WithRetType (FDiv noFastMathFlags a b) (typeOf a)

urem :: Operand -> Operand -> FunInstr
urem a b = WithRetType (URem a b) (typeOf a)

srem :: Operand -> Operand -> FunInstr
srem a b = WithRetType (SRem a b) (typeOf a)

frem :: Operand -> Operand -> FunInstr
frem a b = WithRetType (FRem noFastMathFlags a b) (typeOf a)

shl :: Operand -> Operand -> FunInstr
shl a b = WithRetType (Shl False False a b) (typeOf a)

lshr :: Operand -> Operand -> FunInstr
lshr a b = WithRetType (LShr False a b) (typeOf a)

ashr :: Operand -> Operand -> FunInstr
ashr a b = WithRetType (AShr False a b) (typeOf a)

and' :: Operand -> Operand -> FunInstr
and' a b = WithRetType (And a b) (typeOf a)

or' :: Operand -> Operand -> FunInstr
or' a b = WithRetType (Or a b) (typeOf a)

xor :: Operand -> Operand -> FunInstr
xor a b = WithRetType (Xor a b) (typeOf a)

icmp :: LLIPred.IntegerPredicate -> Operand -> Operand -> FunInstr
icmp p a b = WithRetType (ICmp p a b) i1

fcmp :: LLFPred.FloatingPointPredicate -> Operand -> Operand -> FunInstr
fcmp p a b = WithRetType (FCmp p a b) i1

bitcast :: Operand -> Type -> FunInstr
bitcast x t = WithRetType (BitCast x t) t

inttoptr :: Operand -> Type -> FunInstr
inttoptr x t = WithRetType (IntToPtr x t) t

ptrtoint :: Operand -> Type -> FunInstr
ptrtoint x t = WithRetType (PtrToInt x t) t

trunc :: Operand -> Type -> FunInstr
trunc x t = WithRetType (Trunc x t) t

zext :: Operand -> Type -> FunInstr
zext x t = WithRetType (ZExt x t) t

sext :: Operand -> Type -> FunInstr
sext x t = WithRetType (SExt x t) t

fptrunc :: Operand -> Type -> FunInstr
fptrunc x t = WithRetType (FPTrunc x t) t

fpext :: Operand -> Type -> FunInstr
fpext x t = WithRetType (FPExt x t) t

fptoui :: Operand -> Type -> FunInstr
fptoui x t = WithRetType (FPToUI x t) t

fptosi :: Operand -> Type -> FunInstr
fptosi x t = WithRetType (FPToSI x t) t

uitofp :: Operand -> Type -> FunInstr
uitofp x t = WithRetType (UIToFP x t) t

sitofp :: Operand -> Type -> FunInstr
sitofp x t = WithRetType (SIToFP x t) t

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
litStructNamed :: Ast.TConst -> [LLConst.Constant] -> LLConst.Constant
litStructNamed t xs =
    let tname = mkName (mangleTConst t) in LLConst.Struct (Just tname) False xs

litRealWorld :: Operand
litRealWorld = litUnit

litUnit :: Operand
litUnit = ConstantOperand (LLConst.Array i8 [])

typeStr :: Type
typeStr = NamedTypeReference (mkName (mangleTConst TypeAst.tStr'))

typeBool :: Type
typeBool = i8

typeGenericPtr :: Type
typeGenericPtr = LLType.ptr i8

-- Why is Unit represented by a zero-length array instead of an empty struct? In short,
-- it's to prevent LLVM from performing a certain optimization which later prevents
-- tail-calls from being optimized.
--
-- The problem is that for tail recursive functions with return type Unit, LLVM optimizes
--
--   %x = tail call {} foo()
--   ret {} %x
--
-- to
--
--   %x = tail call {} foo()
--   ret {} zeroinitializer
--
-- However, this "optimization" prevents tail-call optimization from happening later, as
-- TCO requires us to return either void or the local of the return value of the last
-- call. zeroinitializer may have the same value as %x, but the optimizer doesn't
-- recognize it as fulfilling the conditions, so TCO doesn't happen. By representing Unit
-- as an empty array instead, this problem doesn't happen, because %x is simply not
-- replaced with zeroinitializer by LLVM when the type is an array type. Don't know why
-- this is the case, but it works out.
typeUnit :: Type
typeUnit = ArrayType 0 i8

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

mangleName :: (String, [Ast.Type]) -> String
mangleName = \case
    -- Instead of dealing with changing entrypoint name and startfiles, just
    -- call the outermost, compiler generated main `main`, and the user-defined
    -- main `_main`, via this `mangleName` mechanic.
    ("main", []) -> "_main"
    ("main", _) -> ice "mangleName of `main` of non-empty instantiation"
    (x, us) -> x ++ mangleInst us

mangleInst :: [Ast.Type] -> String
mangleInst ts =
    if not (null ts) then "<" ++ intercalate ", " (map mangleType ts) ++ ">" else ""

mangleType :: Ast.Type -> String
mangleType = \case
    Ast.TPrim c -> pretty c
    Ast.TFun p r -> mangleTConst ("Fun", [p, r])
    Ast.TBox t -> mangleTConst (TypeAst.tBox' t)
    Ast.TConst tc -> mangleTConst tc

mangleTConst :: Ast.TConst -> String
mangleTConst (c, ts) = c ++ mangleInst ts
