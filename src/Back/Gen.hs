{-# LANGUAGE TemplateHaskell, DuplicateRecordFields #-}

-- | Code generation operations, generally not restricted to be used with AST
--   inputs. Basically an abstraction over llvm-hs. Reusable operations that can
--   be used both in Codegen and for manually generating LLVM code in other
--   situations.
module Back.Gen where

import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative
import Data.Map (Map)
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Word
import Data.Foldable
import Data.Bifunctor
import Data.Functor
import Data.List
import qualified Data.Map as Map
import Lens.Micro.Platform (makeLenses, modifying, use, view, assign, to)
import LLVM.AST
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.AST.ParameterAttribute
import qualified LLVM.AST.CallingConvention as LLCallConv
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.AddrSpace as LLAddr
import qualified LLVM.AST.Linkage as LLLink
import qualified LLVM.AST.Visibility as LLVis
import qualified LLVM.AST.IntegerPredicate as LLIPred
import qualified LLVM.AST.FloatingPointPredicate as LLFPred

import Misc
import Pretty
import Sizeof (toBytes, wordsizeBits, tagBitWidth)
import qualified Front.TypeAst as TypeAst
import qualified Back.Low as Ast
import qualified Back.Lower as Ast
import Back.Low (TypedVar(..), TPrim(..))


-- | An instruction that returns a value. The name refers to the fact that a
--   mathematical function always returns a value, but an imperative procedure
--   may only produce side effects.
data FunInstr = WithRetType Instruction Type

type GlobalReference = (Type, Name)

data Env = Env
    { _localEnv :: Map TypedVar Val
    , _globalEnv :: Map TypedVar GlobalReference
    , _globalFunEnv :: Map TypedVar GlobalReference
    , _enumTypes :: Map Name Word32
    , _dataTypes :: Map Name [Type]
    , _builtins :: Map String ([Parameter], Type)
    , _strLits :: Vector Val
    }

data St = St
    { _currentBlockLabel :: Name
    , _currentBlockInstrs :: [Named Instruction]
    , _registerCount :: Word
    -- | Keep track of the parent function name so that we can name the
    --   outermost lambdas of a function definition well.
    , _lambdaParentFunc :: Maybe String
    }

type Gen' = StateT St (Reader Env)

-- | The output of generating a function. Dependencies of stuff within the
--   function that must be generated at the top-level.
data Out = Out
    { _outBlocks :: [BasicBlock]
    , _outFuncs :: [(Name, [TypedVar], TypedVar, Gen Type)]
    }

type Gen = WriterT Out Gen'

data Val
    = VVar Operand
    | VLocal Operand

makeLenses ''Env
makeLenses ''St
makeLenses ''Out


instance Semigroup Out where
    Out bs1 fs1 <> Out bs2 fs2 = Out (bs1 <> bs2) (fs1 <> fs2)
instance Monoid Out where
    mempty = Out [] []

instance Typed Val where
    typeOf = \case
        VVar x -> getPointee (typeOf x)
        VLocal x -> typeOf x


-- | Generates a function definition
--
--   The signature definition, the parameter-loading, and the result return are
--   all done according to the calling convention.
genFunDef :: (Name, [TypedVar], TypedVar, Gen Type) -> Gen' (Global, [Definition])
genFunDef (name, fvs, ptv@(TypedVar px pt), genBody) = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    ((rt, fParams), Out basicBlocks lambdaFuncs) <- runWriterT $ do
        (capturesParam, captureMembers) <- genExtractCaptures
        pt' <- genType pt
        px' <- newName px
        let pRef = VLocal (LocalReference pt' px')
        rt' <- withVal ptv pRef (withVals captureMembers genBody)
        let fParams' = [uncurry Parameter capturesParam [], Parameter pt' px' []]
        pure (rt', fParams')
    ls <- fmap
        concat
        (mapM (fmap (uncurry ((:) . GlobalDefinition)) . genFunDef) lambdaFuncs)
    let f = internFunc name fParams rt basicBlocks
    pure (f, ls)
  where
    genExtractCaptures :: Gen ((Type, Name), [(TypedVar, Val)])
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
                captureVals <- mapM
                    (\(TypedVar x _, i) ->
                        VVar <$> (emitReg x =<< getelementptr capturesPtr (litI64 0) [i])
                    )
                    (zip fvs [0 ..])
                pure (zip fvs captureVals)

genTailWrapInLambdas
    :: Type -> [TypedVar] -> [Ast.Type] -> ([TypedVar] -> Gen Val) -> Gen Type
genTailWrapInLambdas rt fvs ps genBody = do
    r <- getLocal =<< genWrapInLambdas rt fvs ps genBody
    commitFinalFuncBlock (Ret (Just r) [])
    pure (typeOf r)

genWrapInLambdas
    :: Type -> [TypedVar] -> [Ast.Type] -> ([TypedVar] -> Gen Val) -> Gen Val
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
    vs <- mapM lookupVar fvXs
    let t = typeStruct (map typeOf vs)
    ptr <- emitAnonReg (bitcast ptrGeneric (LLType.ptr t))
    genStructInPtr ptr vs

genLambda' :: TypedVar -> (Gen (), Type) -> Val -> [TypedVar] -> Gen Val
genLambda' p@(TypedVar _ pt) (genBody, bt) captures fvXs = do
    fname <- use lambdaParentFunc >>= \case
        Just s -> newName (s ++ "_lambda")
        Nothing -> newName "func"
    ft <- genType pt <&> \pt' -> closureFunType pt' bt
    let f = VLocal $ ConstantOperand $ LLConst.GlobalReference (LLType.ptr ft) fname
    scribe outFuncs [(fname, fvXs, p, genBody $> bt)]
    genStruct [captures, f]

runGen' :: StateT St (Reader Env) a -> a
runGen' g = runReader (evalStateT g initSt) initEnv
  where
    initEnv = Env { _localEnv = Map.empty
                  , _globalFunEnv = Map.empty
                  , _globalEnv = Map.empty
                  , _enumTypes = Map.empty
                  , _dataTypes = Map.empty
                  , _builtins = Map.empty
                  , _strLits = Vec.empty
                  }
    initSt = St { _currentBlockLabel = "entry"
                , _currentBlockInstrs = []
                , _registerCount = 0
                , _lambdaParentFunc = Nothing
                }

internFunc :: Name -> [Parameter] -> Type -> [BasicBlock] -> Global
internFunc n ps rt bs = Function { LLGlob.linkage = LLLink.External
                                 , LLGlob.visibility = LLVis.Default
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
                                 , LLGlob.metadata = []
                                 }

externFunc :: Name -> [Parameter] -> Type -> [BasicBlock] -> Global
externFunc n ps rt bs = Function { LLGlob.linkage = LLLink.External
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
                                 , LLGlob.metadata = []
                                 }

simpleGlobVar :: Name -> Type -> LLConst.Constant -> Global
simpleGlobVar name t = simpleGlobVar' False name t . Just

simpleGlobConst :: Name -> Type -> LLConst.Constant -> Global
simpleGlobConst name t = simpleGlobVar' True name t . Just

simpleGlobVar' :: Bool -> Name -> Type -> Maybe LLConst.Constant -> Global
simpleGlobVar' isconst name t initializer = GlobalVariable
    { LLGlob.name = name
    , LLGlob.linkage = LLLink.Private
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
    VLocal x -> do
        ptr <- emitAnonReg (alloca (typeOf x))
        _ <- genStore (VLocal x) (VLocal ptr)
        pure ptr

getLocal :: Val -> Gen Operand
getLocal = \case
    VVar x -> do
        let tpointee = getPointee (typeOf x)
        s <- sizeof tpointee
        if s == 0 then pure (undef tpointee) else emitAnonReg (load x)
    VLocal x -> pure x
  where
    load :: Operand -> FunInstr
    load p = WithRetType
        (Load { volatile = False
              , address = p
              , maybeAtomicity = Nothing
              , alignment = 0
              , metadata = []
              }
        )
        (getPointee (typeOf p))

withVals :: [(TypedVar, Val)] -> Gen a -> Gen a
withVals xs ma = foldr (uncurry withVal) ma xs

withVal :: TypedVar -> Val -> Gen a -> Gen a
withVal x v ga = do
    v' <- passByRef (typeOf v)
        >>= \b -> if b then fmap VVar (getVar v) else fmap VLocal (getLocal v)
    locally localEnv (Map.insert x v') ga

genStruct :: [Val] -> Gen Val
genStruct xs = do
    xs' <- mapM getLocal xs
    let (inits, vars) = foldr
            (flip $ \acc -> uncurry $ \i -> \case
                ConstantOperand c -> first (c :) acc
                x -> bimap (LLConst.Undef (typeOf x) :) ((i, x) :) acc
            )
            ([], [])
            (zip [0 ..] xs')
    let noConsts = length inits == length vars
    -- Prefill any constant operands, if there are any. Less line noise.
    let initial = if noConsts
            then undef (typeStruct (map typeOf xs'))
            else ConstantOperand (litStruct inits)
    fmap VLocal $ foldlM (\acc (i, x) -> emitAnonReg (insertvalue acc x [i])) initial vars

genStructInPtr :: Operand -> [Val] -> Gen ()
genStructInPtr ptr vs = forM_ (zip [0 ..] vs) $ \(i, v) -> do
    dest <- fmap VLocal . emitAnonReg =<< getelementptr ptr (litI64 0) [i]
    genStore v dest

genHeapAllocGeneric :: Type -> Gen Operand
genHeapAllocGeneric t = do
    size <- fmap fromIntegral (lift (sizeof t))
    if size == 0
        then pure (null' typeGenericPtr)
        else emitAnonReg =<< callBuiltin "GC_malloc" [litI64 size]

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
  where
    lookupVar' x = ask <&> \e -> asum
        [ Map.lookup x (_localEnv e)
        , fmap
            (VLocal
            . ConstantOperand
            . litStruct
            . (LLConst.Null typeGenericPtr :)
            . pure
            . uncurry LLConst.GlobalReference
            )
            (Map.lookup x (_globalFunEnv e))
        , fmap (VVar . ConstantOperand . uncurry LLConst.GlobalReference)
               (Map.lookup x (_globalEnv e))
        ]

genAppBuiltinVirtual :: TypedVar -> [Val] -> Gen Val
genAppBuiltinVirtual (TypedVar g t) as = do
    -- TODO: The arguments are not generated in the same scope as the application if the
    --       builtin virtual is partially applied. If it's fully applied, there's no
    --       problem, as no additional wrapping lambda scope will be created, and the
    --       local references to the argument values will be valid. If it's not applied at
    --       all, there's no problem, as there are no generated arguments to try to reach
    --       in the first place. Only partial application is a problem. Update: I've fixed
    --       this specific issue, right?
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
    let wrap xts genRt op = do
            rt' <- genRt
            if length as == length xts
                then op as
                else do
                    f <- genWrapInLambdas rt' [] xts (op <=< mapM lookupVar)
                    apps Nothing f as
        wrap1 f = case t of
            Ast.TFun a b -> wrap [a] (genType b) (\xs -> f (xs !! 0))
            _ -> err
        wrap2 f = case t of
            Ast.TFun a (Ast.TFun b c) ->
                wrap [a, b] (genType c) (\xs -> f (xs !! 0) (xs !! 1))
            _ -> err
    let ta = case t of
            Ast.TFun a _ -> a
            _ -> err
    let binop op a b = WithRetType (op a b []) (typeOf a)
        arithm u s f = \x y -> fmap VLocal . emitAnonReg =<< liftA2
            (binop (if isInt ta then s else if isFloat ta then f else u))
            (getLocal x)
            (getLocal y)
        bitwise u s = \x y -> fmap VLocal . emitAnonReg =<< liftA2
            (binop (if isInt ta then s else u))
            (getLocal x)
            (getLocal y)
        rel u s f = \x y ->
            let op = if isInt ta then icmp s else if isFloat ta then fcmp f else icmp u
                icmp p a b = WithRetType (ICmp p a b []) i1
                fcmp p a b = WithRetType (FCmp p a b []) i1
                zext x = WithRetType (ZExt x i8 []) i8
            in  fmap VLocal . emitAnonReg . zext =<< emitAnonReg =<< liftA2
                    op
                    (getLocal x)
                    (getLocal y)
    case g of
        "+" -> wrap2 $ arithm (Add False False) (Add False False) (FAdd noFastMathFlags)
        "-" -> wrap2 $ arithm (Sub False False) (Sub False False) (FSub noFastMathFlags)
        "*" -> wrap2 $ arithm (Mul False False) (Mul False False) (FMul noFastMathFlags)
        "/" -> wrap2 $ arithm (UDiv False) (SDiv False) (FDiv noFastMathFlags)
        "rem" -> wrap2 $ arithm URem SRem (FRem noFastMathFlags)
        "shift-l" -> wrap2 $ bitwise (Shl False False) (Shl False False)
        "shift-r" -> wrap2 $ bitwise (LShr False) (AShr False)
        "ashift-r" -> wrap2 $ bitwise (AShr False) (AShr False)
        "bit-and" -> wrap2 $ bitwise And And
        "bit-or" -> wrap2 $ bitwise Or Or
        "bit-xor" -> wrap2 $ bitwise Xor Xor
        -- NOTE: When comparing floats, one or both operands may be NaN. We can use either
        --       the `o` or `u` prefix to change how NaNs are treated by `fcmp`. I'm not
        --       sure, but I think that always using `o` will result in the most
        --       predictable code.
        "=" -> wrap2 $ rel LLIPred.EQ LLIPred.EQ LLFPred.OEQ
        "/=" -> wrap2 $ rel LLIPred.NE LLIPred.NE LLFPred.ONE
        ">" -> wrap2 $ rel LLIPred.UGT LLIPred.SGT LLFPred.OGT
        ">=" -> wrap2 $ rel LLIPred.UGE LLIPred.SGE LLFPred.OGE
        "<" -> wrap2 $ rel LLIPred.ULT LLIPred.SLT LLFPred.OLT
        "<=" -> wrap2 $ rel LLIPred.ULE LLIPred.SLE LLFPred.OLE
        "transmute" -> wrap1 $ case t of
            Ast.TFun a b -> \x -> genTransmute x a b
            _ -> err
        "cast" -> wrap1 $ case t of
            Ast.TFun a b -> \x -> genCast x a b
            _ -> err
        "deref" -> wrap1 $ genDeref
        "store" -> wrap2 $ genStore
        _ -> ice $ "genAppBuiltinVirtual: No builtin virtual function `" ++ g ++ "`"
  where
    err :: a
    err = ice $ "genAppBuiltinVirtual: " ++ g ++ " : " ++ pretty t

    -- Infer has checked that args to transmute are of the same size
    genTransmute :: Val -> Ast.Type -> Ast.Type -> Gen Val
    genTransmute x a b = do
        a' <- genType a
        b' <- genType b
        transmute a' b' x

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
        (IntegerType _, PointerType _ _) -> getLocal x
            >>= \x' -> emitAnonReg (WithRetType (IntToPtr x' u []) u) <&> VLocal
        (IntegerType _, FloatingPointType _) -> bitcast'
        (IntegerType _, VectorType _ _) -> bitcast'

        (PointerType pt _, PointerType pu _) | pt == pu -> pure x
                                             | otherwise -> bitcast'
        (PointerType _ _, IntegerType _) -> getLocal x
            >>= \x' -> emitAnonReg (WithRetType (PtrToInt x' u []) u) <&> VLocal
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

    genCast :: Val -> Ast.Type -> Ast.Type -> Gen Val
    genCast x a b = do
        a' <- genType a
        b' <- genType b
        let emit' instr = getLocal x
                >>= \x' -> emitAnonReg (WithRetType (instr x' b' []) b') <&> VLocal
        case (a', b') of
            _ | a' == b' -> pure x
            (IntegerType w1, IntegerType w2) ->
                emit' $ if w2 < w1 then Trunc else if isInt a then SExt else ZExt
            (FloatingPointType f1, FloatingPointType f2) -> case (f1, f2) of
                (HalfFP, _) -> emit' FPTrunc
                (_, HalfFP) -> emit' FPTrunc
                (FloatFP, _) -> emit' FPExt
                (_, FloatFP) -> emit' FPTrunc
                (DoubleFP, _) -> emit' FPExt
                (_, DoubleFP) -> emit' FPTrunc
                _ -> err
            (IntegerType _, FloatingPointType _) ->
                emit' $ if isInt a then SIToFP else UIToFP
            (FloatingPointType _, IntegerType _) ->
                emit' $ if isInt b then FPToSI else FPToUI
            _ -> err

    isInt = \case
        Ast.TPrim (TInt _) -> True
        Ast.TPrim TIntSize -> True
        _ -> False
    isFloat = \case
        Ast.TPrim TF16 -> True
        Ast.TPrim TF32 -> True
        Ast.TPrim TF64 -> True
        Ast.TPrim TF128 -> True
        _ -> False

genStore :: Val -> Val -> Gen Val
genStore x p = sizeof (typeOf x) >>= \s -> if s == 0
    then pure p
    else do
        x' <- getLocal x
        p' <- getLocal p
        emitDo (store x' p')
        pure p
  where
    store :: Operand -> Operand -> Instruction
    store srcVal destPtr = Store { volatile = False
                                 , address = destPtr
                                 , value = srcVal
                                 , maybeAtomicity = Nothing
                                 , alignment = 0
                                 , metadata = []
                                 }

apps :: Maybe TailCallKind -> Val -> [Val] -> Gen Val
apps tailkind f = \case
    [] -> pure f
    a : [] -> app tailkind f a
    a : as -> app (Just NoTail) f a >>= \f' -> apps tailkind f' as

-- TODO: Consider caching the loaded & extracted closure components for the next time
--       the function is called in the same scope! Probably just a Reader with
--       `closure` as key and `(captures, f)` as value. Might be beneficial.
app :: Maybe TailCallKind -> Val -> Val -> Gen Val
app tailkind closure a = do
    closure' <- fmap VLocal $ getLocal closure
    captures <- getLocal =<< genIndexStruct closure' [0]
    f <- getLocal =<< genIndexStruct closure' [1]
    a' <- getLocal a
    let as = [(captures, []), (a', [])]
    let rt = getFunRet (getPointee (typeOf f))
    let returnsViaParam = rt == LLType.void
    fmap VLocal $ if returnsViaParam
        then emitDo (callIntern tailkind f as) $> litUnit
        else emitAnonReg $ WithRetType (callIntern tailkind f as) rt

genDeref :: Val -> Gen Val
genDeref = fmap VVar . getLocal

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
    -> Instruction
callIntern = call LLCallConv.Fast

callExtern
    :: Operand
    -> [(Operand, [LLVM.AST.ParameterAttribute.ParameterAttribute])]
    -> Instruction
callExtern = call LLCallConv.C (Just NoTail)

call
    :: LLCallConv.CallingConvention
    -> Maybe TailCallKind
    -> Operand
    -> [(Operand, [LLVM.AST.ParameterAttribute.ParameterAttribute])]
    -> Instruction
call callconv tailkind f as = Call { tailCallKind = tailkind
                                   , callingConvention = callconv
                                   , returnAttributes = []
                                   , function = Right f
                                   , arguments = as
                                   , functionAttributes = []
                                   , metadata = []
                                   }

withBuiltins :: Gen' a -> Gen' a
withBuiltins ga = builtinExterns
    >>= \es -> augment builtins (Map.union builtinsHidden es) ga
    where builtinExterns = mapM (fmap snd . genExternTypeSig) Ast.builtinExterns

defineBuiltinsHidden :: [Definition]
defineBuiltinsHidden = map
    (\(x, (ps, tr)) -> GlobalDefinition (externFunc (mkName x) ps tr []))
    (Map.toList builtinsHidden)

builtinsHidden :: Map String ([Parameter], Type)
builtinsHidden = Map.fromList
    [ ("install_stackoverflow_handler", ([], LLType.void))
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
    pts' <- mapM genType pts
    ps <- forM pts' $ \pt' -> passByRef' pt' <&> \case
        True -> Parameter (LLType.ptr pt') anon [ByVal]
        False -> Parameter pt' anon []
    rt' <- genType rt
    (rt'', ps') <- passByRef' rt' <&> \case
        True -> (LLType.void, Parameter (LLType.ptr rt') anon [SRet] : ps)
        False -> (rt', ps)
    pure ((pts, rt'), (ps', rt''))
  where
    uncurryType :: Ast.Type -> ([Ast.Type], Ast.Type)
    uncurryType = \case
        Ast.TFun a b -> first (a :) (uncurryType b)
        x -> ([], x)

-- TODO: Split this into two versions: One for the x86 C calling convention, for external
--       declarations, and one for my own, for internal functions, which might differ a
--       little. For example, I don't see why function pointer should be passed behind an
--       extra level of indirection.
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

-- | Convert to the LLVM representation of a type in an expression-context.
genType :: MonadReader Env m => Ast.Type -> m Type
genType = \case
    Ast.TPrim tc -> pure $ case tc of
        Ast.TNat w -> IntegerType w
        Ast.TNatSize -> IntegerType wordsizeBits
        Ast.TInt w -> IntegerType w
        Ast.TIntSize -> IntegerType wordsizeBits
        Ast.TF16 -> half
        Ast.TF32 -> float
        Ast.TF64 -> double
        Ast.TF128 -> fp128
    Ast.TFun a r -> liftA2 closureType (genType a) (genType r)
    Ast.TBox t -> fmap LLType.ptr (genType t)
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
genVariantType totVariants = fmap (maybe id (:) (tagType totVariants)) . mapM genType

tagType :: Ast.Span -> Maybe Type
tagType = fmap IntegerType . tagBitWidth

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
    IntegerType bits -> pure (fromIntegral (toBytes bits))
    PointerType _ _ -> pure 8
    FloatingPointType HalfFP -> pure 2
    FloatingPointType FloatFP -> pure 4
    FloatingPointType DoubleFP -> pure 8
    FloatingPointType FP128FP -> pure 16
    FloatingPointType X86_FP80FP -> pure 16
    FloatingPointType PPC_FP128FP -> pure 16
    StructureType _ us -> do
        (s, a) <- foldlM addMember (0, 1) us
        pure $ s + (mod (a - s) a)
    VectorType n u -> fmap (fromIntegral n *) (sizeof u)
    ArrayType n u -> fmap (n *) (sizeof u)
    VoidType -> ice "sizeof VoidType"
    FunctionType _ _ _ -> ice "sizeof FunctionType"
    MetadataType -> ice "sizeof MetadataType"
    LabelType -> ice "sizeof LabelType"
    TokenType -> ice "sizeof TokenType"
  where
    addMember (accSize, maxAlign) u = do
        align <- alignmentof u
        let padding = if align == 0 then 0 else mod (align - accSize) align
        size <- sizeof u
        pure (accSize + padding + size, max align maxAlign)

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

emitDo :: Instruction -> Gen ()
emitNamedReg :: Name -> FunInstr -> Gen Operand
(emitDo, emitNamedReg) =
    ( emit' Do
    , \reg (WithRetType instr rt) -> emit' (reg :=) instr $> LocalReference rt reg
    )
  where
    emit' :: (Instruction -> Named Instruction) -> Instruction -> Gen ()
    emit' nameInstruction instr = do
        modifying currentBlockInstrs (nameInstruction instr :)

emitReg :: String -> FunInstr -> Gen Operand
emitReg s instr = newName s >>= flip emitNamedReg instr

emitAnonReg :: FunInstr -> Gen Operand
emitAnonReg instr = newAnonRegister >>= flip emitNamedReg instr
    where newAnonRegister = newName "tmp"

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

newName :: MonadState St m => String -> m Name
newName s = fmap (mkName . ((s ++ "_") ++) . show) (registerCount <<+= 1)

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

genIndexStruct :: Val -> [Word32] -> Gen Val
genIndexStruct v [] = pure v
genIndexStruct v is = case v of
    VLocal (ConstantOperand (LLConst.AggregateZero t)) -> undefIndexedLocal t
    VLocal (ConstantOperand (LLConst.Undef t)) -> undefIndexedLocal t
    VLocal (ConstantOperand (LLConst.Struct { memberValues = vs })) ->
        genIndexStruct (VLocal (ConstantOperand (vs !! fromIntegral (head is)))) (tail is)
    VLocal st -> fmap VLocal (emitAnonReg =<< extractvalue st is)
    VVar (ConstantOperand (LLConst.Null t)) -> nullIndexedVar t
    VVar (ConstantOperand (LLConst.Undef t)) -> nullIndexedVar t
    VVar ptr -> fmap VVar (emitAnonReg =<< getelementptr ptr (litI64 0) is)
  where
    undefIndexedLocal t = VLocal . undef <$> getIndexed t is
    nullIndexedVar t = VVar . null' . LLType.ptr <$> getIndexed (getPointee t) is

    extractvalue :: Operand -> [Word32] -> Gen FunInstr
    extractvalue struct is =
        fmap (WithRetType (ExtractValue struct is [])) (getIndexed (typeOf struct) is)

undef :: Type -> Operand
undef = ConstantOperand . LLConst.Undef

null' :: Type -> Operand
null' = ConstantOperand . LLConst.Null

bitcast :: Operand -> Type -> FunInstr
bitcast x t = WithRetType (BitCast x t []) t

trunc :: Operand -> Type -> FunInstr
trunc x t = WithRetType (Trunc x t []) t

insertvalue :: Operand -> Operand -> [Word32] -> FunInstr
insertvalue s e is = WithRetType (InsertValue s e is []) (typeOf s)

getelementptr :: Operand -> Operand -> [Word32] -> Gen FunInstr
getelementptr addr offset memberIs = fmap
    (WithRetType $ GetElementPtr
        { inBounds = False
        , address = addr
        , indices = offset : map (ConstantOperand . LLConst.Int 32 . toInteger) memberIs
        , metadata = []
        }
    )
    (fmap LLType.ptr (getIndexed (getPointee (typeOf addr)) memberIs))

phi :: [(Operand, Name)] -> FunInstr
phi = \case
    [] -> ice "phi was given empty list of cases"
    cs@((op, _) : _) -> let t = typeOf op in WithRetType (Phi t cs []) t

alloca :: Type -> FunInstr
alloca t = WithRetType (Alloca t Nothing 0 []) (LLType.ptr t)

litI64 :: Int -> Operand
litI64 = ConstantOperand . litI64'

litI64' :: Int -> LLConst.Constant
litI64' = LLConst.Int 64 . toInteger

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

getIndexed :: MonadReader Env m => (Integral n, Show n) => Type -> [n] -> m Type
getIndexed t is = foldlM
    (\t' i -> getMembers t' <&> \us -> if fromIntegral i < length us
        then us !! fromIntegral i
        else ice $ "getIndexed: index out of bounds: " ++ (show t ++ ", " ++ show is)
    )
    t
    is

getMembers :: MonadReader Env m => Type -> m [Type]
getMembers = \case
    NamedTypeReference x -> getMembers =<< lookupDatatype x
    StructureType _ members -> pure members
    t -> ice $ "Tried to get member types of non-struct type " ++ show t

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
