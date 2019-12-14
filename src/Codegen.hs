{-# LANGUAGE OverloadedStrings, LambdaCase, TemplateHaskell, TupleSections
           , FlexibleContexts #-}

-- | Generation of LLVM IR code from our monomorphic AST.
--
--   # On ABI / Calling Conventions
--
--   One might think that simply declaring all function definitions and function
--   calls as being of the same LLVM calling convention (e.g. "ccc") would allow
--   us to pass arguments and return results as we please, and everything will
--   be compatible? I sure did, however, that is not the case. To be compatible
--   with C FFIs, we also have to actually conform to the C calling convention,
--   which contains a bunch of details about how more complex types should be
--   passed and returned. Currently, we pass and return simple types by value,
--   and complex types by reference (param by ref, return via sret param).
--
--   See the definition of `passByRef` for up-to-date details about which types
--   are passed how.

module Codegen (codegen) where

import LLVM.AST
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.AST.DataLayout
import LLVM.AST.ParameterAttribute
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.CallingConvention as LLCallConv
import qualified LLVM.AST.Linkage as LLLink
import qualified LLVM.AST.Visibility as LLVis
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Float as LLFloat
import LLVM.AST.Global (Parameter)
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.AddrSpace as LLAddr
import qualified LLVM.AST.FunctionAttribute as LLFnAttr
import qualified Codec.Binary.UTF8.String as UTF8.String
import Data.String
import System.FilePath
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Char
import Data.Bool
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Word
import Data.Foldable
import Data.List
import Data.Composition
import Data.Functor
import Control.Applicative
import Control.Lens
    ( makeLenses
    , modifying
    , scribe
    , (<<+=)
    , (<<.=)
    , use
    , uses
    , assign
    , views
    , locally
    )

import Misc
import FreeVars
import qualified MonoAst
import MonoAst hiding (Type, Const)
import Selections


-- | An instruction that returns a value. The name refers to the fact that a
--   mathematical function always returns a value, but an imperative procedure
--   may only produce side effects.
data FunInstruction = WithRetType Instruction Type

data Val
    = VVar Operand
    | VLocal Operand

data Env = Env
    { _env :: Map TypedVar Operand  -- ^ Environment of stack allocated variables
    , _dataTypes :: Map Name Type
    }
makeLenses ''Env

data St = St
    { _currentBlockLabel :: Name
    , _currentBlockInstrs :: [Named Instruction]
    , _registerCount :: Word
    -- | Keep track of the parent function name so that we can name the
    --   outermost lambdas of a function definition well.
    , _lambdaParentFunc :: Maybe String
    , _outerLambdaN :: Word
    }
makeLenses ''St

type Gen' = StateT St (Reader Env)

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

instance Typed Val where
    typeOf = \case
        VVar x -> getPointee (typeOf x)
        VLocal x -> typeOf x


codegen :: DataLayout -> FilePath -> Program -> Module
codegen layout moduleFilePath (Program defs tdefs externs) =
    let
        defs' = Map.toList defs
        (tdefs', externs', globDefs) = runGen' $ do
            tdefs'' <- defineDataTypes tdefs
            withDataTypes tdefs''
                $ withExternSigs externs
                $ withGlobDefSigs defs'
                $ do
                    es <- genExterns externs
                    ds <- liftA2 (:) genMain (fmap join (mapM genGlobDef defs'))
                    pure (tdefs'', es, ds)
    in Module
        { moduleName = fromString ((takeBaseName moduleFilePath))
        , moduleSourceFileName = fromString moduleFilePath
        , moduleDataLayout = Just layout
        , moduleTargetTriple = Nothing
        , moduleDefinitions = concat
            [ map
                (\(n, tmax) -> TypeDefinition n (Just tmax))
                (Map.toList tdefs')
            , genBuiltins
            , externs'
            , globDefs
            ]
        }
  where
    withDataTypes = augment dataTypes
    withExternSigs es ga = do
        es' <- forM es $ \(name, t) -> do
            t' <- toLlvmType' t
            pure
                ( TypedVar name t
                , ConstantOperand
                    $ LLConst.GlobalReference (LLType.ptr t') (mkName name)
                )
        augment env (Map.fromList es') ga
    withGlobDefSigs sigs ga = do
        sigs' <- forM sigs $ \(v@(TypedVar x t), (us, _)) -> do
            t' <- toLlvmType' t
            pure
                ( v
                , ConstantOperand $ LLConst.GlobalReference
                    (LLType.ptr t')
                    (mkName (mangleName (x, us)))
                )
        augment env (Map.fromList sigs') ga

-- | Convert data-type definitions from `MonoAst` format to LLVM format, and
--   then return them as `Definition`s so that they may be exported in the
--   Module AST.
--
--   A data-type is a tagged union, and is represented in LLVM as a struct where
--   the first element is the variant-index as an i64, and the rest of the
--   elements are the field-types of the largest variant wrt allocation size.
defineDataTypes :: TypeDefs -> Gen' (Map Name Type)
defineDataTypes tds = do
    mfix $ \tds' ->
        fmap Map.fromList $ augment dataTypes tds' $ forM tds $ \(tc, vs) -> do
            let n = mkName (mangleTConst tc)
            ts <- mapM toLlvmVariantType vs
            sizedTs <- mapM (\t -> fmap (\s -> (s, t)) (sizeof t)) ts
            let (_, tmax) = maximum sizedTs
            pure (n, tmax)

runGen' :: Gen' a -> a
runGen' g = runReader
    (evalStateT g initSt)
    Env { _env = Map.empty, _dataTypes = Map.empty }

initSt :: St
initSt = St
    { _currentBlockLabel = "entry"
    , _currentBlockInstrs = []
    , _registerCount = 0
    , _lambdaParentFunc = Nothing
    , _outerLambdaN = 1
    }

genBuiltins :: [Definition]
genBuiltins = map
    (GlobalDefinition . ($ []))
    [ simpleFunc
        (mkName "carth_alloc")
        [Parameter i64 (mkName "size") []]
        (LLType.ptr typeUnit)
    ]

genExterns :: [(String, MonoAst.Type)] -> Gen' [Definition]
genExterns = mapM (uncurry genExtern)

genExtern :: String -> MonoAst.Type -> Gen' Definition
genExtern name t = toLlvmType' t
    <&> \t' -> GlobalDefinition $ simpleGlobVar' (mkName name) t' Nothing

genMain :: Gen' Definition
genMain = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    Out basicBlocks _ _ <- execWriterT $ do
        f <- lookupVar (TypedVar "start" startType)
        _ <- app f (VLocal (ConstantOperand litUnit)) typeUnit
        commitFinalFuncBlock (ret (ConstantOperand (litI32 0)))
    pure (GlobalDefinition (simpleFunc (mkName "main") [] i32 basicBlocks))

-- TODO: Change global defs to a new type that can be generated by llvm. As it
--       is now, global non-function variables can't be straight-forwardly
--       generated in general. Either, initialization is delayed until program
--       start, or an interpretation step is added between monomorphization and
--       codegen that evaluates all expressions in relevant contexts, like
--       constexprs.
genGlobDef :: (TypedVar, ([MonoAst.Type], Expr)) -> Gen' [Definition]
genGlobDef (TypedVar v _, (ts, e)) = case e of
    Fun p (body, _) ->
        fmap (map GlobalDefinition) (genClosureWrappedFunDef (v, ts) p body)
    _ -> nyi $ "Global non-function defs: " ++ show e

genClosureWrappedFunDef
    :: (String, [MonoAst.Type]) -> TypedVar -> Expr -> Gen' [Global]
genClosureWrappedFunDef var p body = do
    let name = mangleName var
    assign lambdaParentFunc (Just name)
    assign outerLambdaN 1
    let fName = mkName (name ++ "_func")
    (f, gs) <- genFunDef (fName, [], p, body)
    let fRef = LLConst.GlobalReference (LLType.ptr (typeOf f)) fName
    let capturesType = LLType.ptr typeUnit
    let captures = LLConst.Null capturesType
    let closure = litStruct [captures, fRef]
    let closureDef = simpleGlobVar (mkName name) (typeOf closure) closure
    pure (closureDef : f : gs)

-- | Generates a function definition
--
--   The signature definition, the parameter-loading, and the result return are
--   all done according to the calling convention.
genFunDef :: (Name, [TypedVar], TypedVar, Expr) -> Gen' (Global, [Global])
genFunDef (name, fvs, ptv@(TypedVar px pt), body) = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    ((rt, fParams), Out basicBlocks globStrings lambdaFuncs) <- runWriterT $ do
        (capturesParam, captureLocals) <- genExtractCaptures fvs
        pt' <- toLlvmType pt
        px' <- newName px
        -- Load params according to calling convention
        passParamByRef <- passByRef pt'
        let (withParam, pt'', pattrs) = if passParamByRef
                then (withVar, LLType.ptr pt', [ByVal])
                else (withLocal, pt', [])
        let pRef = LocalReference pt'' px'
        result <- getLocal
            =<< withParam ptv pRef (withLocals captureLocals (genExpr body))
        let rt' = typeOf result
        let fParams' =
                [uncurry Parameter capturesParam [], Parameter pt'' px' pattrs]
        -- Return result according to calling convention
        returnResultByRef <- passByRef rt'
        if returnResultByRef
            then do
                let out = (LLType.ptr rt', mkName "out")
                emit (store result (uncurry LocalReference out))
                commitFinalFuncBlock retVoid
                pure (LLType.void, uncurry Parameter out [SRet] : fParams')
            else do
                commitFinalFuncBlock (ret result)
                pure (rt', fParams')
    let ss = map globStrVar globStrings
    ls <- concat <$> mapM (fmap (uncurry (:)) . genFunDef) lambdaFuncs
    let f = simpleFunc name fParams rt basicBlocks
    pure (f, ss ++ ls)

genExtractCaptures :: [TypedVar] -> Gen ((Type, Name), [(TypedVar, Operand)])
genExtractCaptures fvs = do
    capturesName <- newName "captures"
    let capturesPtrGenericType = LLType.ptr typeUnit
    let capturesPtrGeneric = LocalReference capturesPtrGenericType capturesName
    let capturesParam = (capturesPtrGenericType, capturesName)
    fmap (capturesParam, ) $ if null fvs
        then pure []
        else do
            capturesType <- typeCaptures fvs
            capturesPtr <- emitAnon
                (bitcast capturesPtrGeneric (LLType.ptr capturesType))
            captures <- emitAnon (load capturesPtr)
            captureVals <- mapM
                (\(TypedVar x _, i) -> emitReg' x (extractvalue captures [i]))
                (zip fvs [0 ..])
            pure (zip fvs captureVals)

genExpr :: Expr -> Gen Val
genExpr expr = do
    parent <- lambdaParentFunc <<.= Nothing
    case expr of
        Lit c -> genConst c
        Var (TypedVar x t) -> lookupVar (TypedVar x t)
        App f e rt -> genApp f e rt
        If p c a -> genIf p c a
        Fun p b -> assign lambdaParentFunc parent *> genLambda p b
        Let ds b -> genLet ds b
        Match e cs tbody -> genMatch e cs =<< toLlvmType tbody
        Ction c -> genCtion c
        Box e -> genBox =<< genExpr e
        Deref e -> genDeref e

toLlvmDataType :: MonoAst.TConst -> Type
toLlvmDataType = typeNamed . mangleTConst

toLlvmVariantType :: [MonoAst.Type] -> Gen' Type
toLlvmVariantType = fmap (typeStruct . (i64 :)) . mapM toLlvmType'

toLlvmType :: MonoAst.Type -> Gen Type
toLlvmType = lift . toLlvmType'

-- | Convert to the LLVM representation of a type in an expression-context.
toLlvmType' :: MonoAst.Type -> Gen' Type
toLlvmType' = \case
    TPrim tc -> pure $ case tc of
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
    TFun a r -> toLlvmClosureType a r
    TBox t -> fmap LLType.ptr (toLlvmType' t)
    TConst t -> pure $ typeNamed (mangleTConst t)

-- | A `Fun` is a closure, and follows a certain calling convention
--
--   A closure is represented as a pair where the first element is the pointer
--   to the structure of captures, and the second element is a pointer to the
--   actual function, which takes as first parameter the captures-pointer, and
--   as second parameter the argument.
--
--   An argument of a structure-type is passed by reference, to be compatible
--   with the C calling convention.
toLlvmClosureType :: MonoAst.Type -> MonoAst.Type -> Gen' Type
toLlvmClosureType a r = toLlvmClosureFunType a r
    <&> \c -> typeStruct [LLType.ptr typeUnit, LLType.ptr c]

-- The type of the function itself within the closure
toLlvmClosureFunType :: MonoAst.Type -> MonoAst.Type -> Gen' Type
toLlvmClosureFunType a r = do
    a' <- toLlvmType' a
    r' <- toLlvmType' r
    passArgByRef <- passByRef' a'
    let a'' = if passArgByRef then LLType.ptr a' else a'
    returnResultByRef <- passByRef' r'
    pure $ if returnResultByRef
        then FunctionType
            { resultType = LLType.void
            , argumentTypes = [LLType.ptr r', LLType.ptr typeUnit, a'']
            , isVarArg = False
            }
        else FunctionType
            { resultType = r'
            , argumentTypes = [LLType.ptr typeUnit, a'']
            , isVarArg = False
            }

genConst :: MonoAst.Const -> Gen Val
genConst = fmap (VLocal . ConstantOperand) . \case
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

lookupVar :: TypedVar -> Gen Val
lookupVar x = do
    views env (Map.lookup x) >>= \case
        Just var -> pure (VVar var)
        Nothing -> ice $ "Undefined variable " ++ show x

-- | Beta-reduction and closure application
genApp :: Expr -> Expr -> MonoAst.Type -> Gen Val
genApp fe ae rt = genApp' (fe, [(ae, rt)])
  where
    -- TODO: Could/should the beta-reduction maybe happen in an earlier stage,
    --       like when desugaring?
    genApp' = \case
        (Fun p (b, _), (ae, _) : aes) -> do
            a <- genExpr ae
            withVal p a (genApp' (b, aes))
        (App fe ae rt, aes) -> genApp' (fe, (ae, rt) : aes)
        (fe, []) -> genExpr fe
        (fe, aes) -> do
            closure <- genExpr fe
            as <- mapM
                (\(ae, rt) -> liftA2 (,) (genExpr ae) (toLlvmType rt))
                aes
            foldlM (\f (a, rt) -> app f a rt) closure as

app :: Val -> Val -> Type -> Gen Val
app closure a rt = do
    closure' <- getLocal closure
    captures <- emitReg' "captures" (extractvalue closure' [0])
    f <- emitReg' "function" (extractvalue closure' [1])
    passArgByRef <- passByRef (typeOf a)
    (a', aattrs) <- if passArgByRef
        then fmap (, [ByVal]) (getVar a)
        else fmap (, []) (getLocal a)
    let args = [(captures, []), (a', aattrs)]
    returnByRef <- passByRef rt
    if returnByRef
        then do
            out <- emitReg' "out" (alloca rt)
            emit'' $ call f ((out, [SRet]) : args)
            pure (VVar out)
        else fmap VLocal (emitAnon (call f args))
  where
    call f as = WithRetType
        (Call
            -- NOTE: Just marking all calls as "tail" did not work out
            --       well. Lotsa segfaults and stuff! Learn more about what
            --       exactly "tail" does first. Maybe it's only ok to mark calls
            --       that are actually in tail position as tail calls?
            { tailCallKind = Nothing
            , callingConvention = cfg_callConv
            , returnAttributes = []
            , function = Right f
            , arguments = as
            , functionAttributes = []
            , metadata = []
            }
        )
        (getFunRet (getPointee (typeOf f)))

genIf :: Expr -> Expr -> Expr -> Gen Val
genIf pred conseq alt = do
    conseqL <- newName "consequent"
    altL <- newName "alternative"
    nextL <- newName "next"
    predV <- getLocal =<< genExpr pred
    commitToNewBlock (condbr predV conseqL altL) conseqL
    conseqV <- getLocal =<< genExpr conseq
    fromConseqL <- use currentBlockLabel
    commitToNewBlock (br nextL) altL
    altV <- getLocal =<< genExpr alt
    fromAltL <- use currentBlockLabel
    commitToNewBlock (br nextL) nextL
    fmap VLocal (emitAnon (phi [(conseqV, fromConseqL), (altV, fromAltL)]))

genLet :: Defs -> Expr -> Gen Val
genLet ds b = do
    let (vs, es) = unzip (Map.toList ds)
    ps <- forM vs $ \(TypedVar n t) -> do
        t' <- toLlvmType t
        emitReg' n (alloca t')
    withVars (zip vs ps) $ do
        forM_ (zip ps es) $ \(p, (_, e)) -> do
            x <- getLocal =<< genExpr e
            emit (store x p)
        genExpr b

genMatch :: Expr -> DecisionTree -> Type -> Gen Val
genMatch m dt tbody = do
    m' <- getLocal =<< genExpr m
    genDecisionTree tbody dt (newSelections m')

genDecisionTree :: Type -> DecisionTree -> Selections Operand -> Gen Val
genDecisionTree tbody = \case
    MonoAst.DSwitch selector cs def -> genDecisionSwitch selector cs def tbody
    MonoAst.DLeaf l -> genDecisionLeaf l

genDecisionSwitch
    :: MonoAst.Access
    -> Map VariantIx DecisionTree
    -> DecisionTree
    -> Type
    -> Selections Operand
    -> Gen Val
genDecisionSwitch selector cs def tbody selections = do
    let (variantIxs, variantDts) = unzip (Map.toAscList cs)
    variantLs <- mapM (newName . (++ "_") . ("variant_" ++) . show) variantIxs
    let dests = zip (map litU64 variantIxs) variantLs
    defaultL <- newName "default"
    nextL <- newName "next"
    (m, selections') <- select genAs genSub selector selections
    mVariantIx <- emitReg' "found_variant_ix" (extractvalueFromNamed m i64 [0])
    commitToNewBlock (switch mVariantIx defaultL dests) defaultL
    v <- getLocal =<< genDecisionTree tbody def selections'
    let genCase l dt = do
            commitToNewBlock (br nextL) l
            genDecisionTree tbody dt selections'
    vs <- zipWithM ((getLocal <=<) . genCase) variantLs variantDts
    commitToNewBlock (br nextL) nextL
    fmap VLocal (emitAnon (phi (zip (v : vs) (defaultL : variantLs))))

genDecisionLeaf :: (MonoAst.VarBindings, Expr) -> Selections Operand -> Gen Val
genDecisionLeaf (bs, e) selections =
    flip withLocals (genExpr e) =<< selectVarBindings genAs genSub selections bs

genAs :: [MonoAst.Type] -> Operand -> Gen Operand
genAs ts matchee = do
    tvariant <- lift (toLlvmVariantType ts)
    let tgeneric = typeOf matchee
    pGeneric <- emitReg' "ction_ptr_generic" (alloca tgeneric)
    emit (store matchee pGeneric)
    p <- emitReg' "ction_ptr" (bitcast pGeneric (LLType.ptr tvariant))
    emitReg' "ction" (load p)

genSub :: Word32 -> Operand -> Gen Operand
genSub i matchee = emitReg' "submatchee" (extractvalue matchee (pure (i + 1)))

genCtion :: MonoAst.Ction -> Gen Val
genCtion (i, tdef, as) = do
    as' <- mapM genExpr as
    s <- getLocal =<< genStruct (VLocal (litU64' i) : as')
    let t = typeOf s
    let tgeneric = toLlvmDataType tdef
    pGeneric <- emitReg' "ction_ptr_generic" (alloca tgeneric)
    p <- emitReg' "ction_ptr" (bitcast pGeneric (LLType.ptr t))
    emit (store s p)
    pure (VVar pGeneric)

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
genLambda :: TypedVar -> (Expr, MonoAst.Type) -> Gen Val
genLambda p@(TypedVar px pt) (b, bt) = do
    let fvs = Set.toList (Set.delete (TypedVar px pt) (freeVars b))
    captures <- genBoxGeneric =<< genStruct =<< mapM lookupVar fvs
    fname <- use lambdaParentFunc >>= \case
        Just s ->
            fmap (mkName . ((s ++ "_func_") ++) . show) (outerLambdaN <<+= 1)
        Nothing -> newName "func"
    ft <- lift (toLlvmClosureFunType pt bt)
    let
        f = VLocal $ ConstantOperand $ LLConst.GlobalReference
            (LLType.ptr ft)
            fname
    scribe outFuncs [(fname, fvs, p, b)]
    genStruct [captures, f]

genStruct :: [Val] -> Gen Val
genStruct xs = do
    xs' <- mapM getLocal xs
    let t = typeStruct (map typeOf xs')
    fmap VLocal $ foldlM
        (\s (i, x) -> emitAnon (insertvalue s x [i]))
        (undef t)
        (zip [0 ..] xs')

genBoxGeneric :: Val -> Gen Val
genBoxGeneric = fmap snd . genBox'

genBox :: Val -> Gen Val
genBox = fmap fst . genBox'

genBox' :: Val -> Gen (Val, Val)
genBox' x = do
    let t = typeOf x
    ptrGeneric <- genHeapAlloc t
    ptr <- emitAnon (bitcast ptrGeneric (LLType.ptr t))
    x' <- getLocal x
    emit (store x' ptr)
    pure (VLocal ptr, VLocal ptrGeneric)

genHeapAlloc :: Type -> Gen Operand
genHeapAlloc t = do
    size <- fmap litU64' (lift (sizeof t))
    emitAnon (callExtern "carth_alloc" (LLType.ptr typeUnit) [size])

genDeref :: Expr -> Gen Val
genDeref e = genExpr e >>= \case
    VVar x -> fmap VVar (emitAnon (load x))
    VLocal x -> pure (VVar x)

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

getVar :: Val -> Gen Operand
getVar = \case
    VVar x -> pure x
    VLocal x -> genStackAllocated' x

getLocal :: Val -> Gen Operand
getLocal = \case
    VVar x -> emitAnon (load x)
    VLocal x -> pure x

withLocals :: [(TypedVar, Operand)] -> Gen a -> Gen a
withLocals = flip (foldr (uncurry withLocal))

-- | Takes a local value, allocates a variable for it, and runs a generator in
--   the environment with the variable
withLocal :: TypedVar -> Operand -> Gen a -> Gen a
withLocal x v gen = do
    vPtr <- genVar' x (pure v)
    withVar x vPtr gen

withVars :: [(TypedVar, Operand)] -> Gen a -> Gen a
withVars = flip (foldr (uncurry withVar))

-- | Takes a local, stack allocated value, and runs a generator in the
--   environment with the variable
withVar :: TypedVar -> Operand -> Gen a -> Gen a
withVar x v = locally env (Map.insert x v)

withVal :: TypedVar -> Val -> Gen a -> Gen a
withVal x v ga = do
    var <- getVar v
    withVar x var ga

genVar :: Name -> Gen Operand -> Gen Operand
genVar n gen = genStackAllocated n =<< gen

genVar' :: TypedVar -> Gen Operand -> Gen Operand
genVar' (TypedVar x _) gen = do
    n <- newName x
    ptr <- genVar n gen
    pure ptr

genStackAllocated' :: Operand -> Gen Operand
genStackAllocated' v = flip genStackAllocated v =<< newAnonRegister

genStackAllocated :: Name -> Operand -> Gen Operand
genStackAllocated n v = do
    ptr <- emitReg n (alloca (typeOf v))
    emit (store v ptr)
    pure ptr

emit :: Instruction -> Gen ()
emit instr = emit' (Do instr)

emit' :: Named Instruction -> Gen ()
emit' = modifying currentBlockInstrs . (:)

emit'' :: FunInstruction -> Gen ()
emit'' (WithRetType instr _) = emit instr

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

-- TODO: Shouldn't need a return type parameter. Should look at global list of
--       hidden builtins or something.
callExtern :: String -> Type -> [Operand] -> FunInstruction
callExtern f rt as = WithRetType (callExtern'' f rt as) rt

callExtern'' :: String -> Type -> [Operand] -> Instruction
callExtern'' f rt as = Call
    { tailCallKind = Nothing
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

retVoid :: Terminator
retVoid = Ret Nothing []

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

-- Seems like just setting the type-field doesn't always do it. Sometimes the
-- named type is just left off? Happened when generating a string. Add a bitcast
-- for safe measure.
litStructOfType :: TConst -> [LLConst.Constant] -> LLConst.Constant
litStructOfType t xs =
    let
        tname = mkName (mangleTConst t)
        t' = NamedTypeReference tname
    in LLConst.BitCast
        (LLConst.Struct (Just (mkName (mangleTConst t))) False xs)
        t'

litUnit :: LLConst.Constant
litUnit = litStruct []

typeCaptures :: [TypedVar] -> Gen Type
typeCaptures = fmap typeStruct . mapM (\(TypedVar _ t) -> toLlvmType t)

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

mangleName :: (String, [MonoAst.Type]) -> String
mangleName (x, us) = x ++ mangleInst us

mangleInst :: [MonoAst.Type] -> String
mangleInst ts = if not (null ts)
    then "<" ++ intercalate ", " (map mangleType ts) ++ ">"
    else ""

mangleType :: MonoAst.Type -> String
mangleType = \case
    TPrim c -> pretty c
    TFun p r -> mangleTConst ("Fun", [p, r])
    TBox t -> mangleTConst ("Box", [t])
    TConst tc -> mangleTConst tc

mangleTConst :: TConst -> String
mangleTConst (c, ts) = c ++ mangleInst ts

passByRef :: Type -> Gen Bool
passByRef = lift . passByRef'

-- NOTE: This post is helpful:
--       https://stackoverflow.com/questions/42411819/c-on-x86-64-when-are-structs-classes-passed-and-returned-in-registers
--       Also, official docs:
--       https://software.intel.com/sites/default/files/article/402129/mpx-linux64-abi.pdf
--       particularly section 3.2.3 Parameter Passing (p18).
passByRef' :: Type -> Gen' Bool
passByRef' = \case
    NamedTypeReference x -> passByRef' =<< views dataTypes (Map.! x)
    -- Simple scalar types. They go in registers.
    VoidType -> pure False
    IntegerType _ -> pure False
    PointerType _ _ -> pure False
    FloatingPointType _ -> pure False
    -- Functions are not POD (Plain Ol' Data), so they are passed on the stack.
    FunctionType _ _ _ -> pure True
    -- TODO: Investigate how exactly SIMD vectors are to be passed when/if we
    --       ever add support for that in the rest of the compiler.
    VectorType _ _ -> pure True
    -- Aggregate types can either be passed on stack or in regs, depending on
    -- what they contain.
    t@(StructureType _ us) -> do
        size <- sizeof t
        if size > 16 then pure True else fmap or (mapM passByRef' us)
    ArrayType _ u -> do
        size <- sizeof u
        if size > 16 then pure True else passByRef' u
    -- N/A
    MetadataType -> ice "passByRef of MetadataType"
    LabelType -> ice "passByRef of LabelType"
    TokenType -> ice "passByRef of TokenType"

-- TODO: Handle packed
--
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
sizeof :: Type -> Gen' Word64
sizeof = \case
    NamedTypeReference x -> sizeof =<< lookupDataType x
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
        let padding = align - mod accSize align
        size <- sizeof u
        pure (accSize + padding + size)

alignmentof :: Type -> Gen' Word64
alignmentof = \case
    NamedTypeReference x -> alignmentof =<< lookupDataType x
    StructureType _ us -> fmap maximum (traverse alignmentof us)
    VectorType _ u -> alignmentof u
    ArrayType _ u -> alignmentof u
    t -> sizeof t

lookupDataType :: Name -> Gen' Type
lookupDataType x = views dataTypes (Map.lookup x) >>= \case
    Just u -> pure u
    Nothing -> ice $ "Undefined datatype " ++ show x

-- TODO: Try out "tailcc" - Tail callable calling convention. It looks like
--       exactly what I want!
cfg_callConv :: LLCallConv.CallingConvention
cfg_callConv = LLCallConv.C
