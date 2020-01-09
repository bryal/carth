{-# LANGUAGE OverloadedStrings, LambdaCase, TupleSections, FlexibleContexts #-}

-- | Generation of LLVM IR code from our monomorphic AST.
module Codegen (codegen) where

import LLVM.AST hiding (args)
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.AST.DataLayout
import LLVM.AST.ParameterAttribute
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Float as LLFloat
import qualified Codec.Binary.UTF8.String as UTF8.String
import Data.String
import System.FilePath
import Control.Monad.Writer
import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Word
import Data.Foldable
import Data.List
import Data.Functor
import Control.Applicative
import Control.Lens
    (modifying, scribe, (<<+=), (<<.=), use, uses, assign, views, locally)

import Misc
import FreeVars
import qualified MonoAst
import MonoAst hiding (Type, Const)
import Selections
import Gen
import Abi


-- | An instruction that returns a value. The name refers to the fact that a
--   mathematical function always returns a value, but an imperative procedure
--   may only produce side effects.
data FunInstruction = WithRetType Instruction Type

data Val
    = VVar Operand
    | VLocal Operand

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
            t' <- genType' t
            pure
                ( TypedVar name t
                , ConstantOperand
                    $ LLConst.GlobalReference (LLType.ptr t') (mkName name)
                )
        augment env (Map.fromList es') ga
    withGlobDefSigs sigs ga = do
        sigs' <- forM sigs $ \(v@(TypedVar x t), (us, _)) -> do
            t' <- genType' t
            pure
                ( v
                , ConstantOperand $ LLConst.GlobalReference
                    (LLType.ptr t')
                    (mkName (mangleName (x, us)))
                )
        augment env (Map.fromList sigs') ga

-- | A data-type is a tagged union, and we represent it in LLVM as a struct
--   where, if there are more than 1 variant, the first element is the
--   variant-index. The variant index is represented as an integer with the
--   smallest width 2^n that can fit all variants. The rest of the elements are
--   the field-types of the largest variant wrt allocation size.
defineDataTypes :: TypeDefs -> Gen' (Map Name Type)
defineDataTypes tds = do
    mfix $ \tds' ->
        fmap Map.fromList $ augment dataTypes tds' $ forM tds $ \(tc, vs) -> do
            let n = mkName (mangleTConst tc)
            let totVariants = length vs
            ts <- mapM (genVariantType (fromIntegral totVariants)) vs
            sizedTs <- mapM (\t -> fmap (\s -> (s, t)) (sizeof t)) ts
            if null sizedTs
                then ice ("defineDataTypes: sizedTs empty for def " ++ show n)
                else pure (n, snd (maximum sizedTs))

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
genExtern name t = genType' t
    <&> \t' -> GlobalDefinition $ simpleGlobVar' (mkName name) t' Nothing

genMain :: Gen' Definition
genMain = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    Out basicBlocks _ _ <- execWriterT $ do
        f <- lookupVar (TypedVar "start" startType)
        _ <- app f (VLocal litUnit) typeUnit
        commitFinalFuncBlock (ret (litI32 0))
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
    let closure = litStruct' [captures, fRef]
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
        (capturesParam, captureLocals) <- genExtractCaptures
        pt' <- genType pt
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
    ss <- mapM globStrVar globStrings
    ls <- concat <$> mapM (fmap (uncurry (:)) . genFunDef) lambdaFuncs
    let f = simpleFunc name fParams rt basicBlocks
    pure (f, concat ss ++ ls)
  where
    globStrVar (strName, s) = do
        name_inner <- newName' "strlit_inner"
        let bytes = UTF8.String.encode s
            len = length bytes
            tInner = ArrayType (fromIntegral len) i8
            defInner = simpleGlobVar
                name_inner
                tInner
                (LLConst.Array i8 (map litI8' bytes))
            inner = LLConst.GlobalReference (LLType.ptr tInner) name_inner
            ptrBytes = LLConst.BitCast inner (LLType.ptr i8)
            array = litStructNamed'
                ("Array", [TPrim TNat8])
                [ptrBytes, litI64' len]
            str = litStructNamed' ("Str", []) [array]
            defStr = simpleGlobVar strName typeStr str
        pure [defInner, defStr]
    genExtractCaptures = do
        capturesName <- newName "captures"
        let capturesPtrGenericType = LLType.ptr typeUnit
        let capturesPtrGeneric =
                LocalReference capturesPtrGenericType capturesName
        let capturesParam = (capturesPtrGenericType, capturesName)
        fmap (capturesParam, ) $ if null fvs
            then pure []
            else do
                capturesType <- genCapturesType fvs
                capturesPtr <- emitAnon
                    (bitcast capturesPtrGeneric (LLType.ptr capturesType))
                captures <- emitAnon (load capturesPtr)
                captureVals <- mapM
                    (\(TypedVar x _, i) ->
                        emitReg' x =<< extractvalue captures [i]
                    )
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
        Match e cs tbody -> genMatch e cs =<< genType tbody
        Ction c -> genCtion c
        Box e -> genBox =<< genExpr e
        Deref e -> genDeref e
        Absurd t -> fmap (VLocal . undef) (genType t)

genConst :: MonoAst.Const -> Gen Val
genConst = \case
    Unit -> pure (VLocal litUnit)
    Int n -> pure (VLocal (litI64 n))
    Double x -> pure (VLocal (litDouble x))
    Str s -> do
        var <- newName "strlit"
        scribe outStrings [(var, s)]
        pure $ VVar $ ConstantOperand
            (LLConst.GlobalReference (LLType.ptr typeStr) var)
    Bool b -> pure (VLocal (litBool b))

-- | Beta-reduction and closure application
genApp :: Expr -> Expr -> MonoAst.Type -> Gen Val
genApp fe' ae' rt' = genApp' (fe', [(ae', rt')])
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
                (\(ae, rt) -> liftA2 (,) (genExpr ae) (genType rt))
                aes
            foldlM (\f (a, rt) -> app f a rt) closure as

app :: Val -> Val -> Type -> Gen Val
app closure a rt = do
    closure' <- getLocal closure
    captures <- emitReg' "captures" =<< extractvalue closure' [0]
    f <- emitReg' "function" =<< extractvalue closure' [1]
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
genIf pred' conseq alt = do
    conseqL <- newName "consequent"
    altL <- newName "alternative"
    nextL <- newName "next"
    predV <- emitAnon . flip trunc i1 =<< getLocal =<< genExpr pred'
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
        t' <- genType t
        emitReg' n (alloca t')
    withVars (zip vs ps) $ do
        forM_ (zip ps es) $ \(p, (_, e)) -> do
            x <- getLocal =<< genExpr e
            emit (store x p)
        genExpr b

genMatch :: Expr -> DecisionTree -> Type -> Gen Val
genMatch m dt tbody = do
    -- TODO: Do we have to convert it to an operand here already? Keeping it as
    --       Val would probably eliminate a needless stack allocation.
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
    defaultL <- newName "default"
    nextL <- newName "next"
    (m, selections') <- select selAs selSub selDeref selector selections
    mVariantIx <- case typeOf m of
        IntegerType _ -> pure m
        _ -> emitReg' "found_variant_ix" =<< extractvalue m [0]
    let ixBits = getIntBitWidth (typeOf mVariantIx)
    let litIxInt = LLConst.Int ixBits
    let dests' = zip (map litIxInt variantIxs) variantLs
    commitToNewBlock (switch mVariantIx defaultL dests') defaultL
    let genDecisionTree' dt = do
            u <- genDecisionTree tbody dt selections'
            liftA2 (,) (getLocal u) (use currentBlockLabel)
    v <- genDecisionTree' def
    let genCase l dt = do
            commitToNewBlock (br nextL) l
            genDecisionTree' dt
    vs <- zipWithM genCase variantLs variantDts
    commitToNewBlock (br nextL) nextL
    fmap VLocal (emitAnon (phi (v : vs)))

genDecisionLeaf :: (MonoAst.VarBindings, Expr) -> Selections Operand -> Gen Val
genDecisionLeaf (bs, e) selections = do
    bs' <- selectVarBindings selAs selSub selDeref selections bs
    withLocals bs' (genExpr e)

selAs :: Span -> [MonoAst.Type] -> Operand -> Gen Operand
selAs totVariants ts matchee = do
    tvariant <- lift (genVariantType totVariants ts)
    let tgeneric = typeOf matchee
    pGeneric <- emitReg' "ction_ptr_generic" (alloca tgeneric)
    emit (store matchee pGeneric)
    p <- emitReg' "ction_ptr" (bitcast pGeneric (LLType.ptr tvariant))
    emitReg' "ction" (load p)

selSub :: Span -> Word32 -> Operand -> Gen Operand
selSub span' i matchee =
    let tagOffset = if span' > 1 then 1 else 0
    in emitReg' "submatchee" =<< extractvalue matchee (pure (tagOffset + i))

selDeref :: Operand -> Gen Operand
selDeref x = emitAnon (load x)

genCtion :: MonoAst.Ction -> Gen Val
genCtion (i, span', dataType, as) = do
    as' <- mapM genExpr as
    let tag = maybe
            id
            ((:) . VLocal . ConstantOperand . flip LLConst.Int i)
            (tagBitWidth span')
    s <- getLocal =<< genStruct (tag as')
    let t = typeOf s
    let tgeneric = genDatatypeRef dataType
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
    ft <- lift (genClosureFunType pt bt)
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
    size <- fmap (litI64 . fromIntegral) (lift (sizeof t))
    emitAnon (callExtern "carth_alloc" (LLType.ptr typeUnit) [size])

genDeref :: Expr -> Gen Val
genDeref e = genExpr e >>= \case
    VVar x -> fmap VVar (selDeref x)
    VLocal x -> pure (VVar x)

getVar :: Val -> Gen Operand
getVar = \case
    VVar x -> pure x
    VLocal x -> genStackAllocated x

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
    vPtr <- genStackAllocated v
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

genStackAllocated :: Operand -> Gen Operand
genStackAllocated v = do
    ptr <- emitAnon (alloca (typeOf v))
    emit (store v ptr)
    pure ptr

genType :: MonoAst.Type -> Gen Type
genType = lift . genType'

-- | Convert to the LLVM representation of a type in an expression-context.
genType' :: MonoAst.Type -> Gen' Type
genType' = \case
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
        TBool -> typeBool
    TFun a r -> genClosureType a r
    TBox t -> fmap LLType.ptr (genType' t)
    TConst t -> pure (genDatatypeRef t)

-- | A `Fun` is a closure, and follows a certain calling convention
--
--   A closure is represented as a pair where the first element is the pointer
--   to the structure of captures, and the second element is a pointer to the
--   actual function, which takes as first parameter the captures-pointer, and
--   as second parameter the argument.
--
--   An argument of a structure-type is passed by reference, to be compatible
--   with the C calling convention.
genClosureType :: MonoAst.Type -> MonoAst.Type -> Gen' Type
genClosureType a r = genClosureFunType a r
    <&> \c -> typeStruct [LLType.ptr typeUnit, LLType.ptr c]

-- The type of the function itself within the closure
genClosureFunType :: MonoAst.Type -> MonoAst.Type -> Gen' Type
genClosureFunType a r = do
    a' <- genType' a
    r' <- genType' r
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

genCapturesType :: [TypedVar] -> Gen Type
genCapturesType = fmap typeStruct . mapM (\(TypedVar _ t) -> genType t)

genDatatypeRef :: MonoAst.TConst -> Type
genDatatypeRef = NamedTypeReference . mkName . mangleTConst

genVariantType :: Span -> [MonoAst.Type] -> Gen' Type
genVariantType totVariants =
    fmap (typeStruct . maybe id ((:) . IntegerType) (tagBitWidth totVariants))
        . mapM genType'

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
callExtern f rt as = flip WithRetType rt $ Call
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

trunc :: Operand -> Type -> FunInstruction
trunc x t = WithRetType (Trunc x t []) t

insertvalue :: Operand -> Operand -> [Word32] -> FunInstruction
insertvalue s e is = WithRetType (InsertValue s e is []) (typeOf s)

extractvalue :: Operand -> [Word32] -> Gen FunInstruction
extractvalue struct is = fmap
    (WithRetType
        (ExtractValue { aggregate = struct, indices' = is, metadata = [] })
    )
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
        t ->
            ice
                $ "Tried to get member types of non-struct type "
                ++ pretty t

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

litI64 :: Int -> Operand
litI64 = ConstantOperand . litI64'

litI64' :: Int -> LLConst.Constant
litI64' = LLConst.Int 64 . toInteger

litI32 :: Int -> Operand
litI32 = ConstantOperand . LLConst.Int 32 . toInteger

litI8' :: Integral n => n -> LLConst.Constant
litI8' = LLConst.Int 8 . toInteger

litBool :: Bool -> Operand
litBool b = ConstantOperand $ LLConst.Int 8 $ if b then 1 else 0

litDouble :: Double -> Operand
litDouble = ConstantOperand . LLConst.Float . LLFloat.Double

litStruct :: [LLConst.Constant] -> Operand
litStruct = ConstantOperand . litStruct'

litStruct' :: [LLConst.Constant] -> LLConst.Constant
litStruct' = LLConst.Struct Nothing False

-- NOTE: typeOf Struct does not return NamedTypeReference of the structName, so
--       sometimes, an expression created from this will have the wrong
--       type. Specifically, I have observed this behaviour i phi-nodes. To
--       guard against it (until fixed upstream, hopefully), store the value in
--       a variable beforehand.
litStructNamed' :: TConst -> [LLConst.Constant] -> LLConst.Constant
litStructNamed' t xs =
    let tname = mkName (mangleTConst t) in LLConst.Struct (Just tname) False xs

litUnit :: Operand
litUnit = litStruct []

typeStruct :: [Type] -> Type
typeStruct ts = StructureType { isPacked = False, elementTypes = ts }

typeStr :: Type
typeStr = NamedTypeReference (mkName (mangleTConst ("Str", [])))

typeBool :: Type
typeBool = i8

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

getIntBitWidth :: Type -> Word32
getIntBitWidth = \case
    LLType.IntegerType w -> w
    t -> ice $ "Tried to get bit width of non-integer type " ++ pretty t

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

lookupVar :: TypedVar -> Gen Val
lookupVar x = do
    views env (Map.lookup x) >>= \case
        Just var -> pure (VVar var)
        Nothing -> ice $ "Undefined variable " ++ show x
