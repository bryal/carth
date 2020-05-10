{-# LANGUAGE OverloadedStrings, LambdaCase, TupleSections, FlexibleContexts #-}

-- | Generation of LLVM IR code from our monomorphic AST.
module Codegen (codegen) where

import LLVM.AST hiding (args)
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.AST.DataLayout
import qualified LLSubprog
import qualified LLCompunit
import qualified LLVM.AST.Operand as LLOp
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.Constant as LLConst
import Data.String
import System.FilePath
import Control.Monad.Writer
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Word
import Data.Maybe
import Data.Foldable
import Data.List
import Data.Function
import Data.Functor
import Data.Bifunctor
import Control.Applicative
import Lens.Micro.Platform (use, assign)

import Misc
import SrcPos
import FreeVars
import qualified Monomorphic
import Monomorphic hiding (Type, Const)
import Selections
import Gen
import Extern


codegen :: DataLayout -> FilePath -> Program -> Module
codegen layout moduleFilePath (Program (Topo defs) tdefs externs) =
    let
        (tdefs', externs', globDefs) = runGen' $ do
            (enums, tdefs'') <- defineDataTypes tdefs
            augment enumTypes enums
                $ augment dataTypes tdefs''
                $ withExternSigs externs
                $ withGlobDefSigs (map (second unpos) defs)
                $ do
                    es <- genExterns externs
                    ds <- liftA2 (:) genMain (fmap join (mapM genGlobDef defs))
                    pure (tdefs'', es, ds)
    in
        Module
            { moduleName = fromString ((takeBaseName moduleFilePath))
            , moduleSourceFileName = fromString moduleFilePath
            , moduleDataLayout = Just layout
            , moduleTargetTriple = Nothing
            , moduleDefinitions = concat
                [ map
                    (\(n, tmax) -> TypeDefinition n (Just (typeStruct tmax)))
                    (Map.toList tdefs')
                , genBuiltins
                , externs'
                , globDefs
                , globMetadataDefs
                ]
            }
  where
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
    fileId = MetadataNodeID 1
    debugInfoVersionId = MetadataNodeID 2
    globMetadataDefs =
        [ MetadataNodeDefinition compileUnitId
            $ DINode (LLOp.DIScope (LLOp.DICompileUnit compileUnitDef))
        , MetadataNodeDefinition fileId
            $ DINode (LLOp.DIScope (LLOp.DIFile fileDef))
        , MetadataNodeDefinition debugInfoVersionId $ MDTuple
            [ Just (MDValue (litI32 2))
            , Just (MDString "Debug Info Version")
            , Just (MDValue (litI32 3))
            ]
        , NamedMetadataDefinition "llvm.dbg.cu" [compileUnitId]
        , NamedMetadataDefinition "llvm.module.flags" [debugInfoVersionId]
        ]
    compileUnitDef = LLCompunit.CompileUnit
        { LLCompunit.language =
            let unstandardized_c = 1 in unstandardized_c
        , LLCompunit.file = MDRef fileId
        , LLCompunit.producer = "carth version alpha"
        , LLCompunit.optimized = False
        , LLCompunit.flags = ""
        , LLCompunit.runtimeVersion = 0
        , LLCompunit.splitDebugFileName = ""
        , LLCompunit.emissionKind = LLOp.FullDebug
        , LLCompunit.enums = []
        , LLCompunit.retainedTypes = []
        , LLCompunit.globals = []
        , LLCompunit.imports = []
        , LLCompunit.macros = []
        , LLCompunit.dWOId = 0
        , LLCompunit.splitDebugInlining = False
        , LLCompunit.debugInfoForProfiling = False
        , LLCompunit.nameTableKind = LLOp.NameTableKindNone
        , LLCompunit.debugBaseAddress = False
        }
    fileDef =
        let (dir, file) = splitFileName moduleFilePath
        in
            LLOp.File
                { LLSubprog.filename = fromString file
                , LLSubprog.directory = fromString dir
                , LLSubprog.checksum = Nothing
                }

-- | A data-type is a tagged union, and we represent it in LLVM as a struct
--   where, if there are more than 1 variant, the first element is the
--   variant-index. The variant index is represented as an integer with the
--   smallest width 2^n that can fit all variants. The rest of the elements are
--   the field-types of the largest variant wrt allocation size.
--
--   If none of the variants of the data-type has any members, we say it's an
--   enumeration, which is represented as a single integer, equal to the size it
--   would have been as a tag. If further there's only a single variant, the
--   data-type is represented as `{}`.
defineDataTypes :: TypeDefs -> Gen' (Map Name Word32, Map Name [Type])
defineDataTypes tds = do
    let (enums, datas) = partition (all null . snd) tds
    let enums' = Map.fromList $ map
            (\(tc, vs) ->
                ( mkName (mangleTConst tc)
                , fromMaybe 0 (tagBitWidth (fromIntegral (length vs)))
                )
            )
            enums
    datas'' <- mfix $ \datas' ->
        fmap Map.fromList
            $ augment enumTypes enums'
            $ augment dataTypes datas'
            $ forM datas
            $ \(tc, vs) -> do
                let n = mkName (mangleTConst tc)
                let totVariants = fromIntegral (length vs)
                ts <- mapM (genVariantType totVariants) vs
                sizedTs <- mapM (\t -> sizeof (typeStruct t) <&> (, t)) ts
                if null sizedTs
                    then ice ("defineDataTypes: sizedTs empty for " ++ show n)
                    else pure (n, snd (maximum sizedTs))
    pure (enums', datas'')

genMain :: Gen' Definition
genMain = do
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    Out basicBlocks _ _ _ <- execWriterT $ do
        emitDo' (callExtern "install_stackoverflow_handler" [])
        f <- lookupVar (TypedVar "main" mainType)
        _ <- app f (VLocal litUnit)
        commitFinalFuncBlock (ret (litI32 0))
    pure (GlobalDefinition (simpleFunc (mkName "main") [] i32 basicBlocks []))

-- TODO: Change global defs to a new type that can be generated by llvm. As it
--       is now, global non-function variables can't be straight-forwardly
--       generated in general. Either, initialization is delayed until program
--       start, or an interpretation step is added between monomorphization and
--       codegen that evaluates all expressions in relevant contexts, like
--       constexprs.
genGlobDef
    :: (TypedVar, WithPos ([Monomorphic.Type], Expr)) -> Gen' [Definition]
genGlobDef (TypedVar v _, WithPos dpos (ts, (Expr _ e))) = case e of
    Fun p (body, _) -> do
        let var = (v, ts)
        let name = mangleName var
        assign lambdaParentFunc (Just name)
        assign outerLambdaN 1
        let fName = mkName (name ++ "_func")
        (f, gs) <- genFunDef (fName, [], dpos, p, genExpr body)
        let fRef = LLConst.GlobalReference (LLType.ptr (typeOf f)) fName
        let capturesType = LLType.ptr typeUnit
        let captures = LLConst.Null capturesType
        let closure = litStruct [captures, fRef]
        let closureDef = simpleGlobVar (mkName name) (typeOf closure) closure
        pure (GlobalDefinition closureDef : GlobalDefinition f : gs)
    _ -> nyi $ "Global non-function defs: " ++ show e

genExpr :: Expr -> Gen Val
genExpr (Expr pos expr) = locally srcPos (pos <|>) $ do
    parent <- use lambdaParentFunc <* assign lambdaParentFunc Nothing
    case expr of
        Lit c -> genConst c
        Var (TypedVar x t) -> lookupVar (TypedVar x t)
        App f e _ -> genApp f e
        If p c a -> genIf p c a
        Fun p b -> assign lambdaParentFunc parent *> genExprLambda p b
        Let ds b -> genLet ds b
        Match e cs tbody -> genMatch e cs =<< genType tbody
        Ction c -> genCtion c
        Box e -> genBox =<< genExpr e
        Deref e -> genDeref e
        Absurd t -> fmap (VLocal . undef) (genType t)

genExprLambda :: TypedVar -> (Expr, Monomorphic.Type) -> Gen Val
genExprLambda p (b, bt) = do
    let fvXs = Set.toList (Set.delete p (freeVars b))
    bt' <- genType bt
    genLambda fvXs p (genExpr b, bt')

genConst :: Monomorphic.Const -> Gen Val
genConst = \case
    Int n -> pure (VLocal (litI64 n))
    F64 x -> pure (VLocal (litF64 x))
    Str s -> genStrLit s

genStrLit :: String -> Gen Val
genStrLit s = do
    var <- newName "strlit"
    scribe outStrings [(var, s)]
    pure $ VVar $ ConstantOperand
        (LLConst.GlobalReference (LLType.ptr typeStr) var)

-- | Beta-reduction and closure application
genApp :: Expr -> Expr -> Gen Val
genApp fe' ae' = genApp' (fe', [ae'])
  where
    -- TODO: Could/should the beta-reduction maybe happen in an earlier stage,
    --       like when desugaring?
    genApp' = \case
        (Expr _ (Fun p (b, _)), ae : aes) -> do
            a <- genExpr ae
            withVal p a (genApp' (b, aes))
        (Expr _ (App fe ae _), aes) -> genApp' (fe, ae : aes)
        (fe, []) -> genExpr fe
        (fe, aes) -> do
            closure <- genExpr fe
            as <- mapM genExpr aes
            foldlM (\f a -> app f a) closure as

app :: Val -> Val -> Gen Val
app closure a = do
    closure' <- getLocal closure
    captures <- emitReg "captures" =<< extractvalue closure' [0]
    f <- emitReg "function" =<< extractvalue closure' [1]
    a' <- getLocal a
    let args = [(captures, []), (a', [])]
    fmap VLocal (emitAnonReg (call f args))
  where
    call f as =
        WithRetType (callVoid f as) (getFunRet (getPointee (typeOf f)))

genIf :: Expr -> Expr -> Expr -> Gen Val
genIf pred' conseq alt = do
    predV <- genExpr pred'
    genCondBr predV (genExpr conseq) (genExpr alt)

genCondBr :: Val -> Gen Val -> Gen Val -> Gen Val
genCondBr predV genConseq genAlt = do
    predV' <- emitAnonReg . flip trunc i1 =<< getLocal predV
    conseqL <- newName "consequent"
    altL <- newName "alternative"
    nextL <- newName "next"
    commitToNewBlock (condbr predV' conseqL altL) conseqL
    conseqV <- getLocal =<< genConseq
    fromConseqL <- use currentBlockLabel
    commitToNewBlock (br nextL) altL
    altV <- getLocal =<< genAlt
    fromAltL <- use currentBlockLabel
    commitToNewBlock (br nextL) nextL
    fmap VLocal (emitAnonReg (phi [(conseqV, fromConseqL), (altV, fromAltL)]))

genLet :: Defs -> Expr -> Gen Val
genLet (Topo ds) letBody = do
    (binds, cs) <- fmap unzip $ forM ds $ \case
        (v, WithPos _ (_, Expr _ (Fun p (fb, fbt)))) -> do
            let fvXs = Set.toList (Set.delete p (freeVars fb))
            tcaptures <- fmap
                typeStruct
                (mapM (\(TypedVar _ t) -> genType t) fvXs)
            captures <- genHeapAllocGeneric tcaptures
            fbt' <- genType fbt
            l <- genLambda' p (genExpr fb, fbt') (VLocal captures) fvXs
            pure ((v, l), Just (captures, fvXs))
        (v, WithPos _ (_, e)) -> genExpr e <&> \e' -> ((v, e'), Nothing)
    withVals binds $ do
        forM_ (catMaybes cs) (uncurry populateCaptures)
        genExpr letBody

genMatch :: Expr -> DecisionTree -> Type -> Gen Val
genMatch m dt tbody = do
    -- TODO: Do we have to convert it to an operand here already? Keeping it as
    --       Val would probably eliminate a needless stack allocation.
    m' <- getLocal =<< genExpr m
    genDecisionTree tbody dt (newSelections m')

genDecisionTree :: Type -> DecisionTree -> Selections Operand -> Gen Val
genDecisionTree tbody = \case
    Monomorphic.DLeaf l -> genDecisionLeaf l
    Monomorphic.DSwitch selector cs def ->
        genDecisionSwitchIx selector cs def tbody
    Monomorphic.DSwitchStr selector cs def ->
        genDecisionSwitchStr selector cs def tbody

genDecisionSwitchIx
    :: Monomorphic.Access
    -> Map VariantIx DecisionTree
    -> DecisionTree
    -> Type
    -> Selections Operand
    -> Gen Val
genDecisionSwitchIx selector cs def tbody selections = do
    let (variantIxs, variantDts) = unzip (Map.toAscList cs)
    variantLs <- mapM (newName . (++ "_") . ("variant_" ++) . show) variantIxs
    defaultL <- newName "default"
    nextL <- newName "next"
    (m, selections') <- select selAs selSub selDeref selector selections
    mVariantIx <- case typeOf m of
        IntegerType _ -> pure m
        _ -> emitReg "found_variant_ix" =<< extractvalue m [0]
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
    fmap VLocal (emitAnonReg (phi (v : vs)))

genDecisionSwitchStr
    :: Monomorphic.Access
    -> Map String DecisionTree
    -> DecisionTree
    -> Type
    -> Selections Operand
    -> Gen Val
genDecisionSwitchStr selector cs def tbody selections = do
    (matchee, selections') <- select selAs selSub selDeref selector selections
    let cs' = Map.toAscList cs
    let genCase :: (String, DecisionTree) -> Gen Val -> Gen (Gen Val)
        genCase (s, dt) next = do
            s' <- genStrLit s
            isMatch <- genStrEq (VLocal matchee) s'
            -- Do some wrapping to preserve effect/Gen order
            pure (genCondBr isMatch (genDT dt) next)
        genDT dt = genDecisionTree tbody dt selections'
    f <- foldrM genCase (genDT def) cs'
    f

genDecisionLeaf
    :: (Monomorphic.VarBindings, Expr) -> Selections Operand -> Gen Val
genDecisionLeaf (bs, e) selections = do
    bs' <- selectVarBindings selAs selSub selDeref selections bs
    withLocals bs' (genExpr e)

selAs :: Span -> [Monomorphic.Type] -> Operand -> Gen Operand
selAs totVariants ts matchee = do
    tvariant <- fmap typeStruct (lift (genVariantType totVariants ts))
    let tgeneric = typeOf matchee
    pGeneric <- emitReg "ction_ptr_nominal" (alloca tgeneric)
    emitDo (store matchee pGeneric)
    p <- emitReg "ction_ptr_structural" (bitcast pGeneric (LLType.ptr tvariant))
    emitReg "ction" (load p)

selSub :: Span -> Word32 -> Operand -> Gen Operand
selSub span' i matchee =
    let tagOffset = if span' > 1 then 1 else 0
    in emitReg "submatchee" =<< extractvalue matchee (pure (tagOffset + i))

selDeref :: Operand -> Gen Operand
selDeref x = emitAnonReg (load x)

genCtion :: Monomorphic.Ction -> Gen Val
genCtion (i, span', dataType, as) = do
    lookupEnum dataType & lift >>= \case
        Just 0 -> pure (VLocal litUnit)
        Just w -> pure (VLocal (ConstantOperand (LLConst.Int w i)))
        Nothing -> do
            as' <- mapM genExpr as
            let tag = maybe
                    id
                    ((:) . VLocal . ConstantOperand . flip LLConst.Int i)
                    (tagBitWidth span')
            s <- getLocal =<< genStruct (tag as')
            let t = typeOf s
            let tgeneric = genDatatypeRef dataType
            pGeneric <- emitReg "ction_ptr_nominal" (alloca tgeneric)
            p <- emitReg
                "ction_ptr_structural"
                (bitcast pGeneric (LLType.ptr t))
            emitDo (store s p)
            pure (VVar pGeneric)

genBox :: Val -> Gen Val
genBox = fmap fst . genBox'

genBox' :: Val -> Gen (Val, Val)
genBox' x = do
    let t = typeOf x
    ptrGeneric <- genHeapAllocGeneric t
    ptr <- emitAnonReg (bitcast ptrGeneric (LLType.ptr t))
    x' <- getLocal x
    emitDo (store x' ptr)
    pure (VLocal ptr, VLocal ptrGeneric)

genDeref :: Expr -> Gen Val
genDeref e = genExpr e >>= \case
    VVar x -> fmap VVar (selDeref x)
    VLocal x -> pure (VVar x)

genStrEq :: Val -> Val -> Gen Val
genStrEq s1 s2 = do
    s1' <- getLocal s1
    s2' <- getLocal s2
    b <- emitAnonReg (callExtern "carth_str_eq" [s1', s2'])
    pure (VLocal b)
