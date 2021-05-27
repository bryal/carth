{-# LANGUAGE DuplicateRecordFields, GADTs, RankNTypes #-}

-- | Generation of LLVM IR code from our monomorphic AST.
module Back.Codegen (codegen) where

import LLVM.Prelude
import LLVM.AST hiding (args)
import LLVM.AST.Typed
import LLVM.AST.Type hiding (ptr)
import LLVM.AST.DataLayout
import qualified LLVM.AST.Type as LLType
import qualified LLVM.AST.Constant as LLConst
import Data.String
import System.FilePath
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.List
import Data.Function
import Data.Maybe
import Lens.Micro.Platform (use, assign, view)

import Misc
import FreeVars
import Sizeof (toBytes, tagBitWidth)
import qualified Back.Low as Ast
import Back.Low hiding (Type, Const)
import Front.TypeAst
import Back.Selections
import Back.Gen
import Back.Extern

instance Select Gen Val where
    selectAs span ts matchee = if span == 1
        then pure matchee
        else do
            p <- getVar matchee
            tvariant <- fmap typeStruct (mapM genType ts)
            fmap VVar $ selectVarAs p tvariant
    selectSub _span i matchee = genIndexStruct matchee [i]
    selectDeref = genDeref

codegen :: DataLayout -> ShortByteString -> FilePath -> Program -> Module
codegen layout triple moduleFilePath (Program (Topo defs) tdefs externs) =
    let (tdefs', externs', globDefs) =
            let (enums, tdefs'') = runGen' (defineDataTypes tdefs)
                defs' = defToVarDefs =<< defs
                (funDefs, varDefs) = separateFunDefs defs'
            in  runGen'
                    $ augment enumTypes enums
                    $ augment dataTypes tdefs''
                    $ withBuiltins
                    $ withExternSigs externs
                    $ withGlobFunSigs funDefs
                    $ withGlobVarSigs varDefs
                    $ do
                          es <- genExterns externs
                          funDefs' <- mapM genGlobFunDef funDefs
                          varDecls <- mapM genGlobVarDecl varDefs
                          init_ <- genInit varDefs
                          main <- genMain
                          let ds = main : init_ ++ join funDefs' ++ varDecls
                          pure (tdefs'', es, ds)
    in  Module
            { moduleName = fromString (takeBaseName moduleFilePath)
            , moduleSourceFileName = fromString moduleFilePath
            , moduleDataLayout = Just layout
            , moduleTargetTriple = Just triple
            , moduleDefinitions = concat
                                      [ map
                                          (\(n, tmax) ->
                                              TypeDefinition n (Just (typeStruct tmax))
                                          )
                                          (Map.toList tdefs')
                                      , defineBuiltinsHidden
                                      , externs'
                                      , globDefs
                                      ]
            }
  where
    withGlobFunSigs sigs ga = do
        sigs' <- forM sigs $ \(v@(TypedVar x t), (us, _)) -> do
            t' <- genType t
            tf <- getIndexed t' [1 :: Int]
            pure (v, (tf, mkName (mangleName (x, us) ++ "_func")))
        augment globalFunEnv (Map.fromList sigs') ga

    withGlobVarSigs sigs ga = do
        sigs' <- forM sigs $ \(v@(TypedVar x t), (us, _)) -> do
            t' <- genType t
            pure (v, (LLType.ptr t', mkName (mangleName (x, us))))
        augment globalEnv (Map.fromList sigs') ga

-- | A data-type is a tagged union, and we represent it in LLVM as a representing struct
--   of a tagged union, an untagged struct, an integer, or a zero-sized empty array,
--   depending on how many variants and members it has.
--
--   If there's only one variant, the struct just contains the members of that variant. If
--   there's more than one variant, the representing type consists of 2 members: an
--   integer that can fit the variant index as well as "fill" the succeeding space
--   (implied by alignment) until the second member starts, followed by the second member
--   which is an array of integers with integer size equal to the alignment of the
--   greatest aligned variant and array length equal to the smallest n that results in the
--   array being of size >= the size of the largest sized variant.
--
--   If none of the variants of the data-type has any members, we say it's an
--   enumeration, which is represented as a single integer, equal to the size it
--   would have been as a tag. If further there's only a single variant, the
--   data-type is represented as `{}`.
--
--   The reason we must make sure to "fill" all space in the representing struct is that
--   LLVM may essentially otherwise incorrectly assume that the space is unused and
--   doesn't have to be considered passing the type as an argument to a function.
--
--   The reason we fill it with values the size of the alignment instead of bytes is to
--   not wrongfully signal to LLVM that the padding will be used as-is, and should be
--   passed/returned in its own registers (or whatever exactly is going on). I just know
--   from trial and error when debugging issues with how the representation of `(Maybe
--   Int8)` affects how it is returned from a function. The intuitive definition (which
--   indeed could be used for `Maybe` specifically without problems, since the only other
--   variant is the non-data-carrying `None`) is `{i8, i64}`. Representing it instead with
--   `{i64, i64}` (to make alignment-induced padding explicit, also this is how Rust
--   represents it) works well -- it seems to be passed/returned in exactly the same
--   way. However, if we represent it as `{i8, [7 x i8], i64}` or `{i8, [15 x i8], [0 x
--   i64]}`: while having the same size and alignment, it is not returned in the same way
--   (seeming instead to use an additional return parameter), and as such, a Carth
--   function returning `(Maybe Int8)` represented as `{i8, [15 x i8], [0 x i64]}` is not
--   ABI compatible with a Rust function returning `Maybe<i8>` represented as `{i64,
--   i64}`.
defineDataTypes :: Datas -> Gen' (Map Name Word32, Map Name [Type])
defineDataTypes datasEnums = do
    let (enums, datas) = partition (all null . snd) (Map.toList datasEnums)
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
            $ \(tc, vs) ->
                  let
                      n = mkName (mangleTConst tc)
                      totVariants = fromIntegral (length vs)
                  in
                      fmap (n, ) $ if totVariants == 1
                          then mapM genType (head vs)
                          else do
                              ts <- mapM (fmap typeStruct . mapM genType) vs
                              aMax <- fmap maximum $ mapM alignmentof ts
                              sMax <- fmap maximum $ mapM sizeof ts
                              let sTag = max
                                      (toBytes (fromJust (tagBitWidth totVariants)))
                                      aMax
                              let tag = IntegerType (fromIntegral sTag * 8)
                              pure
                                  [ tag
                                  , ArrayType (div (sMax + aMax - 1) aMax)
                                              (IntegerType (8 * fromIntegral aMax))
                                  ]
    pure (enums', datas'')

genMain :: Gen' Definition
genMain = do
    let tDummyParam = typeUnit
    let init_ = ConstantOperand $ LLConst.GlobalReference
            (LLType.ptr (FunctionType LLType.void [typeGenericPtr, tDummyParam] False))
            (mkName "carth_init")
    assign currentBlockLabel (mkName "entry")
    assign currentBlockInstrs []
    Out basicBlocks _ _ <- execWriterT $ do
        emitDo' =<< callBuiltin "install_stackoverflow_handler" []
        emitDo (callIntern Nothing init_ [(null' typeGenericPtr, []), (litUnit, [])])
        iof <- lookupVar (TypedVar "main" mainType)
        f <- genIndexStruct iof [0]
        _ <- app' @Val f (VLocal litRealWorld)
        commitFinalFuncBlock (ret (litI32 0))
    pure (GlobalDefinition (externFunc (mkName "main") [] i32 basicBlocks))

separateFunDefs :: [VarDef] -> ([FunDef], [VarDef])
separateFunDefs = partitionWith $ \(lhs, (ts, e)) -> case e of
    Fun f -> Left (lhs, (ts, f))
    _ -> Right (lhs, (ts, e))

genInit :: [VarDef] -> Gen' [Definition]
genInit ds = do
    let name = mkName "carth_init"
    let param = TypedVar "_" tUnit
    let genDefs =
            forM_ ds genDefineGlobVar *> commitFinalFuncBlock retVoid $> LLType.void
    fmap (uncurry ((:) . GlobalDefinition)) $ genFunDef (name, [], param, genDefs)

genDefineGlobVar :: VarDef -> Gen ()
genDefineGlobVar (TypedVar v _, (ts, e)) = do
    let name = mkName (mangleName (v, ts))
    e' <- genExpr e
    let ref = LLConst.GlobalReference (LLType.ptr (typeOf e')) name
    -- Fix for Boehm GC to detect global vars when running in JIT
    genGcAddRoot ref
    genStore e' (VLocal (ConstantOperand ref)) $> ()

genGlobVarDecl :: VarDef -> Gen' Definition
genGlobVarDecl (TypedVar v t, (ts, _)) = do
    let name = mkName (mangleName (v, ts))
    t' <- genType t
    pure (GlobalDefinition (simpleGlobVar name t' (LLConst.Undef t')))

-- TODO: Detect when a fun def is nested lambdas, like (define (foo a b) (+ a b)). Now,
--       nested functions wrappers are generated for the currying that handle boilerplate
--       closure capturing, but only the outermost, fully curried function is actually
--       exposed as a variable, and if you apply the function with all arguments, like
--       (foo 1 2), it has to needlessly go through all the wrapping stuff of putting in
--       closures and directly extracting again.
--
--       It would be a serious optimization to handle saturated (i.e., fully applied)
--       calls specially. Just generate an extra, innermost function that takes the params
--       as a tuple, and does no closure-extraction stuff, then generate the currying
--       wrappers around that.
--
--       Look at how Haskell does
--       it. https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/haskell-execution/function-calls. Seems
--       very reasonable. They handle 4 different cases when compiling a call: Unknown
--       function, Known function - saturated call, Known function - too few arguments,
--       and Known function - too many arguments.
--
--       Additional reading: http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.134.9317&rep=rep1&type=pdf
genGlobFunDef :: FunDef -> Gen' [Definition]
genGlobFunDef (TypedVar v _, (ts, (p, (body, rt)))) = do
    let name = mangleName (v, ts)
    assign lambdaParentFunc (Just name)
    let fName = mkName (name ++ "_func")
    (f, gs) <- genFunDef (fName, [], p, genTailExpr body *> genType rt)
    pure (GlobalDefinition f : gs)

genTailExpr :: Expr -> Gen ()
genTailExpr = genExpr

genExpr :: TailVal v => Expr -> Gen v
genExpr expr = do
    case expr of
        Lit c -> propagate =<< genConst c
        Var (_, x) -> propagate =<< lookupVar x
        App f as -> genApp f as
        If p c a -> genExpr p >>= \p' -> genCondBr p' (genExpr c) (genExpr a)
        Fun (p, b) -> genExprLambda p b >>= propagate
        Let d b -> genLet d b
        Match e cs -> genMatch e cs
        Ction c -> propagate =<< genCtion c
        Sizeof t ->
            propagate
                =<< (VLocal . litI64 . fromIntegral)
                <$> ((lift . sizeof) =<< genType t)
        Absurd t -> propagate =<< fmap (VLocal . undef) (genType t)

genExprLambda :: TypedVar -> (Expr, Ast.Type) -> Gen Val
genExprLambda p (b, bt) = do
    fvXs <- view localEnv <&> \locals ->
        Set.toList (Set.intersection (Set.delete p (freeVars b)) (Map.keysSet locals))
    bt' <- genType bt
    genLambda fvXs p (genTailExpr b, bt')

genConst :: Ast.Const -> Gen Val
genConst = \case
    Int n -> pure (VLocal (litI64 n))
    F64 x -> pure (VLocal (litF64 x))
    Str s -> genStrLit s

genStrLit :: String -> Gen Val
genStrLit s = do
    var <- newName "strlit"
    scribe outStrings [(var, s)]
    pure $ VVar $ ConstantOperand (LLConst.GlobalReference (LLType.ptr typeStr) var)

class TailVal v where
    propagate :: Val -> Gen v
    app' :: Val -> Val -> Gen v
    converge :: Gen v -> [(Name, Gen v)] -> Gen v

instance TailVal Val where
    propagate = pure
    app' = app (Just NoTail)
    converge default' cs = do
        nextL <- newName "next"
        v <- liftA2 (,) (getLocal =<< default') (use currentBlockLabel)
        let genCase (l, mv) = do
                commitToNewBlock (br nextL) l
                liftA2 (,) (getLocal =<< mv) (use currentBlockLabel)
        vs <- mapM genCase cs
        commitToNewBlock (br nextL) nextL
        fmap VLocal (emitAnonReg (phi (v : vs)))

instance TailVal () where
    propagate v = commitFinalFuncBlock . ret =<< getLocal v
    app' f e = propagate =<< app (Just Tail) f e
    converge default' cs = do
        () <- default'
        forM_ cs $ \(l, gen) -> assign currentBlockLabel l *> gen

genApp :: TailVal v => Expr -> [Expr] -> Gen v
genApp fe aes = case fe of
    Var (Virt, x) -> propagate =<< genAppBuiltinVirtual x =<< mapM genExpr aes
    _ -> do
        f <- genExpr fe
        as <- mapM genExpr (init aes)
        closure <- foldlM app' f as
        arg <- genExpr (last aes)
        app' closure arg

genCondBr :: TailVal v => Val -> Gen v -> Gen v -> Gen v
genCondBr predV genConseq genAlt = do
    predV' <- emitAnonReg . flip trunc i1 =<< getLocal predV
    conseqL <- newName "consequent"
    altL <- newName "alternative"
    commitToNewBlock (condbr predV' conseqL altL) conseqL
    converge genConseq [(altL, genAlt)]

genLet :: TailVal v => Def -> Expr -> Gen v
genLet def body = case def of
    VarDef (lhs, (_, rhs)) -> genExpr rhs >>= \rhs' -> withVal lhs rhs' (genExpr body)
    RecDefs ds -> do
        (binds, cs) <- fmap unzip $ forM ds $ \case
            (lhs, (_, (p, (fb, fbt)))) -> do
                fvXs <- view localEnv <&> \locals ->
                    let locals' = Set.insert lhs (Map.keysSet locals)
                    in  Set.toList (Set.intersection (Set.delete p (freeVars fb)) locals')
                tcaptures <- fmap typeStruct (mapM (\(TypedVar _ t) -> genType t) fvXs)
                captures <- genHeapAllocGeneric tcaptures
                fbt' <- genType fbt
                lam <- genLambda' p (genTailExpr fb, fbt') (VLocal captures) fvXs
                pure ((lhs, lam), (captures, fvXs))
        withVals binds $ do
            forM_ cs (uncurry populateCaptures)
            (genExpr body)

genMatch :: TailVal v => Expr -> DecisionTree -> Gen v
genMatch m dt = genDecisionTree dt . newSelections =<< genExpr m

genDecisionTree :: TailVal v => DecisionTree -> Selections Val -> Gen v
genDecisionTree = \case
    Ast.DLeaf l -> genDecisionLeaf l
    Ast.DSwitch span selector cs def -> genDecisionSwitchIx span selector cs def
    Ast.DSwitchStr selector cs def -> genDecisionSwitchStr selector cs def
  where
    genDecisionLeaf (bs, e) selections = do
        bs' <- selectVarBindings selections bs
        withVals bs' (genExpr e)
    genDecisionSwitchIx span selector cs def selections = do
        let (variantIxs, variantDts) = unzip (Map.toAscList cs)
        (m, selections') <- select selector selections
        mVariantIx <- case typeOf m of
            IntegerType _ -> getLocal m
            -- We can't read the index from the representative struct directly. We first
            -- have to "remove the padding" on the index by truncating it to the smallest
            -- size that can fit all variants. We have to do this because the padding
            -- bytes may be nonzero.
            _ -> do
                tagBig <- getLocal =<< genIndexStruct m [0]
                let tSmall = IntegerType (fromJust (tagBitWidth span))
                if typeOf tagBig == tSmall
                    then pure tagBig
                    else emitAnonReg $ trunc tagBig tSmall
        let ixBits = getIntBitWidth (typeOf mVariantIx)
        let litIxInt = LLConst.Int ixBits
        variantLs <- mapM (newName . (++ "_") . ("variant_" ++) . show) variantIxs
        defaultL <- newName "default"
        let dests' = zip (map litIxInt variantIxs) variantLs
        commitToNewBlock (switch mVariantIx defaultL dests') defaultL
        converge (genDecisionTree def selections')
                 (zip variantLs (map (flip genDecisionTree selections') variantDts))
    genDecisionSwitchStr selector cs def selections = do
        (matchee, selections') <- select selector selections
        let cs' = Map.toAscList cs
        let genCase (s, dt) next = do
                s' <- genStrLit s
                isMatch <- genStrEq matchee s'
                -- Do some wrapping to preserve effect order
                pure $ genCondBr isMatch (genDecisionTree dt selections') next
        join (foldrM genCase (genDecisionTree def selections') cs')

genCtion :: Ast.Ction -> Gen Val
genCtion (i, span', dataType, as) = do
    lookupEnum dataType & lift >>= \case
        Just 0 -> pure (VLocal litUnit)
        Just w -> pure (VLocal (ConstantOperand (LLConst.Int w i)))
        Nothing -> do
            as' <- mapM genExpr as -- can have side effects, so generate even if zero size
            let tnominal = genDatatypeRef dataType
            pnominal <- emitReg "nominal" (alloca tnominal)
            -- If span is 1, there is no tag & no need to bitcast etc
            p <- if span' == 1
                then pure pnominal
                else do
                    ptag <- emitReg "tag" =<< getelementptr pnominal (litI64 0) [0]
                    let w = getIntBitWidth (getPointee (typeOf ptag))
                    let tag = ConstantOperand (LLConst.Int w i)
                    _ <- genStore (VLocal tag) (VLocal ptag)
                    selectVarAs pnominal (typeStruct (map typeOf as'))
            genStructInPtr p as'
            pure (VVar pnominal)

genStrEq :: Val -> Val -> Gen Val
genStrEq s1 s2 =
    fmap VLocal . emitAnonReg =<< callBuiltin "carth_str_eq" =<< mapM getLocal [s1, s2]

selectVarAs :: Operand -> Type -> Gen Operand
selectVarAs pRepresentative tvariant = do
    pGeneric <- emitReg "generic" =<< getelementptr pRepresentative (litI64 0) [1]
    emitReg "structural" (bitcast pGeneric (LLType.ptr tvariant))
