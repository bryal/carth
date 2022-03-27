{-# LANGUAGE TemplateHaskell, DataKinds #-}

module Back.Lower (lower) where

import Control.Arrow
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor (bimap)
import Data.Function
import Data.Functor
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Word
import Lens.Micro.Platform (makeLenses, modifying, use)

import Back.Low (typeof)
import qualified Back.Low as Low
import Front.Monomorphic
import Misc
import Sizeof

data Sized x = ZeroSized | Sized x

mapSized :: (a -> b) -> Sized a -> Sized b
mapSized f (Sized a) = Sized (f a)
mapSized _ ZeroSized = ZeroSized

newtype St = St
    { _strLits :: Map String Low.GlobalId
    }
makeLenses ''St

type Out = ([Low.FunDef], [Low.GlobDef])

type Lower = WriterT Out (State St)

type EBlock = Low.Block (Sized (Either Low.Expr Low.Operand, Low.Type))

lower :: Program -> Low.Program
lower (Program (Topo defs) datas externs) =
    let _externNames = map fst externs
        (fs, gs) = run $ do
            fs' <- mapM lowerFunDef funDefs
            init <- defineInit
            tell (fs' ++ [init], [])
    in  Low.Program fs externs' (map lowerGVarDecl gvarDefs ++ gs) tenv undefined -- (resolveNameConflicts globNames externNames)
  where
    builtinNames = ["carth_init"] :: [String]
    initNameIx = fromIntegral (fromJust (elemIndex "carth_init" builtinNames))

    -- resolveNameConflicts :: [String] -> [String] -> Vector String
    -- resolveNameConflicts = _

    externs' = flip map externs $ \case
        (name, TFun pts rt) ->
            Low.ExternDecl name (toParam () . lowerType =<< pts) (toRet (lowerType rt))
        (name, t) -> nyi $ "lower: Non-function externs: " ++ name ++ ", " ++ show t

    run :: Lower () -> ([Low.FunDef], [Low.GlobDef])
    run = undefined

    defineInit :: Lower Low.FunDef
    defineInit = pure $ Low.FunDef initNameIx
                                   []
                                   Low.RetVoid
                                   (Low.Block undefined undefined)
                                   undefined
                                   undefined
    -- do
        -- let name = mkName "carth_init"
        -- let param = TypedVar "_" tUnit
        -- let genDefs =
        --         forM_ ds genDefineGlobVar *> commitFinalFuncBlock retVoid $> LLType.void
        -- fmap (uncurry ((:) . GlobalDefinition)) $ genFunDef (name, [], param, genDefs)

    lowerFunDef :: (TypedVar, (Inst, Fun)) -> Lower Low.FunDef
    lowerFunDef (lhs, (_inst, (ps, (body, rt)))) = do
        let Low.Global name _ = globFunEnv Map.! lhs
        -- Zero-sized parameters don't actually get to exist in the Low IR and beyond
        (binds, pIds, pts) <- fmap (unzip3 . catMaybes) $ forM ps $ \p -> do
            case lowerType (tvType p) of
                ZeroSized -> pure Nothing
                Sized pt -> do
                    pid <- newLName (tvName p)
                    let bind = (p, Low.OLocal (Low.Local pid pt))
                    pure (Just (bind, pid, pt))
        capturesName <- newLName "captures"
        body <- withVars binds (lowerBody body)
        localNames <- popLocalNames
        allocs <- popAllocs
        pure $ Low.FunDef
            name
            (Low.ByVal capturesName Low.VoidPtr : zipWith sizedToParam pIds pts)
            (toRet (lowerType rt))
            body
            allocs
            localNames

    popLocalNames :: Lower Low.VarNames
    popLocalNames = undefined

    popAllocs :: Lower Low.Allocs
    popAllocs = undefined

    lowerBody :: Expr -> Lower (Low.Block Low.Terminator)
    lowerBody body = do
        Low.Block stms e <- lowerExpr body
        case e of
            ZeroSized -> pure $ Low.Block stms Low.TRetVoid
            Sized (e', t) -> do
                if passByRef t
                    then undefined
                    else do
                        ret <- fmap (flip Low.Local t) (newLName "ret")
                        pure $ case e' of
                            Left i -> Low.Block (stms ++ [Low.Let ret i])
                                                (Low.TRetVal (Low.OLocal ret))
                            Right o -> Low.Block stms (Low.TRetVal o)

    lowerExpr :: Expr -> Lower EBlock
    lowerExpr = \case
        Lit c -> lowerConst c <&> \c' -> Low.Block [] (Sized (Right c', typeof c'))
        Var x -> Low.Block [] . mapSized (Right &&& typeof) <$> lookupVar x
        -- App Expr [Expr]
        -- If Expr Expr Expr
        -- Fun Fun
        -- Let Def Expr
        Match es dt -> lowerMatch es dt
        -- Ction Ction
        -- Sizeof Type
        -- Absurd Type
        _ -> undefined

    lookupVar :: TypedVar -> Lower (Sized Low.Operand)
    lookupVar = undefined

    lowerConst :: Const -> Lower Low.Operand
    lowerConst = \case
        Int n -> pure (Low.OConst (Low.CInt (Low.I64 n)))
        F64 x -> pure (Low.OConst (Low.F64 x))
        Str s -> internStr s <&> \s' -> Low.OGlobal s'

    internStr :: String -> Lower Low.Global
    internStr s = use strLits >>= \m ->
        fmap (flip Low.Global tStr) $ case Map.lookup s m of
            Just n -> pure n
            Nothing ->
                let n = fromIntegral (Map.size m)
                in  modifying strLits (Map.insert s n) $> n

    tStr = Low.TConst (tids Map.! ("Str", []))

    lowerMatch :: [Expr] -> DecisionTree -> Lower EBlock
    lowerMatch ms dt = do
        Low.Block msStms ms' <- eblocksToOperandsBlock =<< mapM lowerExpr ms
        Low.Block dtStms result <- lowerDecisionTree dt (topSelections ms')
        pure (Low.Block (msStms ++ dtStms) result)
      where
        topSelections :: [Sized Low.Operand] -> Map Access Low.Operand
        topSelections xs = Map.fromList . catMaybes $ zipWith
            (\i x -> (TopSel i, ) <$> sizedMaybe x)
            [0 ..]
            xs

        lowerDecisionTree :: DecisionTree -> Map Access Low.Operand -> Lower EBlock
        lowerDecisionTree = undefined

    eblocksToOperandsBlock :: [EBlock] -> Lower (Low.Block [Sized Low.Operand])
    eblocksToOperandsBlock bs = do
        bs' <- forM bs $ \(Low.Block stms e) -> case e of
            ZeroSized -> pure (stms, ZeroSized)
            Sized (Right o, _) -> pure (stms, Sized o)
            Sized (Left e', t) -> do
                name <- newLName "tmp"
                let l = Low.Local name t
                pure (stms ++ [Low.Let l e'], Sized (Low.OLocal l))
        let (stmss, os) = unzip bs'
        pure (Low.Block (concat stmss) os)

    withVars :: [(TypedVar, Low.Operand)] -> Lower a -> Lower a
    withVars = undefined withVar

    withVar :: TypedVar -> Low.Operand -> Lower a -> Lower a
    withVar = undefined

    newLName :: String -> Lower Low.LocalId
    newLName = undefined

    lowerGVarDecl :: (TypedVar, (Inst, Expr)) -> Low.GlobDef
    lowerGVarDecl = undefined

    globFunEnv :: Map TypedVar Low.Global
    globFunEnv = undefined funDefs

    _globVarEnv :: Map TypedVar Low.Global
    _globVarEnv = undefined gvarDefs

    (funDefs, gvarDefs) =
        let defs' = defs >>= \case
                VarDef d -> [d]
                RecDefs ds -> map (second (second Fun)) ds
        in  flip partitionWith defs' $ \(lhs, (ts, e)) -> case e of
                Fun f -> Left (lhs, (ts, f))
                _ -> Right (lhs, (ts, e))

    builtinTypeDefs =
        -- closure: pointer to captures struct & function pointer, genericized
        [ ( "closure"
          , Low.DStruct (Low.Struct [Low.VoidPtr, Low.VoidPtr] (wordsize * 2) wordsize)
          )
        ]

    closureType = builtinType "closure"

    builtinType name = Low.TConst $ fromIntegral $ fromJust $ findIndex
        ((== name) . fst)
        builtinTypeDefs

    -- Iff a TConst is zero sized, it will have no entry in tids
    tenv :: Vector Low.TypeDef
    tids :: Map TConst Word
    (tenv, tids) =
        bimap (Vec.fromList . nameUniquely fst (first . const) . (builtinTypeDefs ++))
              Map.fromList
            . snd
            $ foldl
                  (\(i, (env, ids)) (inst@(name, _), variants) ->
                      (i, (env, ids)) <> case defineData i name variants of
                          Nothing -> (0, ([], []))
                          Just (outer, inners) ->
                              ( 1 + fromIntegral (length inners)
                              , ((name, outer) : inners, [(inst, i)])
                              )
                  )
                  (fromIntegral (length builtinTypeDefs), ([], []))
                  (Map.toList datas)

      where
        defineData typeId0 name variants =
            let
                variantNames = map fst variants
                variantTypess = map (lowerSizedTypes . snd) variants
            in
                case variantTypess of
                    [] -> ice "Lower.defineData: uninhabited type"
                    [[]] -> Nothing
                    [ts] -> Just (structDef ts, [])
                    _ | all null variantTypess ->
                        Just (Low.DEnum (Vec.fromList variantNames), [])
                    _ ->
                        let
                            aMax = maximum $ map alignmentofStruct variantTypess
                            sMax = maximum $ map sizeofStruct variantTypess
                            variants' = Vec.fromList (zip variantNames [typeId0 + 2 ..])
                            sTag = variantsTagBits variants'
                            tag = if
                                | sTag <= 8 -> Low.TI8
                                | sTag <= 16 -> Low.TI16
                                | sTag <= 32 -> Low.TI32
                                | sTag <= 64 -> Low.TI64
                                | otherwise -> ice "Lower.defineData: tag > 64 bits"
                            unionId = typeId0 + 1
                            outerStruct = structDef [tag, Low.TConst unionId]
                            innerUnion =
                                ( name ++ "_union"
                                , Low.DUnion $ Low.Union variants' sMax aMax
                                )
                            variantStructs =
                                zip variantNames (map structDef variantTypess)
                        in
                            Just (outerStruct, innerUnion : variantStructs)
        structDef ts =
            Low.DStruct $ Low.Struct ts (alignmentofStruct ts) (sizeofStruct ts)

    nameUniquely :: (a -> String) -> (String -> a -> a) -> [a] -> [a]
    nameUniquely get set =
        ((reverse . fst) .) $ flip foldl ([], Map.empty) $ \(ds, seen) d ->
            let name = get d
                uq n =
                    let name' = if n == 0 then name else name ++ "_" ++ show (n :: Int)
                    in  if Map.findWithDefault 0 name' seen == 0
                            then (name', Map.insert name (n + 1) seen)
                            else uq (n + 1)
                (name', seen') = uq (Map.findWithDefault 0 name seen)
            in  (set name' d : ds, seen')

    sizedMaybe = \case
        ZeroSized -> Nothing
        Sized t -> Just t

    toParam name = \case
        ZeroSized -> []
        Sized t -> [sizedToParam name t]

    sizedToParam name t = if passByRef t then Low.ByRef name t else Low.ByVal name t

    toRet = \case
        ZeroSized -> Low.RetVoid
        Sized t -> if passByRef t then Low.OutParam t else Low.RetVal t

    lowerSizedTypes :: [Type] -> [Low.Type]
    lowerSizedTypes = mapMaybe (sizedMaybe . lowerType)

    -- TODO: Should respect platform ABI. For example wrt size of TNatSize on 32-bit
    --       vs. 64-bit platform.
    --
    -- | The Low representation of a type in expression-context
    lowerType :: Type -> Sized Low.Type
    lowerType = \case
        TPrim (TNat w) -> genIntT w
        TPrim TNatSize -> genIntT wordsizeBits
        TPrim (TInt w) -> genIntT w
        TPrim TIntSize -> genIntT wordsizeBits
        TPrim TF32 -> Sized Low.TF32
        TPrim TF64 -> Sized Low.TF64
        TFun _ _ -> Sized closureType
        TBox t -> Sized $ case lowerType t of
            ZeroSized -> Low.VoidPtr
            Sized t' -> Low.TPtr t'
        TConst tc -> Map.lookup tc tids & \case
            Nothing -> ZeroSized
            Just ix -> Sized $ Low.TConst ix
      where
        genIntT :: Word32 -> Sized Low.Type
        genIntT w = if
            | w == 0 -> ZeroSized
            | w <= 8 -> Sized Low.TI8
            | w <= 16 -> Sized Low.TI16
            | w <= 32 -> Sized Low.TI32
            | w <= 64 -> Sized Low.TI64
            | otherwise -> ice "Lower.lowerType: integral type larger than 64-bit"

    -- NOTE: This post is helpful:
    --       https://stackoverflow.com/questions/42411819/c-on-x86-64-when-are-structs-classes-passed-and-returned-in-registers
    --       Also, official docs:
    --       https://refspecs.linuxbase.org/elf/x86_64-abi-0.99.pdf
    --       particularly section 3.2.3 Parameter Passing (p18).
    --
    --       From SystemV x86-64 ABI:
    --       "The size of each argument gets rounded up to eightbytes."
    --       "the term eightbyte refers to a 64-bit object"
    --       "If the size of an object is larger than four eightbytes, or it contains
    --        unaligned fields, it has class MEMORY"
    --       "If the size of the aggregate exceeds two eightbytes and the first eight-byte
    --        isn’t SSE or any other eightbyte isn’t SSEUP, the whole argument is passed
    --        in memory.""
    --
    --       Essentially, for Carth, I think it's true that all aggregate types of size >
    --       2*8 bytes are passed in memory, and everything else is passed in register. We
    --       could always state that this is the ABI we use, and that it's the user's
    --       responsibility to manually handle the cases where it may clash with the
    --       correct C ABI. Maybe we'll want to revisit this if/when we add support for
    --       SIMD vector types something similarly exotic.
    passByRef :: Low.Type -> Bool
    passByRef t = sizeof t > 2 * 8

    sizeof = Low.sizeof tenv
    _alignmentof = Low.alignmentof tenv
    sizeofStruct = Low.sizeofStruct tenv
    alignmentofStruct = Low.alignmentofStruct tenv

-- | To generate cleaner code, a data-type is only represented as a tagged union (Data) if
--   it has to be. If there is only a single variant, we skip the tag and represent it as
--   a Struct. If the struct also has no members, we simplify it further and represent it
--   as a Unit. If instead the data-type has multiple variants, but no variant has any
--   members, it is represented as an Enum.
-- lowerDatas :: ()
-- lowerDatas = ()

-- builtinExterns :: Map String Type
-- builtinExterns = _


-- instance TypeAst Type where
--     tprim = TPrim
--     tconst = TConst
--     tfun = TFun
--     tbox = TBox

-- instance FreeVars Expr TypedVar where
--     freeVars e = fvExpr e

-- fvExpr :: Expr -> Set TypedVar
-- fvExpr = \case
--     Lit _ -> Set.empty
--     Var (_, x) -> Set.singleton x
--     App f a -> Set.unions (map freeVars (f : a))
--     If p c a -> fvIf p c a
--     Fun (p, (b, _)) -> fvFun p b
--     Let (VarDef (lhs, (_, rhs))) e ->
--         Set.union (freeVars rhs) (Set.delete lhs (freeVars e))
--     Let (RecDefs ds) e -> fvLet (unzip (map (second (Fun . snd)) ds)) e
--     Match e dt -> Set.union (freeVars e) (fvDecisionTree dt)
--     Ction (_, _, _, as) -> Set.unions (map freeVars as)
--     Sizeof _t -> Set.empty
--     Absurd _ -> Set.empty

-- fvDecisionTree :: DecisionTree -> Set TypedVar
-- fvDecisionTree = \case
--     DLeaf (bs, e) -> Set.difference (freeVars e) (Set.fromList (map fst bs))
--     DSwitch _ _ cs def -> fvDSwitch (Map.elems cs) def
--     DSwitchStr _ cs def -> fvDSwitch (Map.elems cs) def
--     where fvDSwitch es def = Set.unions $ fvDecisionTree def : map fvDecisionTree es
