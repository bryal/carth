{-# LANGUAGE TemplateHaskell, DataKinds, InstanceSigs, ScopedTypeVariables #-}

module Back.Lower (lower) where

import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Bifunctor (bimap)
import Data.Bitraversable
import Data.Foldable
import Data.Function
import Data.Functor
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Word
import Lens.Micro.Platform (makeLenses, modifying, use, assign, view, assign)

import Back.Low (typeof)
import qualified Back.Low as Low
import Front.Monomorphic
import Misc
import Sizeof
import FreeVars

data Sized x = ZeroSized | Sized x

mapSized :: (a -> b) -> Sized a -> Sized b
mapSized f (Sized a) = Sized (f a)
mapSized _ ZeroSized = ZeroSized

mapSizedM :: Monad m => (a -> m b) -> Sized a -> m (Sized b)
mapSizedM f = \case
    Sized a -> fmap Sized (f a)
    ZeroSized -> pure ZeroSized

data St = St
    { _strLits :: Map String Low.GlobalId
    , _localNames :: Vector String
    -- Iff a TConst is zero sized, it will have no entry
    , _tconsts :: Map TConst Low.TypeId
    , _tids :: Seq Low.TypeDef -- ^ Maps type IDs as indices to type defs
    , _tdefs :: Map Low.TypeDef Low.TypeId
    }
makeLenses ''St

-- We need to be able to generate (pseudo) anonymous structs as part of lowering.
-- For example, a named struct needs to be defined for each captures struct of a closure.
-- In LLVM backend, this is not strictly necessary, as we can use anonymous structs. Naming
-- them implies shorter lines and less noise though, so that's still a good idea.
-- In C, anonymous structs are uniqued, and can't be "reused", so we will need to name them for
-- things to even work.

-- Just added (& renamed / modified) tids and tenv to St. This will affect a bunch of code, since
-- existing in the big `where` is no longer enough to access all of the type environment.
-- Things like `sizeof` needs to be in a `Lower` monad now, so yeah. Fixing that and implementing
-- lowerExpr for Fun is what's currently going on.

-- data TailPos = TailRet | TailOutParam Low.LocalId | NoTail

newtype Env = Env
    { _localEnv :: Map TypedVar Low.Operand
    -- , _tailPos :: TailPos
    }
makeLenses ''Env

type Out = ([Low.FunDef], [Low.GlobDef])

type Lower = WriterT Out (StateT St (Reader Env))

-- | A potentially not yet emitted&named operand
-- type PartialOperand = Either Low.Expr Low.Operand
-- type EBlock = Low.Block (Sized PartialOperand)

-- Regarding the stack and registers.
--
-- I'm thinking we could generate Low IR such that all structs & unions are on the stack,
-- which means they would require an Alloc and the type would be behind a TPtr. All
-- primitive types would be in registers. This would simplify Lower. We would for example
-- not need both an ExtractElement and GetElementPointer, like in LLVM. Only a GEP would
-- do, since we keep all structs on the stack.
--
-- We assume then that the next codegen step in the pipe will do register allocation, and
-- optimize such that small structs are kept in register instead of on the stack etc.

class Destination d where
    type DestTerm d
    toDest :: d -> Sized Low.Expr -> Lower (Low.Block (DestTerm d))

newtype There = There Low.Operand
instance Destination There where
    type DestTerm There = ()

    toDest (There a) = \case
        ZeroSized -> ice "Lower.toDest: ZeroSized to There"
        Sized e -> do
            x <- newLName "tmp"
            let x' = Low.Local x (typeof e)
            let x'' = Low.OLocal x'
            pure $ Low.Block [Low.Let x' e, Low.Store x'' a] ()

data Here = Here
instance Destination Here where
    type DestTerm Here = Low.Expr

    toDest Here = \case
        ZeroSized -> ice "Lower.toDest: ZeroSized to Here"
        Sized e -> pure $ Low.Block [] e

data HereSized = HereSized
instance Destination HereSized where
    type DestTerm HereSized = Sized Low.Expr

    toDest HereSized = pure . Low.Block []

data Nowhere = Nowhere
instance Destination Nowhere where
    type DestTerm Nowhere = ()

    toDest Nowhere = \case
        ZeroSized -> pure $ Low.Block [] ()
        Sized _ -> ice "Lower.toDest: Sized to Nowhere"

lower :: Program -> Low.Program
lower (Program (Topo defs) datas externs) =
    let _externNames = map fst externs
        (externs'', fs, gs, tenv) = run $ do
            defineDatas
            externs' <- lowerExterns
            fs' <- mapM lowerFunDef funDefs
            init <- defineInit
            tell (fs' ++ [init], [])
            pure externs'
    in  Low.Program fs externs'' (map lowerGVarDecl gvarDefs ++ gs) tenv undefined -- (resolveNameConflicts globNames externNames)
  where
    builtinNames = ["carth_init"] :: [String]
    initNameIx = fromIntegral (fromJust (elemIndex "carth_init" builtinNames))

    -- resolveNameConflicts :: [String] -> [String] -> Vector String
    -- resolveNameConflicts = _

    lowerExterns = forM externs $ \case
        (name, TFun pts rt) -> liftM2
            (Low.ExternDecl name)
            (catMaybes <$> mapM (toParam () <=< lowerType) pts)
            (undefined (lowerType rt))
        (name, t) -> nyi $ "lower: Non-function externs: " ++ name ++ ", " ++ show t

    run :: Lower a -> (a, [Low.FunDef], [Low.GlobDef], Vector Low.TypeDef)
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
        let self@(Low.Global name _) = globFunEnv Map.! lhs
        -- Zero-sized parameters don't actually get to exist in the Low IR and beyond
        (binds, innerParamIds, directParamTs) <-
            fmap (unzip3 . catMaybes) $ forM ps $ \p -> lowerType (tvType p) >>= \case
                ZeroSized -> pure Nothing
                Sized pt -> do
                    pid <- newLName (tvName p)
                    let bind = (p, Low.OLocal (Low.Local pid pt))
                    pure (Just (bind, pid, pt))
        capturesName <- newLName "captures"
        rt' <- lowerType rt
        paramTs <- mapM
            (\t -> passByRef t <&> \case
                True -> Low.TPtr t
                False -> t
            )
            directParamTs
        let innerParams = zipWith Low.Local innerParamIds paramTs
        -- Lower the body, generate an out-parameter if the return value is to be passed
        -- on the stack, and optimize to loop if the function is tail recursive.
        (outParam, outerParamIds, body'') <- do
            -- These will be discarded if the function is not tail recursive. In that
            -- case, the inner params and the outer params are the same.
            outerParamIds <- mapM spinoffLocalId innerParamIds
            let outerParams = zipWith Low.Local outerParamIds paramTs
            withVars binds $ case rt' of
                ZeroSized -> do
                    body' <- lowerExpr Nowhere body
                    pure $ if isTailRec_RetVoid self body'
                        then
                            ( Nothing
                            , outerParamIds
                            , tailCallOpt_RetVoid self outerParams innerParams body'
                            )
                        else (Nothing, innerParamIds, mapTerm (\() -> Low.TRetVoid) body')
                Sized t -> passByRef t >>= \case
                    True -> do
                        outParamId <- newLName "sret"
                        let outParamOp = Low.OLocal $ Low.Local outParamId (Low.TPtr t)
                        let outParam = Just $ Low.ByRef outParamId t
                        body' <- lowerExpr (There outParamOp) body
                        pure $ if isTailRec_RetVoid self body'
                            then
                                ( outParam
                                , outerParamIds
                                , tailCallOpt_RetVoid self outerParams innerParams body'
                                )
                            else
                                ( outParam
                                , innerParamIds
                                , mapTerm (\() -> Low.TRetVoid) body'
                                )
                    False -> do
                        body' <- lowerExpr Here body
                        pure $ if isTailRec_RetVal self body'
                            then
                                ( Nothing
                                , outerParamIds
                                , tailCallOpt_RetVal self outerParams innerParams body'
                                )
                            else (Nothing, innerParamIds, mapTerm Low.TRetVal body')
        localNames <- popLocalNames
        allocs <- popAllocs
        outerParams <- zipWithM sizedToParam outerParamIds directParamTs
        let params =
                maybe id (:) outParam $ Low.ByVal capturesName Low.VoidPtr : outerParams
        ret <- toRet rt'
        pure $ Low.FunDef name params ret body'' allocs localNames

    isTailRec_RetVoid self = go
      where
        go (Low.Block stms ()) = case last stms of
            Low.VoidCall (Low.OGlobal other) _ | other == self -> True
            Low.SBranch br -> goBranch br
            _ -> False
        goBranch = \case
            Low.BIf _ b1 b2 -> go b1 || go b2
            Low.BSwitch _ cs d -> any (go . snd) cs || go d

    isTailRec_RetVal self = go
      where
        go (Low.Block _ (Low.Expr e _)) = case e of
            Low.Call (Low.OGlobal other) _ | other == self -> True
            Low.EBranch br -> goBranch br
            _ -> False
        goBranch = \case
            Low.BIf _ b1 b2 -> go b1 || go b2
            Low.BSwitch _ cs d -> any (go . snd) cs || go d

    tailCallOpt_RetVoid self outerParams innerParams body =
        let loopInner = go body
            loopParams = zip innerParams (map Low.OLocal outerParams)
            loop = Low.Loop loopParams loopInner
        in  Low.Block [Low.SLoop loop] Low.TRetVoid
      where
        goStm = \case
            Low.VoidCall (Low.OGlobal other) args | other == self ->
                Low.Block [] (Low.Continue args)
            Low.SBranch br -> goBranch br
            stm -> Low.Block [stm] (Low.Break ())
        goBranch = \case
            Low.BIf pred conseq alt ->
                Low.Block [] . Low.LBranch $ Low.BIf pred (go conseq) (go alt)
            Low.BSwitch matchee cases default' ->
                Low.Block [] . Low.LBranch $ Low.BSwitch matchee
                                                         (map (second go) cases)
                                                         (go default')
        go (Low.Block stms ()) =
            let (initStms, lastStm) = fromJust (unsnoc stms)
                termBlock = goStm lastStm
            in  Low.Block initStms () `thenBlock` termBlock

    tailCallOpt_RetVal self outerParams innerParams body@(Low.Block _ (Low.Expr _ t)) =
        let loopInner = go body
            loopParams = zip innerParams (map Low.OLocal outerParams)
            loop = Low.Loop loopParams loopInner
            t = Low.eType (Low.blockTerm body)
        in  Low.Block [] (Low.TRetVal (Low.Expr (Low.ELoop loop) t))
      where
        go (Low.Block stms (Low.Expr lastExpr _)) =
            let termBlock = goExpr lastExpr in Low.Block stms () `thenBlock` termBlock
        goExpr = \case
            Low.Call (Low.OGlobal other) args | other == self ->
                Low.Block [] (Low.Continue args)
            Low.EBranch br -> goBranch br
            e -> Low.Block [] (Low.Break (Low.Expr e t))
        goBranch = \case
            Low.BIf pred conseq alt ->
                Low.Block [] . Low.LBranch $ Low.BIf pred (go conseq) (go alt)
            Low.BSwitch matchee cases default' ->
                Low.Block [] . Low.LBranch $ Low.BSwitch matchee
                                                         (map (second go) cases)
                                                         (go default')

    spinoffLocalId :: Low.LocalId -> Lower Low.LocalId
    spinoffLocalId x = do
        names <- use localNames
        let name = names Vec.! fromIntegral x
        newLName name

    popLocalNames :: Lower Low.VarNames
    popLocalNames = do
        xs <- use localNames
        assign localNames Vec.empty
        pure xs

    popAllocs :: Lower Low.Allocs
    popAllocs = undefined

    lowerExpr :: Destination d => d -> Expr -> Lower (Low.Block (DestTerm d))
    lowerExpr dest = \case
        Lit c -> toDest dest . Sized . operandToExpr =<< lowerConst c
        Var x -> toDest dest . mapSized operandToExpr =<< lookupVar x
        App f as -> do
            Low.Block stms1 closure <-
                bindBlockM (emitNamed "closure") =<< lowerExpr Here f
            Low.Block stms2 as' <-
                bindBlockM (fmap catBlocks . mapM emit)
                . mconcat
                . map (mapTerm (sized (: []) []))
                =<< mapM (lowerExpr HereSized) as
            Low.Block stms3 captures <- bindBlockM load =<< indexStruct 0 closure
            Low.Block stms4 f' <- bindBlockM load =<< indexStruct 1 closure
            fmap (thenBlock (Low.Block (stms1 ++ stms2 ++ stms3 ++ stms4) ()))
                . toDest dest
                . mapSized (Low.Expr (Low.Call f' (captures : as')))
                $ returneeType (typeof f')
        If pred conseq alt ->
            lowerExpr Here pred >>= bindBlockM (emitNamed "predicate") >>= bindBlockM
                (\p -> do
                    Low.Block cstms c <- lowerExpr HereSized conseq
                    Low.Block astms a <- lowerExpr HereSized alt
                    case (c, a) of
                        (Sized c'@(Low.Expr _ t), Sized a') ->
                            toDest dest . Sized $ Low.Expr
                                (Low.EBranch
                                    (Low.BIf p (Low.Block cstms c') (Low.Block astms a'))
                                )
                                t
                        (ZeroSized, ZeroSized) ->
                            bindBlockM (\() -> toDest dest ZeroSized)
                                $ Low.Block
                                      [ Low.SBranch $ Low.BIf
                                            p
                                            (Low.Block cstms ())
                                            (Low.Block astms ())
                                      ]
                                      ()
                        _ -> ice "Lower.lowerExpr If: conseq and alt not same Sized"
                )
        Fun (params, (body, tbody)) -> do
            let params' = Set.fromList params
            freeLocalVars <- view localEnv <&> \locals -> Set.toList
                (Set.intersection (Set.difference (freeVars body) params')
                                  (Map.keysSet locals)
                )
            tbody' <- lowerType tbody
            -- _ genLambda fvXs p (genTailExpr b, bt')
            captures <- if null freeLocalVars
                then pure (Low.Zero Low.VoidPtr)
                else do
                    tcaptures <-
                        defineStruct "captures"
                        . mapMaybe sizedMaybe
                        =<< mapM (\(TypedVar x t) -> mapSized (x, ) <$> lowerType t)
                                 freeLocalVars
                    -- captures' <- genHeapAllocGeneric tcaptures
                    -- populateCaptures captures' fvXs
                    -- pure captures'
                    undefined
            -- genLambda' p body (VLocal captures) fvXs
            fname <- newLName "fun"
            -- ft <- lowerType pt <&> \pt' -> closureFunType pt' bt
            -- let f = Low.OGlobal $ Low.Global fname (Low.TPtr ft)
            -- scribe outFuncs [(fname, fvXs, p, genBody $> bt)]
            -- genStruct [captures, f]
            undefined
        -- Let Def Expr
        Match es dt -> lowerMatch dest es dt
        -- Ction Ction
        Sizeof t ->
            toDest dest
                . Sized
                . operandToExpr
                =<< sized (fmap litI64 . sizeof) (pure (litI64 0))
                =<< lowerType t
        Absurd _ -> toDest dest ZeroSized
        _ -> undefined

    -- TODO: Regarding the name, I'm thinking we should probably dedup pseudo-anonymous
    --       structs of the same name, if they're structurally identical. Like with the
    --       "captures" struct for closures. It would just be polluting to generate tons
    --       of different "captures1", "captures7", ..., if the all share the same
    --       body. Like, `{ i64 }` or `{ %closure }` will probably be a very common
    --       captures type.
    defineStruct :: String -> [(String, Low.Type)] -> Lower Low.TypeId
    defineStruct _name _members = undefined

    operandToExpr x = Low.Expr (Low.EOperand x) (typeof x)

    litI64 = Low.OConst . Low.CInt . Low.I64 . fromIntegral

    lookupVar :: TypedVar -> Lower (Sized Low.Operand)
    lookupVar x = maybe ZeroSized Sized . Map.lookup x <$> view localEnv

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

    -- tStr = Low.TConst (tids Map.! ("Str", []))
    tStr = undefined

    lowerMatch
        :: forall d
         . Destination d
        => d
        -> [Expr]
        -> DecisionTree
        -> Lower (Low.Block (DestTerm d))
    lowerMatch dest matchees decisionTree = do
        Low.Block stms1 ms <- catBlocks <$> mapM lowerMatchee matchees
        Low.Block stms2 result <- lowerDecisionTree (topSelections ms) decisionTree
        pure (Low.Block (stms1 ++ stms2) result)
      where
        lowerMatchee m = lowerExpr HereSized m >>= bindBlockM
            (\case
                ZeroSized -> pure $ Low.Block [] ZeroSized
                Sized e -> mapTerm Sized <$> emitNamed "matchee" e
            )

        topSelections :: [Sized Low.Operand] -> Map Low.Access Low.Operand
        topSelections xs = Map.fromList . catMaybes $ zipWith
            (\i x -> (TopSel i, ) <$> sizedMaybe x)
            [0 ..]
            xs

        lowerDecisionTree
            :: Map Low.Access Low.Operand
            -> DecisionTree
            -> Lower (Low.Block (DestTerm d))
        lowerDecisionTree selections = \case
            DLeaf (bs, e) -> do
                bs' <- mapMaybeM (\(x, a) -> fmap (x, ) . sizedMaybe <$> lowerAccess a) bs
                vars <- selectVarBindings selections bs'
                vars `bindrBlockM` \vars' -> withVars vars' (lowerExpr dest e)
            DSwitch _span _selector _cs _def -> undefined
            DSwitchStr _selector _cs _def -> undefined

        select
            :: Low.Access
            -> Map Low.Access Low.Operand
            -> Lower (Low.Block Low.Operand, Map Low.Access Low.Operand)
        select selector selections = case Map.lookup selector selections of
            Just a -> pure (Low.Block [] a, selections)
            Nothing -> do
                (ba, selections') <- case selector of
                    TopSel _ -> ice "select: TopSel not in selections"
                    As x span' i _ts -> do
                        (ba', s') <- select x selections
                        ba'' <- bindrBlockM ba'
                            $ \a' -> asVariant a' span' (fromIntegral i)
                        pure (ba'', s')
                    Sel i _span x -> do
                        (a', s') <- select x selections
                        a'' <- bindrBlockM a' $ indexStruct (fromIntegral i)
                        pure (a'', s')
                    ADeref x -> do
                        (a', s') <- select x selections
                        a'' <- bindrBlockM a' load
                        pure (a'', s')
                pure (ba, Map.insert selector (Low.blockTerm ba) selections')

        -- Assumes matchee is of type pointer to tagged union
        asVariant matchee span variantIx = if span == 1
            then pure $ Low.Block [] matchee
            else do
                let
                    tidData = case typeof matchee of
                        Low.TPtr (Low.TConst tid) -> tid
                        _ -> ice "Lower.asVariant: type of mathee is not TPtr to TConst"
                    -- t = Low.TPtr $ typeOfDataVariant variantIx (pointee (typeof matchee))
                let tvariant = Low.TPtr (Low.TConst (tidData + 2 + variantIx))
                union <- indexStruct 1 matchee -- Skip tag to get inner union
                bindrBlockM union $ \union' ->
                    emit $ Low.Expr (Low.EAsVariant union' variantIx) tvariant

        -- typeOfDataVariant variantIx = \case
        --     -- For a sum type / tagged union, the TConst ID maps to the outer struct, the
        --     -- succeding ID maps to the inner union type, and following that is a struct
        --     -- for each variant.
        --     Low.TConst tid -> Low.TConst (tid + 2 + variantIx)
        --     _ ->

        selectVarBindings
            :: Map Low.Access Low.Operand
            -> [(TypedVar, Low.Access)]
            -> Lower (Low.Block [(TypedVar, Low.Operand)])
        selectVarBindings selections = fmap fst . foldlM
            (\(block1, selections) (x, access) -> do
                (block2, ss') <- select access selections
                pure (mapTerm (pure . (x, )) block2 <> block1, ss')
            )
            (Low.Block [] [], selections)

    lowerAccess :: Access -> Lower (Sized Low.Access)
    lowerAccess = \case
        TopSel i -> pure . Sized $ TopSel i
        As a span vi vts ->
            mapSizedM (\a' -> As a' span vi <$> lowerSizedTypes vts) =<< lowerAccess a
        Sel i span a -> mapSized (Sel i span) <$> lowerAccess a
        ADeref a -> mapSized ADeref <$> lowerAccess a

    mapTerm f b = b { Low.blockTerm = f (Low.blockTerm b) }

    thenBlock :: Low.Block () -> Low.Block a -> Low.Block a
    thenBlock (Low.Block stms1 ()) (Low.Block stms2 a) = Low.Block (stms1 ++ stms2) a

    -- bindBlock :: (a -> Low.Block b) -> Low.Block a -> Low.Block b
    -- bindBlock f (Low.Block stms1 a) =
    --     let Low.Block stms2 b = f a in Low.Block (stms1 ++ stms2) b

    bindBlockM :: Monad m => (a -> m (Low.Block b)) -> Low.Block a -> m (Low.Block b)
    bindBlockM f (Low.Block stms1 a) =
        f a <&> \(Low.Block stms2 b) -> Low.Block (stms1 ++ stms2) b

    bindrBlockM = flip bindBlockM

    emit :: Low.Expr -> Lower (Low.Block Low.Operand)
    emit = emitNamed "tmp"

    emitNamed :: String -> Low.Expr -> Lower (Low.Block Low.Operand)
    emitNamed name e = do
        name' <- newLName name
        let l = Low.Local name' (typeof e)
        pure (Low.Block [Low.Let l e] (Low.OLocal l))

    -- Assumes that struct is kept on stack. Returns pointer to member.
    indexStruct :: Word -> Low.Operand -> Lower (Low.Block Low.Operand)
    indexStruct i x = do
        t <- Low.TPtr . (!! fromIntegral i) . Low.structMembers <$> getTypeStruct
            (pointee (typeof x))
        emit (Low.Expr (Low.EGetMember i x) t)

    load :: Low.Operand -> Lower (Low.Block Low.Operand)
    load addr = emit $ Low.Expr (Low.Load addr) (pointee (typeof addr))

    catBlocks :: [Low.Block a] -> Low.Block [a]
    catBlocks = mconcat . map (mapTerm pure)

    withVars :: [(TypedVar, Low.Operand)] -> Lower a -> Lower a
    withVars vs ma = foldl (flip (uncurry withVar)) ma vs

    withVar :: TypedVar -> Low.Operand -> Lower a -> Lower a
    withVar lhs rhs = locally localEnv (Map.insert lhs rhs)

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

    defineDatas :: Lower ()
    defineDatas = do
        (tids', tconsts') <-
            bimap (Seq.fromList . (builtinTypeDefs ++)) Map.fromList . snd <$> foldlM
                (\(i, (env, ids)) (inst@(name, _), variants) ->
                    fmap (bimap (i +) ((env, ids) <>))
                        $ defineData i name variants
                        <&> \case
                                Nothing -> (0, ([], []))
                                Just (outer, inners) ->
                                    ( 1 + fromIntegral (length inners)
                                    , ((name, outer) : inners, [(inst, i)])
                                    )
                )
                (fromIntegral (length builtinTypeDefs), ([], []))
                (Map.toList datas)
        let tdefs' = Map.fromList $ zip (toList tids') [0 ..]
        assign tconsts tconsts'
        assign tids tids'
        assign tdefs tdefs'
      where
        defineData
            :: Low.TypeId
            -> String
            -> [(String, VariantTypes)]
            -> Lower (Maybe (Low.TypeDef', [Low.TypeDef]))
        defineData typeId0 name variants = do
            let variantNames = map fst variants
            variantTypess <- mapM (lowerSizedTypes . snd) variants
            case variantTypess of
                [] -> pure Nothing -- Uninhabited type
                [[]] -> pure Nothing
                [ts] -> Just . (, []) <$> structDef ts
                _ | all null variantTypess ->
                    pure $ Just (Low.DEnum (Vec.fromList variantNames), [])
                _ -> do
                    aMax <- maximum <$> mapM alignmentofStruct variantTypess
                    sMax <- maximum <$> mapM sizeofStruct variantTypess
                    let variants' = Vec.fromList (zip variantNames [typeId0 + 2 ..])
                        sTag = variantsTagBits variants' :: Word
                        tag = if
                            | sTag <= 8 -> Low.TI8
                            | sTag <= 16 -> Low.TI16
                            | sTag <= 32 -> Low.TI32
                            | sTag <= 64 -> Low.TI64
                            | otherwise -> ice "Lower.defineData: tag > 64 bits"
                        unionId = typeId0 + 1
                    outerStruct <- structDef [tag, Low.TConst unionId]
                    let innerUnion =
                            (name ++ "_union", Low.DUnion $ Low.Union variants' sMax aMax)
                    variantStructs <- zip variantNames <$> mapM structDef variantTypess
                    pure $ Just (outerStruct, innerUnion : variantStructs)
        structDef ts = liftM2 (Low.DStruct .* Low.Struct ts)
                              (alignmentofStruct ts)
                              (sizeofStruct ts)

    -- nameUniquely :: (a -> String) -> (String -> a -> a) -> [a] -> [a]
    -- nameUniquely get set =
    --     ((reverse . fst) .) $ flip foldl ([], Map.empty) $ \(ds, seen) d ->
    --         let name = get d
    --             uq n =
    --                 let name' = if n == 0 then name else name ++ "_" ++ show (n :: Int)
    --                 in  if Map.findWithDefault 0 name' seen == 0
    --                         then (name', Map.insert name (n + 1) seen)
    --                         else uq (n + 1)
    --             (name', seen') = uq (Map.findWithDefault 0 name seen)
    --         in  (set name' d : ds, seen')

    sized f b = \case
        ZeroSized -> b
        Sized a -> f a

    sizedMaybe = \case
        ZeroSized -> Nothing
        Sized t -> Just t

    -- fromSized = \case
    --     ZeroSized -> ice "Lower.unSized: was ZeroSized"
    --     Sized x -> x

    toParam :: name -> Sized Low.Type -> Lower (Maybe (Low.Param name))
    toParam name = \case
        ZeroSized -> pure Nothing
        Sized t -> Just <$> sizedToParam name t

    sizedToParam name t = passByRef t <&> \case
        True -> Low.ByRef name t
        False -> Low.ByVal name t

    toRet = \case
        ZeroSized -> pure Low.RetVoid
        Sized t -> passByRef t <&> \case
            True -> Low.RetVoid
            False -> Low.RetVal t

    lowerSizedTypes :: [Type] -> Lower [Low.Type]
    lowerSizedTypes = fmap catMaybes . mapM (fmap sizedMaybe . lowerType)

    -- TODO: Should respect platform ABI. For example wrt size of TNatSize on 32-bit
    --       vs. 64-bit platform.
    --
    -- | The Low representation of a type in expression-context
    lowerType :: Type -> Lower (Sized Low.Type)
    lowerType = \case
        TPrim (TNat w) -> pure $ genIntT w
        TPrim TNatSize -> pure $ genIntT wordsizeBits
        TPrim (TInt w) -> pure $ genIntT w
        TPrim TIntSize -> pure $ genIntT wordsizeBits
        TPrim TF32 -> pure $ Sized Low.TF32
        TPrim TF64 -> pure $ Sized Low.TF64
        TFun _ _ -> pure $ Sized closureType
        TBox t -> lowerType t <&> \case
            ZeroSized -> Sized Low.VoidPtr
            Sized t' -> Sized $ Low.TPtr t'
        TConst tc -> use tconsts <&> Map.lookup tc <&> \case
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

    pointee = \case
        Low.TPtr t -> t
        _ -> ice "Lower.pointee of non pointer type"

    returnee = \case
        Low.TFun _ ret -> ret
        _ -> ice "Lower.returnee of non function type"

    returneeType = returnee >>> \case
        Low.RetVal t -> Sized t
        Low.RetVoid -> ZeroSized

    getTypeStruct = \case
        Low.TConst i -> use tids <&> (Seq.!? fromIntegral i) <&> \case
            Just (_, Low.DStruct struct) -> struct
            _ -> ice "Low.getTypeStruct: TypeDef in tenv is not DStruct"
        _ -> ice "Low.getTypeStruct: type is not a TConst"

    -- TODO: Maybe we could get rid of all ad-hoc logic using this function, by wrapping
    --       the type returned from lowerType in not just a Sized vs. ZeroSized, but also a
    --       Stack vs. Register.
    --
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
    passByRef :: Low.Type -> Lower Bool
    passByRef t = sizeof t <&> (> 2 * 8)

    sizeof = tidsHelper Low.sizeof
    -- _alignmentof = Low.alignmentof tenv
    sizeofStruct = tidsHelper Low.sizeofStruct
    alignmentofStruct = tidsHelper Low.alignmentofStruct

    tidsHelper f x = use tids <&> \tids' -> f (\tid -> tids' Seq.!? fromIntegral tid) x

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

newLName :: String -> Lower Low.LocalId
newLName x = do
    localId <- Vec.length <$> use localNames
    modifying localNames (`Vec.snoc` x)
    pure (fromIntegral localId)
