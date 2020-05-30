{-# LANGUAGE OverloadedStrings, LambdaCase, TupleSections, FlexibleContexts #-}

-- | Codegeneration related to external C function declarations
--
--   `extern` forms are translated pretty literally to extern declarations,
--   taking the C ABI into account when deciding whether to pass a ref on the
--   stack or in registers, etc. Further, ad wrapper-closure is generated around
--   the function, which translates the calling convention from C to whatever we
--   use internally (e.g. tailcc or fastcc), adds a dummy `captures` parameter
--   to make it compatible with all other function signatures, and finally it
--   adds currying.
--
--   One might think that simply declaring all function definitions and function
--   calls as being of the same "ccc" LLVM calling convention would allow us to
--   pass arguments and return results as we please, and everything will be
--   compatible? I sure did, however, that is not the case. To be compatible
--   with C FFIs, we also have to actually conform to the C calling convention,
--   which contains a bunch of details about how more complex types should be
--   passed and returned. Currently, we pass and return simple types by value,
--   and complex types by reference (param by ref, return via sret param).
--
--   See the definition of `passByRef` for up-to-date details about which types
--   are passed how.
module Extern (withExternSigs, genExterns, callExtern) where

import LLVM.AST
import LLVM.AST.ParameterAttribute
import qualified LLVM.AST.Constant as LLConst
import Control.Monad.Writer
import qualified Data.Map as Map
import Lens.Micro.Platform (assign)
import LLVM.AST.Typed
import qualified LLVM.AST.Type as LLType
import Data.Functor

import Misc
import SrcPos
import qualified Monomorphic as M
import Monomorphic hiding (Type, Const)
import Gen


withExternSigs :: [(String, M.Type, SrcPos)] -> Gen' a -> Gen' a
withExternSigs es ga = do
    es' <- forM es $ \(name, t, _) -> do
        t' <- genType' t
        pure
            ( TypedVar name t
            , ConstantOperand
                $ LLConst.GlobalReference (LLType.ptr t') (mkName ("_wrapper_" ++ name))
            )
    augment env (Map.fromList es') ga

genExterns :: [(String, M.Type, SrcPos)] -> Gen' [Definition]
genExterns = fmap join . mapM genExtern

genExtern :: (String, M.Type, SrcPos) -> Gen' [Definition]
genExtern (name, t, pos) = do
    ((pts, rt), (ps, rt')) <- genExternTypeSig t
    let externDef = GlobalDefinition (externFunc (mkName name) ps rt' [] [])
    wrapperDefs <- genWrapper pos name rt pts
    pure (externDef : wrapperDefs)

genWrapper :: SrcPos -> String -> Type -> [M.Type] -> Gen' [Definition]
genWrapper pos externName rt paramTs =
    case (zipWith (TypedVar . ("x" ++) . show) [1 :: Word ..] paramTs) of
        [] -> ice "genWrapper of empty param list"
        (firstParam : restParams) -> do
            let genCallExtern :: [TypedVar] -> Gen Val
                genCallExtern vars = do
                    ts <- mapM (\(TypedVar _ t) -> genType t) vars
                    vars' <- mapM lookupVar vars
                    as <- forM (zip vars' ts) $ \(v, t) -> passByRef t >>= \case
                        True -> fmap (, [ByVal]) (getVar v)
                        False -> fmap (, []) (getLocal v)
                    let ats = map (typeOf . fst) as
                    let fname = mkName externName
                    passByRef rt >>= \case
                        True -> do
                            out <- emitReg "out" (alloca rt)
                            let f = ConstantOperand $ LLConst.GlobalReference
                                    (LLType.ptr $ FunctionType LLType.void
                                                               (typeOf out : ats)
                                                               False
                                    )
                                    fname
                            emitDo $ callExtern f ((out, [SRet]) : as)
                            pure (VVar out)
                        False ->
                            let f = ConstantOperand $ LLConst.GlobalReference
                                    (LLType.ptr $ FunctionType rt ats False)
                                    fname
                            in  if rt == LLType.void
                                    then emitDo (callExtern f as) $> VLocal litUnit
                                    else fmap VLocal $ emitAnonReg $ WithRetType
                                        (callExtern f as)
                                        rt
            let
                genWrapper' fvs ps' = do
                    r <- getLocal =<< case ps' of
                        [] -> genCallExtern fvs
                        (p : ps) -> do
                            pts <- mapM (\(TypedVar _ t) -> genType t) ps
                            let bt = foldr closureType rt pts
                            genLambda fvs p (genWrapper' (fvs ++ [p]) ps $> (), bt)
                    if typeOf r == typeUnit
                        then commitFinalFuncBlock retVoid $> LLType.void
                        else commitFinalFuncBlock (ret r) $> typeOf r
            let wrapperName = "_wrapper_" ++ externName
            assign lambdaParentFunc (Just wrapperName)
            let fname = mkName (wrapperName ++ "_func")
            (f, gs) <- locallySet srcPos (Just pos)
                $ genFunDef
                      (fname, [], pos, firstParam, genWrapper' [firstParam] restParams)
            let fref = LLConst.GlobalReference (LLType.ptr (typeOf f)) fname
            let captures = LLConst.Null (LLType.ptr typeUnit)
            let closure = litStruct [captures, fref]
            let closureDef = simpleGlobConst (mkName ("_wrapper_" ++ externName))
                                             (typeOf closure)
                                             closure
            pure (GlobalDefinition closureDef : GlobalDefinition f : gs)
