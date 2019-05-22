{-# LANGUAGE OverloadedStrings, LambdaCase, TemplateHaskell #-}

module Codegen where

import LLVM.AST
import qualified LLVM.AST.CallingConvention as CallConv
import qualified LLVM.AST.Constant as LLConst
import qualified LLVM.AST.Global as LLGlob
import qualified LLVM.AST.Type as LLType
import Data.String
import System.FilePath
import Control.Monad.Writer
-- import Control.Lens (makeLenses)

import qualified Annot as An
import qualified Mono

-- data St = St
--     { blocks :: [BasicBlock] }
-- makeLenses ''St

type Gen a = Writer [BasicBlock] a

genModule :: FilePath -> Mono.MExpr -> Mono.Defs -> Module
genModule moduleFilePath main defs = defaultModule
    { moduleName = fromString ((takeBaseName moduleFilePath))
    , moduleSourceFileName = fromString moduleFilePath
    , moduleDefinitions = genMain main : genDefs defs
    }

genMain :: Mono.MExpr -> Definition
genMain main = GlobalDefinition
    (functionDefaults
        { LLGlob.name = "main"
        , LLGlob.parameters = ([], False)
        , LLGlob.returnType = VoidType
        , LLGlob.basicBlocks = execWriter (genExpr main)
        }
    )

genExpr :: Mono.MExpr -> Gen Operand
genExpr = \case
    An.Lit c -> pure (ConstantOperand (toLlvmConstant c))
    An.Var _ _ -> undefined
    An.App _ _ -> undefined
    An.If _ _ _ -> undefined
    An.Fun _ _ -> undefined
    An.Let _ _ -> undefined
    -- main


toLlvmConstant :: An.Const -> LLConst.Constant
toLlvmConstant = \case
    An.Unit -> litStruct []
    An.Int _ -> undefined
    An.Double _ -> undefined
    An.Char _ -> undefined
    An.Str _ -> undefined
    An.Bool _ -> undefined

litStruct :: [LLConst.Constant] -> LLConst.Constant
litStruct = LLConst.Struct Nothing False

mainEntry :: BasicBlock
mainEntry = BasicBlock
    "entry"
    [ Do $ Call
          { tailCallKind = Nothing
          , callingConvention = CallConv.C
          , returnAttributes = []
          , function = Right
              (ConstantOperand
                  (LLConst.GlobalReference
                      (LLType.ptr
                          (FunctionType
                              { argumentTypes = [LLType.i8]
                              , resultType = LLType.i32
                              , isVarArg = False
                              }
                          )
                      )
                      "putchar"
                  )
              )
          , arguments = [ ( ConstantOperand
                              (LLConst.Int
                                  { LLConst.integerBits = 8
                                  , LLConst.integerValue = 65
                                  }
                              )
                          , []
                          )
                        ]
          , functionAttributes = []
          , metadata = []
          }
    ]
    (Do (Ret Nothing []))

genDefs :: Mono.Defs -> [Definition]
genDefs defs = undefined defs [putchar]

putchar :: Definition
putchar = GlobalDefinition $ functionDefaults
    { LLGlob.name = "putchar"
    , LLGlob.parameters = ([LLGlob.Parameter LLType.i8 "x" []], False)
    , LLGlob.returnType = LLType.i32
    }
