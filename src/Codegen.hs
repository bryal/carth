{-# LANGUAGE OverloadedStrings #-}

module Codegen where

import qualified LLVM.AST as L
import qualified LLVM.AST.CallingConvention as CallConv
import qualified LLVM.AST.Constant as C
import qualified LLVM.AST.Global as G
import qualified LLVM.AST.Instruction as I
import qualified LLVM.AST.Operand as O
import qualified LLVM.AST.Type as T
import Data.String
import System.FilePath

import qualified Mono

genModule :: FilePath -> Mono.MExpr -> Mono.Defs -> L.Module
genModule moduleFilePath main defs = L.defaultModule
    { L.moduleName = fromString ((takeBaseName moduleFilePath))
    , L.moduleSourceFileName = fromString moduleFilePath
    , L.moduleDefinitions = genMain main : genDefs defs
    }

genMain :: Mono.MExpr -> L.Definition
genMain main = undefined
    main
    (L.GlobalDefinition
        (G.functionDefaults
            { G.name = "main"
            , G.parameters = ([], False)
            , G.returnType = T.VoidType
            , G.basicBlocks = [mainEntry]
            }
        )
    )

mainEntry :: L.BasicBlock
mainEntry = G.BasicBlock
    "entry"
    [ I.Do
          (I.Call
              { I.tailCallKind = Nothing
              , I.callingConvention = CallConv.C
              , I.returnAttributes = []
              , I.function = Right
                  (O.ConstantOperand
                      (C.GlobalReference
                          (T.ptr
                              (T.FunctionType
                                  { T.argumentTypes = [T.i8]
                                  , T.resultType = T.i32
                                  , T.isVarArg = False
                                  }
                              )
                          )
                          "putchar"
                      )
                  )
              , I.arguments = [ ( O.ConstantOperand
                                    (C.Int
                                        { C.integerBits = 8
                                        , C.integerValue = 65
                                        }
                                    )
                                , []
                                )
                              ]
              , I.functionAttributes = []
              , I.metadata = []
              }
          )
    ]
    (I.Do (I.Ret Nothing []))

genDefs :: Mono.Defs -> [L.Definition]
genDefs defs = undefined defs [putchar]

putchar :: L.Definition
putchar = L.GlobalDefinition
    (G.functionDefaults
        { G.name = "putchar"
        , G.parameters = ([G.Parameter T.i8 "x" []], False)
        , G.returnType = T.i32
        }
    )
