{-# LANGUAGE TemplateHaskell, DuplicateRecordFields #-}

-- | Code generation operations, generally not restricted to be used with AST
--   inputs. Basically an abstraction over llvm-hs. Reusable operations that can
--   be used both in Codegen and for manually generating LLVM code in other
--   situations.
module Back.Gen where

