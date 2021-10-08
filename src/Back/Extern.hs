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
module Back.Extern (
    ) where







