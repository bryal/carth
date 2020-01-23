(use-modules (gnu)
             (guix packages)
             (guix build-system haskell)
             (guix download)
             ((guix licenses) #:prefix license:))

(use-package-modules haskell haskell-xyz haskell-check llvm)

(package
  (name "carth")
  (version "0.3.1")
  (source (local-file "./" "carth" #:recursive? #t))
  (build-system haskell-build-system)
  (arguments `(#:haddock? #f #:tests? #f))
  (inputs `(("ghc-megaparsec" ,ghc-megaparsec)
            ("ghc-microlens-platform" ,ghc-microlens-platform)
            ("ghc-llvm-hs-pure" ,ghc-llvm-hs-pure)
            ("ghc-llvm-hs" ,ghc-llvm-hs)
            ("ghc-utf8-string" ,ghc-utf8-string)))
  (home-page "https://github.com/bryal/carth")
  (synopsis "The Carth compiler")
  (description "The compiler for Carth -- a purely functional
programming language with Scheme-like syntax. Work in progress.")
  (license license:agpl3+))
