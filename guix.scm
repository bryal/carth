;; -*- eval: (guix-devel-mode) -*-

(use-modules (gnu)
             (guix packages)
             (guix build-system haskell)
             (guix build-system cargo)
             (guix download)
             ((guix licenses)
              #:prefix license:))

(use-package-modules haskell haskell-xyz haskell-check
                     llvm
                     crates-io
                     libsigsegv
                     tls
                     bdw-gc)

(define ghc-llvm-hs-pretty
  (package
    (name "ghc-llvm-hs-pretty")
    (version "0.9.0.0")
    (source
     (origin
       (method url-fetch)
       (uri (hackage-uri "llvm-hs-pretty" version))
       (sha256
        (base32 "17kj713j38lg6743dwv1gd0wcls888zazzhlw3xvxzw2n8bjahyj"))))
    (build-system haskell-build-system)
    (inputs (list ghc-llvm-hs-pure ghc-prettyprinter))
    (native-inputs
     (list ghc-tasty
           ghc-tasty-hspec
           ghc-tasty-hunit
           ghc-tasty-golden
           ghc-llvm-hs))
    (home-page "https://github.com/llvm-hs/llvm-hs-pretty")
    (synopsis "A pretty printer for LLVM IR.")
    (description
     "This package provides a pretty printer for the LLVM AST types provided by
llvm-hs.")
    (license license:expat)))

(define carth-std-rs
  (package
    (name "carth-std-rs")
    (version "0.4.0")
    (source
     (file-union name
                 `(("Cargo.toml" ,(local-file "std-rs/Cargo.toml"))
                   ("src" ,(local-file "std-rs/src" #:recursive? #t)))))
    (build-system cargo-build-system)
    (inputs `(("libsigsegv" ,libsigsegv)
              ("openssl" ,openssl)
              ("libgc" ,libgc)))
    (arguments
     `(#:cargo-inputs
       (("rust-libc" ,rust-libc-0.2)
        ("rust-native-tls" ,rust-native-tls-0.2))
       #:phases
       (modify-phases %standard-phases
         (replace 'install
           (lambda* (#:key inputs outputs #:allow-other-keys)
             (let* ((out (assoc-ref outputs "out"))
                    (lib (string-append out "/lib")))
               (mkdir-p lib)
               ;; Both static and shared libraries are produced, and needed. The
               ;; shared is used in the JIT when doing `cart run`, and the static
               ;; is used when compiling with `carth compile`.
               (copy-file "target/release/libcarth_std_rs.a"
                          (string-append lib "/libcarth_std_rs.a"))
               (copy-file "target/release/libcarth_std_rs.so"
                          (string-append lib "/libcarth_std_rs.so"))))))))
    (home-page "https://github.com/bryal/carth")
    (synopsis "The Carth foreign core library")
    (description "The core and runtime library for Carth -- a purely functional
programming language with Scheme-like syntax. Work in progress.")
    (license license:agpl3+)))

(package
  (name "carth")
  (version "0.4.0")
  (source
   (file-union name
               `(("carth.cabal" ,(local-file "carth.cabal"))
                 ("README.md" ,(local-file "README.md"))
                 ("CHANGELOG.org" ,(local-file "CHANGELOG.org"))
                 ("LICENSE-AGPLv3" ,(local-file "LICENSE-AGPLv3"))
                 ("LICENSE-ACSL" ,(local-file "LICENSE-ACSL"))
                 ("Setup.hs" ,(local-file "Setup.hs"))
                 ("src" ,(local-file "src" #:recursive? #t))
                 ("app" ,(local-file "app" #:recursive? #t))
                 ("test" ,(local-file "test" #:recursive? #t)))))
  (build-system haskell-build-system)
  (arguments
   `(#:haddock?
     #f
     #:tests?
     #f
     ;; #:phases
     ;; (modify-phases %standard-phases
     ;;   (add-before 'configure 'patch-runtime-lib-paths
     ;;     (lambda* (#:key inputs outputs #:allow-other-keys)
     ;;       (let* ((sigsegv (assoc-ref inputs "libsigsegv"))
     ;;              (std-rs (assoc-ref inputs "carth-std-rs"))
     ;;              (sigsegv-a (string-append sigsegv "/lib/libsigsegv.a"))
     ;;              (sigsegv-so (string-append sigsegv "/lib/libsigsegv.so"))
     ;;              (foreign-a (string-append std-rs "/lib/libcarth_std_rs.a"))
     ;;              (foreign-so (string-append std-rs "/lib/libcarth_std_rs.so")))
     ;;         (invoke "ls" "-la" "src/Compile.hs")
     ;;         (invoke "cat" "/etc/passwd")
     ;;         (chmod "src/Compile.hs" #o755)
     ;;         (substitute* "src/Compile.hs"
     ;;           (("-l:libcarth_std_rs.a") (string-append "-l:" foreign-a))
     ;;           (("-lsigsegv") (string-append "-l:" sigsegv-a))
     ;;           (("libsigsegv.so") sigsegv-so)
     ;;           (("libcarth_std_rs.so") foreign-so))))))
     ))
  (inputs
   `(("ghc-megaparsec" ,ghc-megaparsec)
     ("ghc-microlens-platform" ,ghc-microlens-platform)
     ("ghc-llvm-hs-pretty" ,ghc-llvm-hs-pretty)
     ("ghc-llvm-hs-pure" ,ghc-llvm-hs-pure)
     ("ghc-llvm-hs" ,ghc-llvm-hs)
     ("ghc-utf8-string" ,ghc-utf8-string)))
  (native-inputs (list llvm-9))
  (propagated-inputs
   `(("carth-std-rs" ,carth-std-rs)
     ("libsigsegv" ,libsigsegv)))
  (home-page "https://github.com/bryal/carth")
  (synopsis "The Carth compiler")
  (description "The compiler for Carth -- a purely functional
programming language with Scheme-like syntax. Work in progress.")
  (license license:agpl3+))
