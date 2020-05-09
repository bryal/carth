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
                     libsigsegv)

(define carth-foreign-core
  (package
    (name "carth-foreign-core")
    (version "0.4.0")
    (source
     (file-union name
                 `(("Cargo.toml" ,(local-file "foreign-core/Cargo.toml"))
                   ("src" ,(local-file "foreign-core/src" #:recursive? #t)))))
    (build-system cargo-build-system)
    (inputs `(("libsigsegv" ,libsigsegv)))
    (arguments
     `(#:cargo-inputs
       (("rust-libc" ,rust-libc-0.2))
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
               (copy-file "target/release/libcarth_foreign_core.a"
                          (string-append lib "/libcarth_foreign_core.a"))
               (copy-file "target/release/libcarth_foreign_core.so"
                          (string-append lib "/libcarth_foreign_core.so"))))))))
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
                 ("README.org" ,(local-file "README.org"))
                 ("CHANGELOG.org" ,(local-file "CHANGELOG.org"))
                 ("LICENSE" ,(local-file "LICENSE"))
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
     ;;              (foreign-core (assoc-ref inputs "carth-foreign-core"))
     ;;              (sigsegv-a (string-append sigsegv "/lib/libsigsegv.a"))
     ;;              (sigsegv-so (string-append sigsegv "/lib/libsigsegv.so"))
     ;;              (foreign-a (string-append foreign-core "/lib/libcarth_foreign_core.a"))
     ;;              (foreign-so (string-append foreign-core "/lib/libcarth_foreign_core.so")))
     ;;         (invoke "ls" "-la" "src/Compile.hs")
     ;;         (invoke "cat" "/etc/passwd")
     ;;         (chmod "src/Compile.hs" #o755)
     ;;         (substitute* "src/Compile.hs"
     ;;           (("-l:libcarth_foreign_core.a") (string-append "-l:" foreign-a))
     ;;           (("-lsigsegv") (string-append "-l:" sigsegv-a))
     ;;           (("libsigsegv.so") sigsegv-so)
     ;;           (("libcarth_foreign_core.so") foreign-so))))))
     ))
  (inputs
   `(("ghc-megaparsec" ,ghc-megaparsec)
     ("ghc-microlens-platform" ,ghc-microlens-platform)
     ("ghc-llvm-hs-pure" ,ghc-llvm-hs-pure)
     ("ghc-llvm-hs" ,ghc-llvm-hs)
     ("ghc-utf8-string" ,ghc-utf8-string)))
  (propagated-inputs
   `(("carth-foreign-core" ,carth-foreign-core)
     ("libsigsegv" ,libsigsegv)))
  (home-page "https://github.com/bryal/carth")
  (synopsis "The Carth compiler")
  (description "The compiler for Carth -- a purely functional
programming language with Scheme-like syntax. Work in progress.")
  (license license:agpl3+))
