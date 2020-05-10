stack install --profile
carth c $1 +RTS -p
ghc-prof-flamegraph carth.prof
