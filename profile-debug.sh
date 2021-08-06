stack install --profile
carth c --debug $1 +RTS -p
mv carth.prof carth-debug.prof
ghc-prof-flamegraph carth-debug.prof
