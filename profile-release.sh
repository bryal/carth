stack install --profile
carth c $1 +RTS -p
mv carth.prof carth-release.prof
ghc-prof-flamegraph carth-release.prof
