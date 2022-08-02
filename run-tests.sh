cd test/tests/

pushd good
find ./ -name "*.carth" -type f -exec bash -c 'echo -n $(basename "{}") "... " ; if [ "$(stack run carth -- run "{}")" = "$(head -n1 "{}" | tail -c +4)" ]; then echo "OK"; else echo "<<<<<< ERR >>>>>>"; fi' \;
popd
