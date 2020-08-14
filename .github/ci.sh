#!/usr/bin/env bash
# inspired by https://github.com/GaloisInc/cryptol/blob/master/.github/ci.sh

set -Eeuo pipefail

if [[ $# -lt 1 ]];
then
    echo "Need a command"
    exit 1
fi    

COMMAND="$1"
shift

case $COMMAND in
    lean4-sha) git submodule status lean4/deps/lean4 | awk '{print "::set-output name=lean4-sha::"$1}' ;;
    #    lean4-build) ./scripts/build-lean4.sh lean4/deps/lean4/   ;;
    lean4-build)
        ./scripts/build-lean4.sh lean4/deps/lean4 lean4/deps/lean4/build opt/lean llvm-config-8 -DCMAKE_C_COMPILER=gcc -DCMAKE_CXX_COMPILER=g++
        ;;
    build) echo "compiling";;
    *) echo "unknown command"; exit 1;;
esac    
