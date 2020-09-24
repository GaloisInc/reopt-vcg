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
    lean4-build)
        ./scripts/build-lean4.sh lean4/deps/lean4 lean4/deps/lean4/build opt/lean llvm-config-8 -DCMAKE_C_COMPILER=gcc -DCMAKE_CXX_COMPILER=g++
        ;;
    build)
        make -C lean4 LEAN_CXX=clang-8 LEAN=$PWD/opt/lean/bin/lean LEANC=$PWD/opt/lean/bin/leanc LLVM_CONFIG=llvm-config-8 CXX=clang-8 -j4
        ;;
    run-tests)
        pushd lean4/tests/unit-tests/src/Test/ > /dev/null
        bash test.sh
        popd > /dev/null
        pushd lean4/tests/integration-tests/interactive/ > /dev/null
        bash test.sh
        popd > /dev/null
        pushd lean4/tests/integration-tests/export/ > /dev/null
        bash test.sh
        popd > /dev/null
        ;;
    *) echo "unknown command"; exit 1;;
esac    
