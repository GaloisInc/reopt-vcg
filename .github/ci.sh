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
    run-tests)
        pushd tests/unit-tests/src/Test/ > /dev/null
        bash test.sh
        popd > /dev/null
        pushd tests/integration-tests/k-interactive/ > /dev/null
        bash test.sh
        popd > /dev/null
        pushd tests/integration-tests/k-export/ > /dev/null
        bash test.sh
        popd > /dev/null
        ;;
    *) echo "unknown command"; exit 1;;
esac
