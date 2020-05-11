#!/usr/bin/env bash
cd "$(dirname "$0")"
if [ $# -ne 2 -a $# -ne 1 ]; then
    echo "Usage: test.sh [lean-executable-path] [yes/no]?"
    exit 1
fi

LEAN=$1

if [ $# -ne 2 ]; then
    INTERACTIVE=no
else
    INTERACTIVE=$2
fi
NUM_TESTS=0
NUM_FAILS=0
for f in *.lean; do
    NUM_TESTS=$(($NUM_TESTS+1))
    bash ./test_single.sh $LEAN $f $INTERACTIVE
    if [ $? -ne 0 ]; then
        NUM_FAILS=$(($NUM_FAILS+1))
    fi
done

if [ $NUM_FAILS -gt 0 ]; then
    echo "-- $NUM_FAILS out of $NUM_TESTS tests failed"
    exit 1
else
    echo "-- All $NUM_TESTS tests passed"
    exit 0
fi
