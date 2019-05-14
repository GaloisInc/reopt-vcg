#!/bin/bash
set -e

if [ -z ${LEAN_DIR+x} ]; then
    echo "Please set LEAN_DIR to lean root"
    exit 1
fi

LEAN="$LEAN_DIR/bin/lean"
LEANC="$LEAN_DIR/bin/leanc"

# Build C wrappers
clang++ "-I$LEAN_DIR/src" "-I$LEAN_DIR/src/runtime" -I$LLVM_DIR/include -std=c++11 -c io.cpp

$LEAN --cpp="io.lean.cpp" io.lean
$LEAN --cpp="io_test.lean.cpp" io_test.lean

$LEANC -O3 -o io_test "io_test.lean.cpp"  io.lean.cpp io.o 
