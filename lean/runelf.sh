#!/bin/bash -e

DECODER=$PWD/../llvm-tablegen-support/llvm-tablegen-support

BINARY=$1
START=$2
LASTP1=$3

lean --run runelf.lean $DECODER $BINARY
