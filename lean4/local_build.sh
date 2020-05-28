#!/bin/bash

make LEAN_CXX=clang-8 LEAN=$PWD/../local/bin/lean LEANC=$PWD/../local/bin/leanc LLVM_CONFIG=llvm-config-8 CXX=clang-8

