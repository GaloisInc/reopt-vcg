#!/bin/bash

insn=$1
/usr/local/opt/make/libexec/gnubin/make LLVM_CONFIG=/usr/local/opt/llvm@8/bin/llvm-config LDFLAGS="-L/usr/local/lib" build/olean/deps/k-x86-semantics/src/KX86Semantics/Gen/I_$insn.olean > deps/k-x86-semantics/src/KX86Semantics/Gen/O_$insn.txt 2>&1
if [ $? -eq 0 ];
then
    rm deps/k-x86-semantics/src/KX86Semantics/Gen/O_$insn.txt
    echo $insn
else
    echo "# $insn"
fi
