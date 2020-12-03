#!/bin/bash

# force compilatin of deps
./scripts/check-one-insn.sh addq

rm -f build/olean/deps/k-x86-semantics/src/KX86Semantics/Gen/*.olean
rm -f deps/k-x86-semantics/src/KX86Semantics/Gen/O_*.txt

DATETAG=`date +%Y-%m-%d-%H:%M:%S`

rm -f insns-logs/latest-log.txt insns-logs/latest.txt

ln -s $PWD/insns-logs/insns-$DATETAG.log insns-logs/latest-log.txt 
ln -s $PWD/insns-logs/insns-$DATETAG.txt insns-logs/latest.txt     

# --keep-order 
ls -1 deps/k-x86-semantics/k-semantics/*.lean | grep -v incq.lean | parallel --joblog insns-logs/insns-$DATETAG.log ./scripts/check-one-insn.sh {/.} > insns-logs/insns-$DATETAG.txt

