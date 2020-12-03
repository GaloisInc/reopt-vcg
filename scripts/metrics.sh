#!/bin/bash

insns=$1

total=$(wc -l < $insns)
nok=$(grep -c -v '^#' $insns)
missed=$(grep -c '^#' $insns)
startv=$(grep -c '^# v' $insns)
terrors=$(grep -l -E '(error: unexpected argument at application)|(type mismatch)' deps/k-x86-semantics/src/KX86Semantics/Gen/O_* | wc -l)
uerrors=$(grep -l -E 'unknown ident' deps/k-x86-semantics/src/KX86Semantics/Gen/O_* | wc -l)

printf "Summary: %d total, %d compiled, %d failed (%d vector, %d non-vector): %d missing def, %d maybe lean bug\n" $total $nok $missed $startv $(($missed - $startv)) $uerrors $terrors

