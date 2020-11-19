#!/bin/bash

set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
TESTSYM=$DIR/../build/test-sym

out=`mktemp testfile-XXXXXX`
out_obj=${out%.S}.o

cat <<EOF > $out
    .text
    $@
EOF

gcc -x assembler -c $out
# objdump -d $out_obj 
objdump -d $out_obj | sed -n 's/^[[:space:]]*0:[[:space:]]*\([0-9a-fA-F ]*[0-9a-fA-F]\{2\}\).*/\1/p' | \
    tr ' ' '\n' | while read a; do printf "%d " 0x$a; done | xargs $TESTSYM
# gobjdump --disassembler-options=intel-mnemonic -d $out_obj | grep '0:'
rm -f $out $out_obj
