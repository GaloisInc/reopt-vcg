#!/bin/bash

RESDIR=$PWD/nweb-results

mkdir -p $RESDIR

# Force recomp.
/usr/local/opt/make/libexec/gnubin/make LLVM_CONFIG=/usr/local/opt/llvm@8/bin/llvm-config LDFLAGS="-L/usr/local/lib" 

DATETAG=`date +%Y-%m-%d-%H:%M:%S`
OUT=$RESDIR/run-$DATETAG.txt
rm -f $RESDIR/latest.txt

ln -s $OUT $RESDIR/latest.txt     

# --keep-order 
# ls -1 deps/k-x86-semantics/k-semantics/*.lean | grep -v incq.lean | parallel --joblog insns-logs/insns-$DATETAG.log ./check-one-insn.sh {/.} > insns-logs/insns-$DATETAG.txt

pushd test-programs/nweb/ > /dev/null

RUNTIME=`(/usr/bin/time ../../build/bin/reopt-vcg nweb23.ann > $OUT) 2>&1`
GITREV=`git rev-parse HEAD`

echo "# gitrev $GITREV time $RUNTIME" >> $OUT

popd > /dev/null

