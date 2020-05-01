#!/bin/bash
set -e

if [ $# -lt 3 ];
then
    echo "Usage: build-lean4.sh srcdir builddir installdir llvm-config"
    exit 1
fi   

SRCDIR=$(cd $1 && pwd)
RELBUILDDIR=$2
mkdir -p $3
INSTALLDIR=$(cd $3 && pwd)
LLVMCONFIG=$4
shift 4

rm -rf $RELBUILDDIR
mkdir -p $RELBUILDDIR
BUILDDIR=$(cd $RELBUILDDIR && pwd)

# GITREV=$(cd $SRCDIR && git rev-parse --short HEAD)

pushd $BUILDDIR > /dev/null

cmake $SRCDIR/src -DCMAKE_BUILD_TYPE=debug -DCMAKE_INSTALL_PREFIX=$INSTALLDIR -DLLVM=ON -DLLVM_DIR=`$LLVMCONFIG --cmakedir` $@
make -j16
make install
popd

mkdir -p $INSTALLDIR/include/util
cp $SRCDIR/src/util/buffer.h $INSTALLDIR/include/util/

# ninja install
# rm -f $HOME/opt/lean4
# ln -s $HOME/opt/lean4-$GITREV/ $HOME/opt/lean4
