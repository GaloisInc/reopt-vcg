#!/bin/bash
set -e

if [ $# -lt 3 ];
then
    echo "Usage: build-lean4.sh srcdir builddir installdir"
    exit 1
fi   

SRCDIR=$(cd $1 && pwd)
RELBUILDDIR=$2
mkdir -p $3
INSTALLDIR=$(cd $3 && pwd)

rm -rf $RELBUILDDIR
mkdir -p $RELBUILDDIR
BUILDDIR=$(cd $RELBUILDDIR && pwd)

# GITREV=$(cd $SRCDIR && git rev-parse --short HEAD)

pushd $BUILDDIR > /dev/null

cmake $SRCDIR/src -G Ninja -DCMAKE_BUILD_TYPE=debug -DCMAKE_INSTALL_PREFIX=$INSTALLDIR             
ninja
ninja install
popd
# ninja install
# rm -f $HOME/opt/lean4
# ln -s $HOME/opt/lean4-$GITREV/ $HOME/opt/lean4
