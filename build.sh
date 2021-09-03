#!/bin/bash

elan_path=$(which elan)
if [ ! -x "$elan_path" ] ; then
  echo "elan not found in PATH, attempting default installation of elan..."
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y
  export PATH=$HOME/.elan/bin:$PATH
fi

if [ ! -x $(which elan) ] ; then
  echo "elan installation failed, aborting"
  exit 1
fi

elan install leanprover/lean4:nightly-2021-08-18
elan default leanprover/lean4:nightly-2021-08-18



if [[ -x "$LLVM_CONFIG" ]] ; then
  echo "Using LLVM at $($LLVM_CONFIG --bindir)"
else
  echo "could not find LLVM -- please set the LLVM_CONFIG environment variable"
  exit 1
fi

CLANG=${CLANG:-"$($LLVM_CONFIG --bindir)/clang"}

make -C . LEAN_CXX=$CLANG CXX=$CLANG LLVM_CONFIG=$LLVM_CONFIG -j4
