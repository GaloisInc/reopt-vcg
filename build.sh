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



if [[ -x "$LLVM_CONFIG" && $($LLVM_CONFIG --version) == 10.0.* ]] ; then
  LLVM_CONFIG_10=$LLVM_CONFIG
elif [[ -x $(which llvm-config) && $($(which llvm-config) --version) == 10.0.* ]] ; then
  LLVM_CONFIG_10=$(which llvm-config)
elif [[ -x $(which llvm-config-10) && $($(which llvm-config-10) --version) == 10.0.* ]] ; then
  LLVM_CONFIG_10=$(which llvm-config-10)
else
  echo "could not find LLVM 10.0.* -- please update LLVM_CONFIG environment variable"
  exit 1
fi

CLANG=${CLANG:-"$($LLVM_CONFIG_10 --bindir)/clang"}

make -C . LEAN_CXX=$CLANG CXX=$CLANG LLVM_CONFIG=$LLVM_CONFIG_10 -j4
