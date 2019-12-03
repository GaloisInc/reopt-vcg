#!/bin/bash

set -e
sudo apt-add-repository 'http://archive.ubuntu.com/ubuntu bionic-updates main'
sudo apt-get update

# General purpose utilities
sudo apt-get install -y binutils

# For repo build
sudo apt install -y make cmake libgmp-dev zlib1g-dev
sudo apt install -y llvm-8
sudo apt install -y llvm-8-dev
sudo apt install -y clang-8
sudo apt install -y ninja-build
