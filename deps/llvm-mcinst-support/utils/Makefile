LLVM_CONFIG ?= llvm-config

CXX := clang++
CXXFLAGS := $(shell ${LLVM_CONFIG} --cxxflags)

all: dump_mcinst


dump_mcinst: dump_mcinst.o
	clang++ -g -O3 $^ `${LLVM_CONFIG} --cxxflags --ldflags --system-libs --libs x86` -o $@
