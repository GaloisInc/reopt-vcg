

# Required for X86DisassemblerDecoder.h and others
# LLVM_SOURCE_ROOT ?= ${HOME}/galois/vadds/llvm-stuff/llvm
# For autogen files, mainly for regs
LLVM_BUILD_ROOT ?= ${HOME}/galois/vadds/llvm-stuff/llvm-build

LLVM_CONFIG ?= ${LLVM_BUILD_ROOT}/bin/llvm-config

LEANFILES=lean/instruction.lean 
CXXFILES=src/Metadata.cpp src/lean_support.cpp src/X86Disassembler.cpp

LEAN=${LEAN_DIR}/bin/lean
LEANC=${LEAN_DIR}/bin/leanc

all: test_decoder

test_decoder: $(patsubst %.cpp,%.o,${CXXFILES}) $(patsubst %.lean,%.o,${LEANFILES}) test/test.o
	${LEANC} `${LLVM_CONFIG} --cxxflags --ldflags --system-libs --libs x86` -o $@ $^

src/%: CXXFLAGS := -g -O3 -I src/ -I llvm-files/ `${LLVM_CONFIG} --cxxflags` -I${LEAN_DIR}/src -I${LEAN_DIR}/src/runtime -std=c++14 -fexceptions

src/%.cpp: src/Instruction.h

# %.o: %.cpp
# 	clang++ -g -O3 -c $^ -I ${LLVM_SOURCE_ROOT}/lib/Target/X86 `${LLVM_CONFIG} --cxxflags` -o $@

src/Metadata.o: src/operand_table.inc

%.cpp: %.lean
	${LEAN} --cpp=$@ $^

test/% lean/%: CXX=${LEANC}



# llvm-tablegen-support: src/main.o src/X86Disassembler.o src/Metadata.o
# 	clang++ -g -O3 $^ `${LLVM_CONFIG} --cxxflags --ldflags --system-libs --libs x86` -o $@

dump_mcinst: dump_mcinst.o
	clang++ -g -O3 $^ `${LLVM_CONFIG} --cxxflags --ldflags --system-libs --libs x86` -o $@

dump_intinst: dump_intinst.o
	clang++ -g -O3 $^ `${LLVM_CONFIG} --cxxflags --ldflags --system-libs --libs x86` -o $@
