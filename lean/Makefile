
# http://make.mad-scientist.net/papers/advanced-auto-dependency-generation/#tldr

# DEPDIR := .d
# $(shell mkdir -p $(DEPDIR) >/dev/null)

BUILDDIR ?= build
# $(shell mkdir -p $(DEPDIR) >/dev/null)

LEANFILES := deps/galois_stdlib/src/galois/data/bitvec/basic.lean deps/galois_stdlib/src/galois/data/bitvec/default.lean deps/galois_stdlib/src/galois/init/int.lean deps/galois_stdlib/src/galois/init/io.lean deps/galois_stdlib/src/galois/init/nat.lean deps/llvm-tablegen-support/lean/decodex86/basic.lean deps/llvm-tablegen-support/lean/decodex86/default.lean deps/x86_semantics/src/x86_semantics/buffer_map.lean deps/x86_semantics/src/x86_semantics/common.lean deps/x86_semantics/src/x86_semantics/evaluator.lean deps/x86_semantics/src/x86_semantics/instructions.lean deps/x86_semantics/src/x86_semantics/machine_memory.lean elf.lean runelf.lean translate.lean deps/galois_stdlib/src/galois/category/coe1.lean

DEPENDS := ${patsubst %.lean,%.d,${LEANFILES}}
OLEAN   := ${patsubst %.lean,%.olean,${LEANFILES}}
CPPLEAN := ${patsubst %.lean,$(BUILDDIR)/%.cpp,${LEANFILES}}

SRCROOT := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
TARGET  := $(BUILDDIR)/simulator

# FIXME: move to llvm-tablegen-support submake
LLVM_BUILD_ROOT ?= ${HOME}/galois/vadds/llvm-stuff/llvm-build
LLVM_CONFIG = ${LLVM_BUILD_ROOT}/bin/llvm-config
LLVMCXXFILES = deps/llvm-tablegen-support/src/Metadata.cpp deps/llvm-tablegen-support/src/lean_support.cpp deps/llvm-tablegen-support/src/X86Disassembler.cpp

EXTRACXXFILES = deps/galois_stdlib/src/galois/init/io_runtime.cpp ${LLVMCXXFILES}

LEAN ?= lean
LEANC ?= leanc

LEANDIR := ${dir ${shell which lean}}../

MAKEDEPEND = $(LEAN) --deps $< | sed -n 's@${SRCROOT}@@p' | xargs echo "$*.olean:" > $@

# depend: ${DEPENDS}

all: $(TARGET)

$(TARGET): ${CPPLEAN} ${patsubst %.cpp,${BUILDDIR}/%.o,${EXTRACXXFILES}}
	${LEANC} `${LLVM_CONFIG} --cxxflags --ldflags --system-libs --libs x86`  ${CXXFLAGS} -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^

%.d: %.lean
	$(MAKEDEPEND)

# The olean have to be in the same directory :/
%.olean : %.lean
	$(LEAN) --make $<

# could do this when making the olean
$(BUILDDIR)/%.cpp: %.lean %.olean
	@mkdir -p $(@D)
	$(LEAN) --cpp="$@.tmp" $<
	mv $@.tmp $@

$(BUILDDIR)/%.o: %.cpp
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -o $@ -c $^

$(BUILDDIR)/deps/galois_stdlib/src/galois/init/%: CXXFLAGS += -I${LEANDIR}/include  -std=c++14

$(BUILDDIR)/deps/llvm-tablegen-support/src/%: CXXFLAGS := -g -O3 -I deps/llvm-tablegen-support/src/ -I deps/llvm-tablegen-support/llvm-files/ `${LLVM_CONFIG} --cxxflags` -I${LEAN_DIR}/src -I${LEAN_DIR}/src/runtime -std=c++14 -fexceptions

# %.olean %.cpp : %.lean %.d
# 	@mkdir -p $(@D);
#         @$(LEAN) --deps $< > $*.Td; \
#           cp $*.Td $*.d; \
#           sed -e 's/#.*//' -e 's/^[^:]*: *//' -e 's/ *\\$$//' \
#               -e '/^$$/ d' -e 's/$$/ :/' < $*.Td >> $*.d; \
#           rm -f $*.Td
#         $(LEAN) --make --cpp="$*.cpp.tmp" $<
# # create the .cpp file atomically
#         @mv "$*.cpp.tmp" "$*.cpp"
# 	@touch $*.olean

# # %.o : %.cpp
# # %.o : %.cpp

# %.d: ;
# .PRECIOUS: %.d

# include $(wildcard $(patsubst %,%.d,$(basename $(SRCS))))
clean:
	rm -f ${DEPENDS} ${OLEAN}

include ${DEPENDS}

