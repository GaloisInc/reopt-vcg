
# http://make.mad-scientist.net/papers/advanced-auto-dependency-generation/#tldr

# IMPORTANT:
#
# 1. Please AVOID DOUBLE SLASHES (e.g., `//`) and other seemingly
#    innocuous but unneccesary content in generated file paths;
#
# 2. Please do not leave trailing slashes on directory paths---e.g.,
#    use `foo/bar/baz` and not `foo/bar/baz/`---to help achieve (1).
#
# This Makefile and the included `Makefile.include`s must be careful
# to consistently name paths/files/etc since we _generate_ makefile
# rules/dependencies/etc based on these values which then impact the
# build. While the double slashes, dot-dots, etc may be
# ignored/removed/etc in many cases, when used as a target name a path
# with that sort of extra "noise" in it will _not_ be considered the
# same target as the same path without such seemingly innocuous noise.


# Determine the root directory for the source files (e.g., `.../reopt-vcg/lean4`)
SRCROOT := $(abspath $(dir $(realpath $(firstword $(MAKEFILE_LIST)))))

# Where do we put the build files?
BUILDDIR ?= build
# $(shell mkdir -p $(DEPDIR) >/dev/null)

# Names of the Lean executables if they're not explicitly
# set already defined already in the environment
LEAN ?= lean
LEANC ?= leanc

# Up one directory from the executable we should be able to find
# the `lib` directory with Lean files in it
LEANDIR := ${realpath ${dir ${shell which ${LEAN}}}/..}


# Set the Lean Path (i.e., the key-value pairs of Lean packages and their locations)
# to include the Init definitions from Lean
LEAN_PATH := Init=${LEANDIR}/lib/lean/Init

# This forces LEANFILES to be strict
LEANFILES := 
EXTRACXXFILES :=

TARGET := $(BUILDDIR)/sim $(BUILDDIR)/driver $(BUILDDIR)/reopt-vcg $(BUILDDIR)/reopt-vcg-unit-test

all: $(TARGET)


include app/Makefile.include
include deps/galois_stdlib/Makefile.include
include deps/lean-llvm/Makefile.include
include deps/llvm-tablegen-support/Makefile.include
include deps/smtlib/Makefile.include
include deps/x86_semantics/Makefile.include
include simulator/Makefile.include
include tests/Makefile.include


# The paths populating LEANFILES from the various above includes are absolute,
# but we need them to be relative to the root dir for the rest to work.
LEANFILES_REL := ${patsubst ${SRCROOT}/%,%,${LEANFILES}}
EXTRAOBJFILES := ${patsubst ${SRCROOT}/%.cpp,${BUILDDIR}/%.o,${EXTRACXXFILES}}

# For every Lean file `Foo.lean` there should be a `Foo.d` with an entry
# `Foo.c Foo.olean: DEPENDENCY1.olean ... DEPENDENCYN.olean` describing the
# N files that lean file depends on
DEPFILES := ${patsubst %.lean,%.d,${LEANFILES_REL}}

OLEANFILES   := ${patsubst %.lean,%.olean,${LEANFILES_REL}}
CPPLEANFILES := ${patsubst %.lean,$(BUILDDIR)/%.cpp,${LEANFILES_REL}}


# FIXME: move to llvm-tablegen-support submake
# LLVM_BUILD_ROOT ?= ${HOME}/galois/vadds/llvm-stuff/llvm-build
# LLVM_CONFIG = ${LLVM_BUILD_ROOT}/bin/llvm-config
LLVM_CONFIG ?= llvm-config
LLVM_INCLUDE = $(shell $(LLVM_CONFIG) --includedir)

CXXFLAGS += -fPIC -ggdb3

export LEAN_PATH
$(shell echo "#!/bin/bash" > set_LEAN_PATH.sh)
$(shell echo "export LEAN_PATH=${LEAN_PATH}" >> set_LEAN_PATH.sh)


MAKEDEPEND = $(LEAN) --deps $< | sed 's@${SRCROOT}/@@p' | sort -u | xargs echo "$(BUILDDIR)/$*.cpp $*.olean:" > $@


depend: ${DEPFILES}

$(BUILDDIR)/sim : ${CPPLEANFILES} ${EXTRAOBJFILES} build/simulator/Main.cpp
	${LEANC} ${CXXFLAGS} `${LLVM_CONFIG} --cxxflags` -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^ `${LLVM_CONFIG} --ldflags --system-libs --libs x86` -lstdc++ -lm

$(BUILDDIR)/driver: ${CPPLEANFILES} ${EXTRAOBJFILES} build/deps/lean-llvm/src/Driver.cpp
	${LEANC} ${CXXFLAGS} `${LLVM_CONFIG} --cxxflags` -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^ `${LLVM_CONFIG} --ldflags --system-libs --libs x86` -lstdc++ -lm

$(BUILDDIR)/reopt-vcg : ${CPPLEANFILES} ${EXTRAOBJFILES} build/app/Main.cpp
	${LEANC} ${CXXFLAGS} `${LLVM_CONFIG} --cxxflags` -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^ `${LLVM_CONFIG} --ldflags --system-libs --libs x86` -lstdc++ -lm

$(BUILDDIR)/reopt-vcg-unit-test : ${CPPLEANFILES} ${EXTRAOBJFILES} build/tests/Main.cpp
	${LEANC} ${CXXFLAGS} `${LLVM_CONFIG} --cxxflags` -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^ `${LLVM_CONFIG} --ldflags --system-libs --libs x86` -lstdc++ -lm



%.d: %.lean
	$(MAKEDEPEND)

# could do this when making the olean
$(BUILDDIR)/%.cpp %.olean: %.lean
	@mkdir -p ${dir $(BUILDDIR)/$*.cpp}
	$(LEAN) --cpp="$(BUILDDIR)/$*.cpp.tmp" --make $<
	mv $(BUILDDIR)/$*.cpp.tmp $(BUILDDIR)/$*.cpp

$(BUILDDIR)/%.o: %.cpp
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) -o $@ -c $^

$(BUILDDIR)/deps/galois_stdlib/src/Galois/Init/%: CXXFLAGS += -I${LEANDIR}/include -std=c++14

$(BUILDDIR)/deps/llvm-tablegen-support/src/%: CXXFLAGS += -g -O3 -I deps/llvm-tablegen-support/src/ -I deps/llvm-tablegen-support/llvm-files/ `${LLVM_CONFIG} --cxxflags` -I${LEANDIR}/include/ -I${LEANDIR}/include/runtime -std=c++14 -fexceptions

$(BUILDDIR)/deps/lean-llvm/src/%: CXXFLAGS += -g -O3 -I deps/llvm-tablegen-support/src/ -I deps/llvm-tablegen-support/llvm-files/ `${LLVM_CONFIG} --cxxflags` -I${LEANDIR}/include/ -I${LEANDIR}/include/runtime -std=c++14 -fexceptions



clean:
	rm -f ${DEPFILES} ${OLEANFILES}


include ${DEPFILES}
