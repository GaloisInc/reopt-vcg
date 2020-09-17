
# http://make.mad-scientist.net/papers/advanced-auto-dependency-generation/#tldr

# make V=1 will print verbosely

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

BUILDDIR    ?= build

# This is ugly, as it as the side effect of creating the build
# directory if it doesn't exist, but doing it here (as oppposeed to as
# a side-effect of e.g. dependency construction) means we don't have
# to rely on laziness
#
# We need this to be absolute as lean (currently) requires that you
# change directory to genereate the .c files, so LEAN_PATH etc. need
# to be absolute
# ABSBUILDDIR := $(shell mkdir -p ${BUILDDIR} && cd $(BUILDDIR) && pwd)

# $(shell mkdir -p $(DEPDIR) >/dev/null)

# Names of the Lean executables if they're not explicitly
# set already defined already in the environment
LEAN ?= lean
LEANC ?= leanc

# FIXME: move to llvm-tablegen-support submake
# LLVM_BUILD_ROOT ?= ${HOME}/galois/vadds/llvm-stuff/llvm-build
# LLVM_CONFIG = ${LLVM_BUILD_ROOT}/bin/llvm-config
LLVM_CONFIG ?= llvm-config
LLVM_INCLUDE = $(shell $(LLVM_CONFIG) --includedir)

# Up one directory from the executable we should be able to find
# the `lib` directory with Lean files in it
LEANDIR := ${realpath ${dir ${shell which ${LEAN}}}/..}

# Determine the root directory for the source files (e.g., `.../reopt-vcg/lean4`)

makefile-directory = $(abspath $(dir $(realpath $(lastword $(MAKEFILE_LIST)))))

SRCROOT := $(call makefile-directory)

include scripts/Makefile.include

# TARGET := $(BUILDDIR)/sim $(BUILDDIR)/test-sym $(BUILDDIR)/driver $(BUILDDIR)/reopt-vcg $(BUILDDIR)/reopt-vcg-unit-test

# make sure this is the first target
.PHONY: all realall
all: realall

# Libraries
include deps/galois_stdlib/Makefile.include
include deps/smtlib/Makefile.include
include deps/lean-llvm/Makefile.include
include deps/llvm-tablegen-support/Makefile.include
include deps/x86_semantics/Makefile.include
include deps/reopt_vcg/Makefile.include
include tests/unit-tests/Makefile.include


# all the output directories we need
build-dirs = $(sort $(foreach ld,$(1),$(dir $(ld))))

# For every Lean file `Foo.lean` there should be a `Foo.d` with an entry
# `Foo.c Foo.olean: DEPENDENCY1.olean ... DEPENDENCYN.olean` describing the
# N files that lean file depends on
DEPFILES = $(addprefix $(DEPDIR)/,$(LEANFILES:.lean=.d) $(APPLEANFILES:.lean=.d))
DEPDIRS  = $(call build-dirs,$(DEPFILES)) 

OLEANFILES = $(addprefix $(OLEANDIR)/,$(LEANFILES:.lean=.olean) $(APPLEANFILES:.lean=.d))
OLEANDIRS  = $(call build-dirs,$(OLEANFILES))

CXXFLAGS += -fPIC -ggdb3
CFLAGS   += -fPIC -ggdb3

CLEANFILES = $(addprefix $(OBJDIR)/,$(LEANFILES:.lean=.c))
# we don't stick Main.c in CLEANFILES as we don't want them all linked in to all apps
CLEANDIRS  = $(call build-dirs,$(CLEANFILES) $(addprefix $(OBJDIR)/,$(APPLEANFILES:.lean=.c)))

EXTRAOBJFILES = $(addprefix ${EXTRAOBJDIR}/,$(patsubst %.c,%.o,$(patsubst %.cpp,%.o,$(EXTRACFILES))))
EXTRAOBJDIRS  = $(call build-dirs,$(EXTRAOBJFILES))

# Applications

include app/Makefile.include
include tests/unit-tests/app/Makefile.include
# include simulator/Makefile.include
# include test-symbolic/Makefile.include

export LEAN_PATH
$(shell echo "#!/bin/bash" > set_LEAN_PATH.sh)
$(shell echo "export LEAN_PATH=${LEAN_PATH}" >> set_LEAN_PATH.sh)

realall: $(TARGETS)

depend: ${DEPFILES}

RANLIB := ranlib

# This is a hack to get around leanc not taking .o files.  We create a
# library with all the .o files, and then use -l
$(EXTRAOBJDIR)/libextraobjs.a: $(EXTRAOBJFILES)
	$(call cmd,AR)

# $(BUILDDIR)/sim : ${CLEANFILES} ${EXTRAOBJFILES} build/simulator/Main.cpp
# 	${LEANC} ${CXXFLAGS} `${LLVM_CONFIG} --cxxflags` -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^ `${LLVM_CONFIG} --ldflags --system-libs --libs x86 asmparser` -lstdc++ -lm

# $(BINDIR)/test-sym : ${CLEANFILES} ${EXTRAOBJFILES} build/test-symbolic/Main.cpp
# 	${LEANC} ${CXXFLAGS} `${LLVM_CONFIG} --cxxflags` -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^ `${LLVM_CONFIG} --ldflags --system-libs --libs x86 asmparser` -lstdc++ -lm

# $(BUILDDIR)/driver: ${CLEANFILES} ${EXTRAOBJFILES} build/deps/lean-llvm/src/Driver.cpp
# 	${LEANC} ${CXXFLAGS} `${LLVM_CONFIG} --cxxflags` -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^ `${LLVM_CONFIG} --ldflags --system-libs --libs x86 asmparser` -lstdc++ -lm

# $(BUILDDIR)/reopt-vcg-unit-test : ${CLEANFILES} ${EXTRAOBJFILES} build/tests/unit-tests/Main.cpp
# 	${LEANC} ${CXXFLAGS} `${LLVM_CONFIG} --cxxflags` -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^ `${LLVM_CONFIG} --ldflags --system-libs --libs x86 asmparser` -lstdc++ -lm

${OLEANDIRS} ${CLEANDIRS} ${DEPDIRS} ${EXTRAOBJDIRS} ${BINDIR}:
	$(call cmd,MKDIR)

$(DEPDIR)/%.d: %.lean | ${OLEANDIRS} $(DEPDIRS)
	$(call cmd,MAKEDEPEND)


# could do this when making the olean
$(OBJDIR)/%.c $(OLEANDIR)/%.olean: %.lean | ${OLEANDIRS} $(CLEANDIRS)
	$(call cmd,LEAN)

# mv $(BUILDDIR)/$*.cpp.tmp $(BUILDDIR)/$*.cpp

# | ${EXTRAOBJDIRS}
$(EXTRAOBJDIR)/%.o: %.cpp | ${EXTRAOBJDIRS}
	$(call cmd,CXX)

$(EXTRAOBJDIR)/deps/galois_stdlib/src/Galois/Init/%: CXXFLAGS += -I${LEANDIR}/include -std=c++14

$(EXTRAOBJDIR)/deps/llvm-tablegen-support/src/%: CXXFLAGS += -g -O3 -I deps/llvm-tablegen-support/src/ -I deps/llvm-tablegen-support/llvm-files/ `${LLVM_CONFIG} --cflags` -I${LEANDIR}/include/ -I${LEANDIR}/include/runtime -std=c++14 -fexceptions

$(EXTRAOBJDIR)/deps/lean-llvm/src/%: CXXFLAGS += -g -O3 `${LLVM_CONFIG} --cxxflags` -I ${LEANDIR}/include/ -std=c++14 -fexceptions

clean:
	rm -f ${DEPFILES} ${OLEANFILES}

include ${DEPFILES}
