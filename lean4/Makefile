
# http://make.mad-scientist.net/papers/advanced-auto-dependency-generation/#tldr

# DEPDIR := .d
# $(shell mkdir -p $(DEPDIR) >/dev/null)

SRCROOT := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
LCSRCROOT := $(shell echo ${SRCROOT} | tr A-Z a-z)

BUILDDIR ?= build
# $(shell mkdir -p $(DEPDIR) >/dev/null)

LEAN ?= lean
LEANC ?= leanc

LEANDIR := ${dir ${shell which ${LEAN}}}../

LEAN_PATH := Init=${LEANDIR}/lib/lean/Init

# This forces LEANFILES to be strict
LEANFILES := 
EXTRACXXFILES :=

# FIXME
CXXFLAGS := -isysroot /Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk -I /usr/local/include

include deps/galois_stdlib/Makefile.include
# include deps/llvm-tablegen-support/Makefile.include
include deps/llvm-mcinst-support/Makefile.include
include deps/x86_semantics/Makefile.include
include simulator/Makefile.include

#LEANFILES are absolute, we need them to be relative to the root dir for the rest to work.
LEANFILES_REL := ${patsubst ${SRCROOT}%,%,${LEANFILES}}
EXTRAOBJ      := ${patsubst ${SRCROOT}%.cpp,${BUILDDIR}/%.o,${EXTRACXXFILES}}

DEPENDS := ${patsubst %.lean,%.d,${LEANFILES_REL}}
OLEAN   := ${patsubst %.lean,%.olean,${LEANFILES_REL}}
CPPLEAN := ${patsubst %.lean,$(BUILDDIR)/%.cpp,${LEANFILES_REL}}

TARGET  := $(BUILDDIR)/sim

# FIXME: move to llvm-tablegen-support submake
# LLVM_BUILD_ROOT ?= ${HOME}/galois/vadds/llvm-stuff/llvm-build
# LLVM_CONFIG = ${LLVM_BUILD_ROOT}/bin/llvm-config
LLVM_CONFIG ?= llvm-config

CXXFLAGS += -fPIC -ggdb3

export LEAN_PATH

MAKEDEPEND = $(LEAN) --deps $< | sed 's@${LCSRCROOT}@@p' | xargs echo "$(BUILDDIR)/$*.cpp $*.olean:" > $@

# depend: ${DEPENDS}

all: $(TARGET)

$(TARGET): ${CPPLEAN} ${EXTRAOBJ}
	${LEANC} ${CXXFLAGS} `${LLVM_CONFIG} --cxxflags` -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^ `${LLVM_CONFIG} --ldflags --system-libs --libs x86` ${LDFLAGS} -lstdc++

%.d: %.lean
	$(MAKEDEPEND)

# The olean have to be in the same directory :/
# %.olean : %.lean
# 	$(LEAN) --make $<

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

$(BUILDDIR)/deps/llvm-mcinst-support/src/%: CXXFLAGS += -g -O3 `${LLVM_CONFIG} --cxxflags` -I${LEANDIR}/include/ -I${LEANDIR}/include/runtime -std=c++14 -fexceptions


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

