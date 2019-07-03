
# http://make.mad-scientist.net/papers/advanced-auto-dependency-generation/#tldr

# DEPDIR := .d
# $(shell mkdir -p $(DEPDIR) >/dev/null)

BUILDDIR ?= build
# $(shell mkdir -p $(DEPDIR) >/dev/null)

# This forces LEANFILES to be strict
LEANFILES := 
EXTRACXXFILES :=

include deps/galois_stdlib/Makefile.include
include deps/llvm-tablegen-support/Makefile.include
include deps/x86_semantics/Makefile.include
include simulator/Makefile.include

SRCROOT := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))

#LEANFILES are absolute, we need them to be relative to the root dir for the rest to work.
LEANFILES_REL := ${patsubst ${SRCROOT}%,%,${LEANFILES}}
EXTRAOBJ      := ${patsubst ${SRCROOT}%.cpp,${BUILDDIR}/%.o,${EXTRACXXFILES}}

DEPENDS := ${patsubst %.lean,%.d,${LEANFILES_REL}}
OLEAN   := ${patsubst %.lean,%.olean,${LEANFILES_REL}}
CPPLEAN := ${patsubst %.lean,$(BUILDDIR)/%.cpp,${LEANFILES_REL}}

TARGET  := $(BUILDDIR)/sim

# FIXME: move to llvm-tablegen-support submake
LLVM_BUILD_ROOT ?= ${HOME}/galois/vadds/llvm-stuff/llvm-build
LLVM_CONFIG = ${LLVM_BUILD_ROOT}/bin/llvm-config

LEAN ?= lean
LEANC ?= leanc

LEANDIR := ${dir ${shell which lean}}../

MAKEDEPEND = $(LEAN) --deps $< | sed -n 's@${SRCROOT}@@p' | xargs echo "$(BUILDDIR)/$*.cpp $*.olean:" > $@

# depend: ${DEPENDS}

all: $(TARGET)

$(TARGET): ${CPPLEAN} ${EXTRAOBJ}
	${LEANC} `${LLVM_CONFIG} --cxxflags --ldflags --system-libs --libs x86`  ${CXXFLAGS} -Wno-variadic-macros -Wno-gnu-zero-variadic-macro-arguments  -fexceptions -o $@ $^

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

