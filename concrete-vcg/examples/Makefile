# copied from reopt/vcg-test-programs

# Use variable names for programs for distros that want to change these
# (e.g. Ubuntu)
llvm-config ?= llvm-config


ifeq (, $(shell which $(llvm-config)))
$(error "Unable to find llvm-config.  Try make llvm-config=/path/to/llvm-config")
endif

llvm-bindir := $(shell $(llvm-config) --bindir)
clang ?= $(llvm-bindir)/clang
lld ?= $(llvm-bindir)/ld.lld
llc ?= $(llvm-bindir)/llc
llvm_as ?= $(llvm-bindir)/llvm-as
llvm-objdump = $(llvm-bindir)/llvm-objdump
llvm-dis = $(llvm-bindir)/llvm-dis

cpp_flags ?=
#cpp_flags=-I/usr/include/x86_64-linux-gnu

#reopt_flags := --clang="$(clang)" --llc="$(llc)"
#reopt := $(shell which reopt)
#reopt-vcg := $(shell which reopt-vcg)


TESTS := test_fib test_sort test_add

TARGETS := $(foreach x,$(TESTS),$(x)_mindiet_lld.exe $(x).ll)

all: $(TARGETS)

mindiet_libs=mindiet/start.o mindiet/libc.a

# This builds a test program with mindiet libc and lld.
# The mv gets around a weirdness with virtualbox and lld
test_%_mindiet_lld.exe : test_%.o $(mindiet_libs)
	@$(eval TMP := $(shell mktemp))
	$(lld) -static -o ${TMP} $+
	mv ${TMP} $@

# Create disassembly from exe
%.dis : %.exe
	$(llvm-objdump) -d $< > $@

%.ll : %.bc
	$(llvm-dis) -o $@ $<

%.bc : %.c
	$(clang) $(cpp_flags) --target=x86_64-pc-none-elf -I/usr/include/x86_64-linux-gnu -emit-llvm -o $@ -c $<

%.o : %.c
	$(clang) --target=x86_64-pc-linux-elf -I/usr/include/x86_64-linux-gnu -o $@ -c $<

clean :
	rm -rf *.dis *.o *.ll
	rm -f $(TARGETS)

# Deletes executables even though they are checked into repo.
all-clean : clean
	rm -rf *.exe $(TARGETS)

.PHONY : all-clean clean all

.PRECIOUS : %.o %.bc
