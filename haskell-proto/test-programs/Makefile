all : test_add_diet.exe test_fib_diet.exe test_add_glibc.exe test_add.bc test_fib.bc

# This builds a test case with glibc.
test_%_diet.exe : diet/start.o diet/libc.a test_%.o
	ld.lld -static -o $@ $+

# This builds with glibc libraries in case we want an alternate.
test_%_glibc.exe : glibc/libgcc_eh.a glibc/libgcc.a glibc/placeholder_initfini.o glibc/libc.a glibc/crt1.o test_%.o
	ld.lld -static -o $@ $+

# Create disassembly from exe
%.dis : %.exe
	llvm-objdump -d $< > $@

%.ll : %.bc
	llvm-dis -o $@ $<

%.bc : %.c
	clang --target=x86_64-pc-none-elf -emit-llvm -o $@ -c $<

%.o : %.c
	clang --target=x86_64-pc-none-elf -o $@ -c $<

clean :
	rm -rf *.dis *.o *.ll

# Deletes executables even though they are checked into repo.
all-clean : clean
	rm -rf *.exe test_add.bc test_fib.bc

.PHONY : all-clean clean all

.PRECIOUS : %.o %.bc
