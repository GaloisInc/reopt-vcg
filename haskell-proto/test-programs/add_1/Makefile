all : add-diet.exe add-glibc.exe

# This builds the add example with diet libc.
add-diet.exe : diet/start.o diet/libc.a add.o
	ld.lld -static -o $@ $+

# This builds with glibc libraries in case we want an alternate.
add-glibc.exe : glibc/libgcc_eh.a glibc/libgcc.a glibc/placeholder_initfini.o glibc/libc.a glibc/crt1.o add.o
	ld.lld -static -o $@ $+


%.dis : %.exe
	llvm-objdump -d $< > $@

%.ll : %.bc
	llvm-dis -o $@ $<

%.bc : %.c
	clang --target=x86_64-pc-none-elf -emit-llvm -o $@ -c $<

%.o : %.c
	clang --target=x86_64-pc-none-elf -o $@ -c $<


clean :
	rm -rf *.exe *.dis add.bc add.ll add.o

.PHONY : clean all

.PRECIOUS : %.o %.bc
