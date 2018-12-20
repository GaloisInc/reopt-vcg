
# Lean support for decoding elf files

This lean package relies on the decodex86 package (also in this repo) and, via that,
the llvm-tablegen-support binary built in the directory of the same name.  To use:

(cd llvm-tablegen-support && make)
(cd lean && ./runelf.sh path/to/sample-binaries/tiny/test-conditional.x86_64-exe 400190 4001b3

should yield
```
$ ./runelf.sh ../../sample-binaries/tiny/test-conditional.x86_64-exe 400190 4001b3
read_one_elfmem: read 500 bytes
read_one_elfmem: read 28 bytes
Starting process
(0, (inr MOV64ri32 [( R RDX RDX 0 0 ), 6295552[4]]))
(7, (inr MOV32rm [( R RAX EAX 32 0 ), (none:(some ( R RDX RDX 0 0 )) + 1*none + 0)]))
(9, (inr TEST32rr [( R RAX EAX 32 0 ), ( R RAX EAX 32 0 )]))
(11, (inr JLE_1 [(5 + 13)[1]]))
(13, (inr ADD32ri8 [( R RAX EAX 32 0 ), ( R RAX EAX 32 0 ), 1[1]]))
(16, (inr MOV32mr [(none:(some ( R RDX RDX 0 0 )) + 1*none + 0), ( R RAX EAX 32 0 )]))
(18, (inr MOV64ri32 [( R RAX RAX 0 0 ), 60[4]]))
(25, (inr MOV64ri32 [( R RDI RDI 0 0 ), 0[4]]))
(32, (inr SYSCALL []))
(34, (inr RETQ []))
```

For comparison, here is the objdump
```
$ gobjdump -d -w  ../../sample-binaries/tiny/test-conditional.x86_64-exe
0000000000400190 <_start>:
  400190:       48 c7 c2 00 10 60 00    mov    $0x601000,%rdx
  400197:       8b 02                   mov    (%rdx),%eax
  400199:       85 c0                   test   %eax,%eax
  40019b:       7e 05                   jle    4001a2 <_start+0x12>
  40019d:       83 c0 01                add    $0x1,%eax
  4001a0:       89 02                   mov    %eax,(%rdx)
  4001a2:       48 c7 c0 3c 00 00 00    mov    $0x3c,%rax
  4001a9:       48 c7 c7 00 00 00 00    mov    $0x0,%rdi
  4001b0:       0f 05                   syscall 
  4001b2:       c3                      retq
```
