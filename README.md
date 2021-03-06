# reopt-vcg

```
$ reopt-vcg --help
Usage: reopt-vcg [--verbose] <input.json> {--export <export-dir> | --solver <solver-path>}
reopt-vcg generates verification conditions to prove that reopt generated
   LLVM is faithful to the input binary.
```

`reopt-vcg` is an _in-progress_ Lean4 prototype LLVM/x86 equivalence checker for programs optimized by [reopt](https://github.com/galoisinc/reopt).

The original Haskell implementation is located [here](https://github.com/GaloisInc/reopt/tree/aae30af22757e01bf0319f72817064f2eda54992/reopt-vcg).

The `test-programs` folder contains some examples that should currently succeed in being proven equivalent. E.g.,

```
$ cd test-programs
$ ../build/reopt-vcg test_add_diet_reopt.ann
Parsed the JSON annotation file `test_add_diet_reopt.ann` successfully!
Loading Elf file at `test_add_diet_lld.exe`...
Elf file loaded!
x86 decoder built...
Loading LLVM module at `test_add_diet_reopt.ll`
LLVM module loaded!
Running VCG for the module...
Analyzing add
  Verifying add.block_0_201320.1 @ 0x201320: machine code write at 0x201320 is in unreserved stack space.... OK
  Verifying add.block_0_201320.1 @ 0x201324: machine code write at 0x201324 is in unreserved stack space.... OK
  Verifying add.block_0_201320.1 @ 0x201328: machine code read at 0x201328 is not within stack space.... OK
  Verifying add.block_0_201320.1 @ 0x20132c: machine code write at 0x20132c is in unreserved stack space.... OK
  Verifying add.block_0_201320.1 @ 0x201330: machine code read at 0x201330 is not within stack space.... OK
  Verifying add.block_0_201320.1 @ 0x20133a: machine code read at 0x20133a is not within stack space.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: machine code read at 0x20133b is not within stack space.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: stack height at return matches init.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: return address matches entry value.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: value of rbp at return is preserved.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: value of rbx at return is preserved.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: value of r12 at return is preserved.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: value of r13 at return is preserved.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: value of r14 at return is preserved.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: value of r15 at return is preserved.... OK
  Verifying add.block_0_201320.1 @ 0x20133b: return values match... OK
Analyzing main
  Verifying main.block_0_201340.0 @ 0x201340: machine code write at 0x201340 is in unreserved stack space.... OK
  Verifying main.block_0_201340.0 @ 0x201348: machine code write at 0x201348 is in unreserved stack space.... OK
  Verifying main.block_0_201340.0 @ 0x201354: machine code write at 0x201354 is in unreserved stack space.... OK
  Verifying main.block_0_201340.0 @ 0x201354: argument matches register $rdi... OK
  Verifying main.block_0_201340.0 @ 0x201354: return address matches next instruction.... OK
  Verifying main.block_0_201340.1 @ 0x201354: jump register rip.... OK
  Verifying main.block_0_201340.1 @ 0x201354: jump precondition: (= rbx (fnstart rbx))... OK
  Verifying main.block_0_201340.1 @ 0x201354: jump precondition: (= rsp (bvsub stack_high (_ bv24 64)))... OK
  Verifying main.block_0_201340.1 @ 0x201354: jump precondition: (= rbp (bvsub stack_high (_ bv8 64)))... OK
  Verifying main.block_0_201340.1 @ 0x201354: jump precondition: (= r12 (fnstart r12))... OK
  Verifying main.block_0_201340.1 @ 0x201354: jump precondition: (= r13 (fnstart r13))... OK
  Verifying main.block_0_201340.1 @ 0x201354: jump precondition: (= r14 (fnstart r14))... OK
  Verifying main.block_0_201340.1 @ 0x201354: jump precondition: (= r15 (fnstart r15))... OK
  Verifying main.block_0_201340.1 @ 0x201354: jump precondition: (= (mcstack (bvsub stack_high (_ bv8 64)) (_ BitVec 64)) (fnstart rbp))... OK
  Verifying main.block_0_201359.0 @ 0x20135b: machine code write at 0x20135b is in unreserved stack space.... OK
  Verifying main.block_0_201359.0 @ 0x201365: machine code read at 0x201365 is not within stack space.... OK
  Verifying main.block_0_201359.0 @ 0x201366: machine code read at 0x201366 is not within stack space.... OK
  Verifying main.block_0_201359.0 @ 0x201366: stack height at return matches init.... OK
  Verifying main.block_0_201359.0 @ 0x201366: return address matches entry value.... OK
  Verifying main.block_0_201359.0 @ 0x201366: value of rbp at return is preserved.... OK
  Verifying main.block_0_201359.0 @ 0x201366: value of rbx at return is preserved.... OK
  Verifying main.block_0_201359.0 @ 0x201366: value of r12 at return is preserved.... OK
  Verifying main.block_0_201359.0 @ 0x201366: value of r13 at return is preserved.... OK
  Verifying main.block_0_201359.0 @ 0x201366: value of r14 at return is preserved.... OK
  Verifying main.block_0_201359.0 @ 0x201366: value of r15 at return is preserved.... OK
  Verifying main.block_0_201359.0 @ 0x201366: return values match... OK
Verification of all goals succeeded.
Verified 42/42 goal(s).

```

See the co-located `INSTALL.md` file in this directory for installation/build instructions. N.B., as this is a prototype and 
we are targeting the in-development version of the [Lean4 Theorem Prover](https://leanprover.github.io/), instructions/documentation
may be slightly out of date.
