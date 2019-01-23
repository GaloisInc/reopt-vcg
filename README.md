This repo contains a tool for proving that an LLVM program is
a refinement of an x86 program.

The primary use is to verify that a decompilation tool generates a
correct decompilation using formal verification.

We have two ongoing threads:

  * A Haskell-based prototype
  * A Lean-based implementation.

The Haskell prototype uses a large collection of existing libraries.
Once the Lean version has feature parity it will replace the Haskell
prototype.