# reopt-vcg

This is an _in-progress_ Lean4 prototype LLVM/x86 equivalence checker for programs optimized by [reopt](https://github.com/galoisinc/reopt).

The original Haskell implementation is located [here](https://github.com/GaloisInc/reopt/tree/aae30af22757e01bf0319f72817064f2eda54992/reopt-vcg).

The `test-programs` folder contains some examples that should currently succeed in being proven equivalent.

See the co-located `INSTALL.md` file in this directory for installation/build instructions. N.B., as this is a prototype and 
we are targeting the in-development version of the [Lean4 Theorem Prover](https://leanprover.github.io/), instructions/documentation
may be slightly out of date.
