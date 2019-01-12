import system.io
import .file_writer
import .semantics
import .theories.bv

open smt2

/- Generte a proble mtaht asserts a constant x is equal to 3. -/
def generate_problem {m} [is_generator m ] : m unit := do
  let x := symbol.of_string "x",
  declare_const x (BitVec 32),
  assert (all_equal [bv.decimal (bitvec.of_nat 32 3), var x (BitVec 32)]),
  check_sat

/-
This will either report an error because the problem is not well-formed, or
return the property implied by the program.
-/
def mkprop : except string Prop := semantics.run_and_collect_unsat generate_problem

/- This actually generates the SMTLIB file. -/
def main : io unit := do
  smt2.file_writer.run "bar.smt2" $ do
    generate_problem
