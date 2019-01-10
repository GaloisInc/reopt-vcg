import system.io
import .file_writer
import .theories.bv

open smt2
open smt2.file_writer


def write_test_file : io unit := do
  smt2.file_writer.run "bar.smt2" $ do
    let x := symbol.of_string "x",
    declare_const x (BitVec 32),
    file_writer.assert (all_equal [bv.decimal (bitvec.of_nat 32 3), var x (BitVec 32)]),
    check_sat

--#eval write_test_file