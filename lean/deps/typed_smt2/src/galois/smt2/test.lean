import system.io
import .file_writer
import .theories.bv

open smt2
open smt2.file_writer

namespace smt2
namespace logic

namespace all_supported

protected
def interpretation (s:sort) : inhabited_type :=
  if s = bool then
    inhabited_type.bool
  else
    inhabited_type.uninterpreted

protected
theorem bool_correct : (all_supported.interpretation bool).type = Prop := eq.refl _


end all_supported


def all_supported : logic :=
{ interpretation := all_supported.interpretation
, bool_correct := all_supported.bool_correct
}

namespace all_supported

protected
theorem bv_correct : ∀(w:ℕ), all_supported.type_of (bv w) = bitvec w :=
begin
  admit
end

instance : is_bv_logic all_supported :=
{ bv_correct := all_supported.bv_correct
}

end all_supported

end logic
end smt2


def write_test_file : io unit := do
  smt2.file_writer.run smt2.logic.all_supported "foo.smt2" $ do
    let x := symbol.of_string "x" trivial,
    declare_const x (bv 32),
    file_writer.assert (smt2.eq (bv.decimal (bitvec.of_nat 32 3)) (var x (bv 32))),
    check_sat
