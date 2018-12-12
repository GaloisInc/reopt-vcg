import .basic
import data.bitvec

namespace smt2
section bv

def bv (w : ℕ) : sort :=
  sexpr.bin_app (by coerce "_" sexpr) (by coerce "BitVec" sexpr) (sexpr.from_nat w)

/-- Class for typings that interpret bitvectors correctly. -/
class is_bv_logic (l:logic) :=
(bv_valid := ∀(w:ℕ), l.type_of (bv w) = bitvec w)

end bv

end smt2
