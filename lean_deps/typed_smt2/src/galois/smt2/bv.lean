import .basic
import data.bitvec

namespace smt2
section bv

def bv (w : ℕ) : sort := ("(_ BitVec " ++ w.repr ++ ")" : string)

/-- Class for typings that interpret bitvectors correctly. -/
class is_bv_logic (l:logic) :=
(bv_valid := ∀(w:ℕ), l.type_of (bv w) = bitvec w)

end bv

end smt2
