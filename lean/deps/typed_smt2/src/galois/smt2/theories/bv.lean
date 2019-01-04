import data.bitvec

import ..basic

namespace smt2

/-- SMTLIB bitvec sorts -/
def bv (w : ℕ) : sort := ⟨symbol.of_string "BitVec" trivial, [w]⟩

/-- Class for typings that interpret bitvectors correctly. -/
class is_bv_logic (l:logic) :=
(bv_correct : ∀(w:ℕ), l.type_of (bv w) = bitvec w)

def logic.from_bitvec (l:logic) [is_bv_logic l] {w} (v:bitvec w) : l.type_of (bv w) :=
  cast (eq.symm (is_bv_logic.bv_correct l w)) v

def term.to_bitvec {l:logic} [is_bv_logic l] {w} (x:term l (bv w)) (m:model l) : bitvec w := cast (is_bv_logic.bv_correct l w) (x.interp m)

namespace bv

section
parameters {l:logic}
parameters [c:is_bv_logic l]
include c

/- Utility function to create a bitvector term assuming a compatible logic. -/
def mk_term {w} (s:sexpr atom) (interp:model l → bitvec w) : term l (bv w) :=
{ repr := s
, interp := λm, l.from_bitvec (interp m)
}

/- Create a term from a decimal number -/
def decimal {w:ℕ} (v:bitvec w) : term l (bv w) :=
  mk_term ↑{ identifier
           . head    := symbol.of_string "bv" trivial ++ symbol.of_nat v.to_nat
           , indices := [w]
           }
          (λ_, v)


/-- Bitvector addition -/
def add {w:ℕ} (x y : term l (bv w)) : term l (bv w) :=
  mk_term (sexpr.bin_app (symbol.of_string "bvadd" trivial) x y)
          (λm, x.to_bitvec m + y.to_bitvec m)

/-- Bitvector subtraction -/
def sub {w:ℕ} (x y : term l (bv w)) : term l (bv w) :=
  mk_term (sexpr.bin_app (symbol.of_string "bvsub" trivial) x y)
          (λm, x.to_bitvec m + y.to_bitvec m)

end
end bv

end smt2
