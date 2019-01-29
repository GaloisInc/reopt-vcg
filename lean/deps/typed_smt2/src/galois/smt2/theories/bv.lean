import ..basic

namespace smt2

def term.bv_interp {w:ℕ} (x:term (BitVec w)) (m:interpretation) : bitvec w := x.interp m

def bv.to_domain {w:ℕ} (d:bitvec w) : (BitVec w).domain := d

namespace bv

/- Create a term from a decimal number -/
def decimal {w:ℕ} (v:bitvec w) : term (BitVec w) :=
{ to_sexpr := sexpr.parens [ reserved_word.of_string "_"
                           , (symbol.of_string "bv" trivial ++ symbol.of_nat v.to_nat).to_atom
                           , atom.numeral w
                           ]
, interp := λ_, v
}

/-- Bitvector addition -/
def add {w:ℕ} (x y : term (BitVec w)) : term (BitVec w) :=
{ to_sexpr := sexpr.bin_app (symbol.of_string "bvadd" trivial) x y
, interp := λm, (x.bv_interp m + y.bv_interp m : bitvec w)
}

/-- Bitvector subtraction -/
def sub {w:ℕ} (x y : term (BitVec w)) : term (BitVec w) :=
{ to_sexpr := sexpr.bin_app (symbol.of_string "bvsub" trivial) x y
, interp := λm, (x.bv_interp m - y.bv_interp m : bitvec w)
}

end bv

end smt2
