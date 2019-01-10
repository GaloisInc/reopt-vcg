import data.bitvec

import ..basic

namespace smt2

/-- SMTLIB bitvec sorts -/
def bv (w : ℕ) : sort :=
  { name := symbol.of_string "BitVec"
  , args := [ident_arg.nat w]
  , domain := bitvec w
  , default := 0
  }

def term.bv_interp {w:ℕ} (x:term (bv w)) (m:interpretation) : bitvec w := x.interp m


def bv.to_domain {w:ℕ} (d:bitvec w) : (bv w).domain := d

namespace bv

/- Create a term from a decimal number -/
def decimal {w:ℕ} (v:bitvec w) : term (bv w) :=
{ to_sexpr := sexpr.parens [ reserved_word.of_string "_"
                           , (symbol.of_string "bv" trivial ++ symbol.of_nat v.to_nat).to_atom
                           , atom.numeral w
                           ]
, interp := λ_, v
}

/-- Bitvector addition -/
def add {w:ℕ} (x y : term (bv w)) : term (bv w) :=
{ to_sexpr := sexpr.bin_app (symbol.of_string "bvadd" trivial) x y
, interp := λm, (x.bv_interp m + y.bv_interp m : bitvec w)
}

/-- Bitvector subtraction -/
def sub {w:ℕ} (x y : term (bv w)) : term (bv w) :=
{ to_sexpr := sexpr.bin_app (symbol.of_string "bvsub" trivial) x y
, interp := λm, (x.bv_interp m - y.bv_interp m : bitvec w)
}

end bv

end smt2
