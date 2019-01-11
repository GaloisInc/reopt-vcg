import .basic

namespace smt2

/-- An SMT command -/
structure cmd :=
(expr : sexpr atom)

namespace cmd
open sort

/-- Write command to a handle. -/
protected
def write (c:cmd) (h:io.handle) : io punit := sexpr.write h (c.expr)

/-- Construct assert command. -/
protected
def assert (p:term Bool) : cmd := ⟨sexpr.app (reserved_word.of_string "assert") [p]⟩

/-- Construct check-sat command. -/
protected
def check_sat : cmd := ⟨sexpr.parens [reserved_word.of_string "check-sat"]⟩

/-- Declare a constant -/
protected
def declare_const (nm:symbol) (res:sort) : cmd :=
  ⟨sexpr.app (reserved_word.of_string "declare-const") [nm, res]⟩

/-- Declare a function -/
protected
def declare_fun (nm:symbol) (args:list sort) (res:sort) : cmd :=
  ⟨sexpr.app (reserved_word.of_string "declare-fun") [nm, sexpr.parens (args.map sort.to_sexpr), res]⟩

/-- Map a symbol and sort pair from a function declaration to an s-expression -/
def arg_pair : symbol × sort → sexpr atom
| ⟨nm,s⟩ := sexpr.app nm [s]

/-- Define a function in terms of inputs -/
protected
def define_fun (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term res) : cmd := do
  ⟨sexpr.app (sexpr.of_string "define-fun") [ nm, sexpr.parens (args.map arg_pair), res, rhs ]⟩

end cmd

end smt2
