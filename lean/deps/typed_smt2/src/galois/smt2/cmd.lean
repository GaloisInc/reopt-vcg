import .basic

namespace smt2

/-- An SMT command -/
structure cmd :=
(expr : sexpr atom)

namespace cmd

/-- Write command to a handle. -/
protected
def write (c:cmd) (h:io.handle) : io punit := sexpr.write h (c.expr)

/-- Construct assert command. -/
protected
def assert {l} (p:term l bool) : cmd := ⟨sexpr.app (sexpr.of_string "assert" trivial) [p]⟩

/-- Construct check-sat command. -/
protected
def check_sat : cmd := ⟨sexpr.parens [sexpr.of_string "check-sat" trivial]⟩

/-- Declare a constant -/
protected
def declare_const (nm:symbol) (res:sort) : cmd :=
  ⟨sexpr.app (sexpr.of_string "declare-const" trivial) [nm, res]⟩

/-- Declare a function -/
protected
def declare_fun (nm:symbol) (args:list sort) (res:sort) : cmd :=
  ⟨sexpr.app (sexpr.of_string "declare-fun" trivial) [nm, sexpr.parens (args.map sort.to_sexpr), res]⟩

/-- Map a symbol and sort pair from a function declaration to an s-expression -/
def arg_pair : symbol × sort → sexpr atom
| ⟨nm,s⟩ := sexpr.app nm [s]

/-- Define a function in terms of inputs -/
protected
def define_fun {l} (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term l res) : cmd := do
  ⟨sexpr.app (sexpr.of_string "define-fun" trivial) [ nm, sexpr.parens (args.map arg_pair), res, rhs ]⟩

end cmd

end smt2
