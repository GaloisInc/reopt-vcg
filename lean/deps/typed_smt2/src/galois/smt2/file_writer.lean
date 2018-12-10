import .interface

namespace smt2

/-- Interface for writing SMTLIB expressions to a handle or file. -/
def file_writer := reader_t io.handle io

namespace file_writer

instance : monad file_writer := by { unfold file_writer, apply_instance }
instance : has_monad_lift io file_writer := by { unfold file_writer, apply_instance }
instance : monad_reader io.handle file_writer := by { unfold file_writer, apply_instance }

def write (s:sexpr) : file_writer punit := do
 h ← read,
  monad_lift $ sexpr.write h s

/-- Assert a term is true. -/
protected
def assert (p:term bool) : file_writer punit := do
  write (sexpr.app "assert"  [p.repr])

def symbol_is_sexpr : has_coe symbol sexpr := { coe := sexpr.of_string }

local attribute [instance] symbol_is_sexpr

/-- Declare a function -/
protected
def declare_fun (nm:symbol) (args:list sort) (res:sort) : file_writer punit :=
  write (sexpr.app "declare-fun" [nm, sexpr.of_list args, res])

/-- Declare a constant -/
protected
def declare_const (nm:symbol) (res:sort) : file_writer punit :=
  write (sexpr.app "declare-const" [nm, res])

/-- Map a symbol and sort pair from a function declaration to an s-expression -/
def arg_pair : symbol × sort → sexpr
| ⟨nm,s⟩ := sexpr.app nm [s]

/-- Define a function in terms of inputs -/
protected
def define_fun (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term res)
: file_writer punit := do
  write (sexpr.app "define-fun" [ nm, sexpr.of_list (args.map arg_pair), res, rhs.repr ])

instance : is_generator file_writer :=
{ assert := file_writer.assert
, declare_fun := file_writer.declare_fun
, declare_const := file_writer.declare_const
, define_fun := file_writer.define_fun
}

end file_writer


end smt2
