import .interface

namespace smt2

/-- An SMT command -/
structure cmd :=
(expr : sexpr)

namespace cmd


protected
def write (c:cmd) (h:io.handle) : io punit := sexpr.write h (c.expr)

protected
def assert (p:term bool) : cmd := ⟨sexpr.app (by coerce "assert" sexpr)  [p.repr]⟩

def symbol_is_sexpr : has_coe symbol sexpr := { coe := symbol.to_sexpr }

local attribute [instance] symbol_is_sexpr

/-- Declare a function -/
protected
def declare_fun (nm:symbol) (args:list sort) (res:sort) : cmd :=
  ⟨sexpr.app (by coerce "declare-fun" sexpr) [nm, sexpr.of_list args, res]⟩

/-- Declare a constant -/
protected
def declare_const (nm:symbol) (res:sort) : cmd :=
  ⟨sexpr.app (by coerce "declare-const" sexpr) [nm, res]⟩

/-- Map a symbol and sort pair from a function declaration to an s-expression -/
def arg_pair : symbol × sort → sexpr
| ⟨nm,s⟩ := sexpr.app nm [s]

/-- Define a function in terms of inputs -/
protected
def define_fun (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term res) : cmd := do
  ⟨sexpr.app (by coerce "define-fun" sexpr) [ nm, sexpr.of_list (args.map arg_pair), res, rhs.repr ]⟩

end cmd

/-- Interface for writing SMTLIB expressions to a handle or file. -/
def file_writer := reader_t io.handle io

namespace file_writer

instance : monad file_writer := by { unfold file_writer, apply_instance }
instance : has_monad_lift io file_writer := by { unfold file_writer, apply_instance }
instance : monad_reader io.handle file_writer := by { unfold file_writer, apply_instance }

/-- Write a command to the file handle. -/
def write (c:cmd) : file_writer punit := do
  h ← read,
  monad_lift $ do
    c.write h,
    io.fs.put_str h "\n"

/-- Assert a term is true. -/
protected
def assert (p:term bool) : file_writer punit := write (cmd.assert p)

/-- Declare a function -/
protected
def declare_fun (nm:symbol) (args:list sort) (res:sort) : file_writer punit :=
  write (cmd.declare_fun nm args res)

/-- Declare a constant -/
protected
def declare_const (nm:symbol) (res:sort) : file_writer punit :=
  write (cmd.declare_const nm res)

/-- Map a symbol and sort pair from a function declaration to an s-expression -/
def arg_pair : symbol × sort → sexpr
| ⟨nm,s⟩ := sexpr.app nm.to_sexpr [s]

/-- Define a function in terms of inputs -/
protected
def define_fun (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term res)
: file_writer punit := do
  write (cmd.define_fun nm args rhs)

instance : is_generator file_writer :=
{ assert        := file_writer.assert
, declare_fun   := file_writer.declare_fun
, declare_const := file_writer.declare_const
, define_fun    := file_writer.define_fun
}

/-- Run the file writer -/
protected
def run {α} (path:string) (m:file_writer α) : io α := do
  h ← io.mk_file_handle path io.mode.write tt,
  v ← m.run h,
  io.fs.close h,
  pure v

end file_writer


end smt2
