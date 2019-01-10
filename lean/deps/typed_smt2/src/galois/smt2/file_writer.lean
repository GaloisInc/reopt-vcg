import .cmd
import system.io

namespace smt2

/-- Interface for writing SMTLIB expressions to a handle or file. -/
def file_writer := reader_t io.handle io

namespace file_writer

section
local attribute [reducible] file_writer
instance : monad file_writer := by apply_instance
instance : has_monad_lift io file_writer := by apply_instance
instance : monad_reader io.handle file_writer := by apply_instance
end

#print bind

/-- Write a command to the file handle. -/
def write (c:cmd) : file_writer punit := do
  h <- read,
  monad_lift $ do
    c.write (h : io.handle),
    io.fs.put_str h "\n"

/-- Assert a term is true. -/
protected
def assert (p:term bool) : file_writer punit := write (cmd.assert p)

/-- Declare a function -/
def declare_fun (nm:symbol) (args:list sort) (res:sort) : file_writer punit :=
  write (cmd.declare_fun nm args res)

/-- Declare a constant -/
def declare_const (nm:symbol) (res:sort) : file_writer punit :=
  write (cmd.declare_const nm res)

/-- Define a function in terms of inputs -/
def define_fun (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term res)
: file_writer punit := do
  write (cmd.define_fun nm args rhs)

/-- Define a function in terms of inputs -/
def check_sat : file_writer punit := do
  write cmd.check_sat

/-- Run the file writer -/
protected
def run {α} (path:string) (m:file_writer α) : io α := do
  h ← io.mk_file_handle path io.mode.write tt,
  v ← m.run h,
  io.fs.close h,
  pure v

end file_writer

end smt2
