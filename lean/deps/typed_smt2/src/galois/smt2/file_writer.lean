import .cmd

namespace smt2

/-- Interface for writing SMTLIB expressions to a handle or file. -/
def file_writer (l:logic) := reader_t io.handle io

namespace file_writer

instance (l:logic) : monad (file_writer l) := by { unfold file_writer, apply_instance }
instance (l:logic) : has_monad_lift io (file_writer l) := by { unfold file_writer, apply_instance }
instance (l:logic) : monad_reader io.handle (file_writer l) := by { unfold file_writer, apply_instance }

/-- Write a command to the file handle. -/
def write {l:logic} (c:cmd) : file_writer l punit := do
  h ← read,
  monad_lift $ do
    c.write h,
    io.fs.put_str h "\n"

/-- Assert a term is true. -/
protected
def assert {l:logic} (p:term l bool) : file_writer l punit := write (cmd.assert p)

/-- Declare a function -/
def declare_fun {l:logic} (nm:symbol) (args:list sort) (res:sort) : file_writer l punit :=
  write (cmd.declare_fun nm args res)

/-- Declare a constant -/
def declare_const {l:logic} (nm:symbol) (res:sort) : file_writer l punit :=
  write (cmd.declare_const nm res)

/-- Define a function in terms of inputs -/
def define_fun {l:logic} (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term l res)
: file_writer l punit := do
  write (cmd.define_fun nm args rhs)

/-- Define a function in terms of inputs -/
def check_sat{l:logic}  : file_writer l punit := do
  write cmd.check_sat

/-- Run the file writer -/
protected
def run {α} (l:logic) (path:string) (m:file_writer l α) : io α := do
  h ← io.mk_file_handle path io.mode.write tt,
  v ← m.run h,
  io.fs.close h,
  pure v

end file_writer

end smt2
