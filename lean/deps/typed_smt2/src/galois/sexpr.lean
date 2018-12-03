import system.io
import galois.data.buffer


/--  Data-structure for representing s-expressions that can be -/
inductive sexpr : Type
| atom : char_buffer → sexpr
| parens : sexpr → sexpr
| append : sexpr → sexpr → sexpr

namespace sexpr

instance : has_append sexpr := { append := sexpr.append }

def of_string (c:string) : sexpr := sexpr.atom c.to_char_buffer

instance : has_coe string sexpr := { coe := of_string }

/-- Write the sexpression to the file. -/
def write (h:io.handle) : sexpr → io unit
| (atom c) := do
  io.fs.write h c
| (parens s) := do
  io.fs.write h "(".to_char_buffer,
  write s,
  io.fs.write h ")".to_char_buffer
| (append x y) := do
  write x,
  io.fs.write h " ".to_char_buffer,
  write y

local infixr  `<+>`:50 := sexpr.append

-- Create an operation applied to some argumen  ts.
def app (op:string) (args : list sexpr) : sexpr :=
  sexpr.parens (args.foldl sexpr.append op)

/-- Apply an binary operation to two sexpressions. -/
def bin_app (op:string) (x y : sexpr) : sexpr := sexpr.parens (op <+> x <+> y)

instance : decidable_eq sexpr := by tactic.mk_dec_eq_instance

end sexpr
