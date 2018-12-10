/-
This declares an s-expression datatype for generating
expressions and reasoning about their interpretation.
-/
import system.io
import galois.data.buffer


/--
Data-structure for representing s-expressions.

The internal types are strictly general than what one may ordinarily
expect of s-expressions to allow arbitrary strings to be converted into
s-expressions, and concatenating two s-expressions.

We do add a decidable_eq instance for s-expressions, but it is structural
and two s expressions may be distinct, but render to the same string.
The intent is to allow one to efficiently generate s-expressions,
do lightweight pattern matching on them, and write them to handles.
-/
inductive sexpr : Type
| atom : char_buffer → sexpr
| parens : sexpr → sexpr
-- This appends two s-expressions with a space in between.
| append : sexpr → sexpr → sexpr

namespace sexpr

instance : has_append sexpr := { append := sexpr.append }

protected
def of_string : string → sexpr := λc, sexpr.atom c.to_char_buffer

instance : has_coe string sexpr := { coe := sexpr.of_string }

protected
def of_list : list sexpr → sexpr
| [] := parens (sexpr.of_string "")
| (h::r) := parens (r.foldl sexpr.append h)

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
