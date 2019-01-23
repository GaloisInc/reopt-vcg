import .basic

namespace smt2

------------------------------------------------------------------------
-- kind

/- An parameter for polymorphic declarations. -/
inductive kind
| nat  : kind
| sort : kind

namespace kind

instance : decidable_eq kind := by tactic.mk_dec_eq_instance

/- Map SMTLIB kinds to their Lean interpretation -/
def interp : kind → Type 1
| kind.nat := ulift ℕ
| kind.sort := Type

end kind


------------------------------------------------------------------------
-- literal

/--
A symbol representing a Boolean name or its negation.

Used in check-sat-with
-/
inductive literal
-- Assertion named predicate is true
| is_true : symbol → literal
-- Assertion named predicate is false.
| is_false : symbol → literal

------------------------------------------------------------------------
-- string_literal

/-- Return true if each character is legal in a string lit. -/
def is_string_lit_char (c:char)
  := c.is_ascii7_printable
  ∨ c ∈ ['\t', '\n', char.of_nat 13]

def is_string_lit (b:char_buffer) : Prop :=
  ∀(i:fin b.size), is_string_lit_char (b.read i)

end smt2
