/-
This declares sorts, terms, and semantics for generating SMTLIB
expressions and reasoning about their interpretation.
-/
import galois.sexpr

namespace smt2

/-- This represents either function or sort symbol names. -/
def symbol := string

/-- Convert a symbol to an s-expression; this is currently unchecked. -/
protected
def symbol.to_sexpr (s:symbol) : sexpr := sexpr.mk_atom ⟨s.to_char_buffer⟩

namespace symbol

/--
Return true if this symbol is a legal name.

TODO: Fix this to ensure symbol is not a reserved word, and characters are valid.
-/
def is_valid (nm:symbol) : bool := tt

instance : has_lt symbol :=
begin
  unfold symbol,
  apply_instance
end

end symbol

/-- A type for terms in SMTLIB -/
def sort : Type := sexpr

instance : decidable_eq sort := by { unfold sort, apply_instance }

/-- Denotes Booleans -/
def bool : sort := (by coerce "bool" sexpr)

/-- A type with a default value in that type. -/
structure inhabited_type :=
(type : Type)
(value : type)

/-- A type with natural numbers that can be used for uninterpreted values. -/
def inhabited_type.uninterpreted : inhabited_type := { type := ℕ, value := 0 }

/--
This defines an interpretation of sorts.

It maps each sort to an inhabited type, and the mapping for bool must
be Prop.

As there are an unbounded number of sorts, implementations should map
the ones they recognize to the appropriate type, then map the others
to `inhabited_type.uninterpreted` to represent uninterpreted types.

We use a function rather than finite map to deal with polymorphic
types such as bitvectors.
-/
structure logic :=
(eval : sort → inhabited_type)
(bool_eqn : (eval bool).type = Prop)

namespace logic

/-- Return the type associated with the given sort or Prop if not defined -/
def type_of (l:logic) (s:sort) : Type := (l.eval s).type

/-- Assert proposition is assigned to Booleans -/
def prop_is_bool_type (l:logic) : l.type_of bool = Prop := l.bool_eqn

/-- Return the type associated with the given sort or Prop if not defined -/
def value_of (l:logic) (s:sort) : l.type_of s := (l.eval s).value

/-- @fun_type args res@ dReturn the type assigned to functions. -/
def fun_domain (l:logic) : list sort → sort → Type
| [] res := l.type_of res
| (h::r) tp := l.type_of h → fun_domain r tp

/-- Default value for a function -/
def fun_default_value (l:logic) : Π(args:list sort) (res:sort), l.fun_domain args res
| [] res := l.value_of res
| (h::r) tp := λ(x : l.type_of h), fun_default_value r tp

/-- Coercision from prop to l.type_of bool -/
instance bool_coe (l:logic) : has_coe Prop (l.type_of bool) :=
{ coe := λ(x:Prop), eq.rec x l.prop_is_bool_type.symm }

end logic

------------------------------------------------------------------------
-- Model

/--
Provides a valuation of symbols in a SMT formula.  This is parameterized by a logic, which
defines how SMTLIB sorts should be mapped to Lean types.

This maps symbols (which could be functions) to their type information and a valuation with
the write domain according to the logic.
-/
def model (l:logic) : Type := rbmap symbol (Σ(args:list sort) (s:sort), l.fun_domain args s)

instance (l:logic) : has_emptyc (model l) :=
{ emptyc := mk_rbmap _ _ }

/--
A term in SMTLIB representation.

Our term represnetation is extensible so that one can easily construct
terms with arbitrary sexpression respresentations and interpretations.

This is designed to make it easy to introduce new theories without
changing the core of how the language works, but has the risk that one
can give an incorrect interpretation to an expression.

We recommend users only construct terms manually if they must, and
otherwise use existing definitions.
-/
structure term (s : sort) :=
(repr : sexpr)
(interp : Π{l:logic}, model l → l.type_of s)

namespace model

section
parameter {l:logic}

/-- Bind a function to symbol name in the module. -/
def bind (ctx:model l)  (nm:symbol) {args: list sort} {r:sort} (v:l.fun_domain args r) : model l :=
  ctx.insert nm ⟨args, r, v⟩

/-- Bind a constant to a symbol name in the module. -/
def bind_const (ctx:model l)  (nm:symbol) {r:sort} (v:l.type_of r) : model l :=
  @bind ctx nm [] r v

/-- Return the value associated with a symbol, or a default value if not defined. -/
def symbol_value (m:model l) (nm:symbol) (args:list sort) (res:sort) : l.fun_domain args res :=
  match rbmap.find m nm with
  | option.none := l.fun_default_value args res
  | option.some ⟨nm_args, nm_res, nm_val⟩ :=
    if h : nm_args = args ∧ nm_res = res then
      eq.rec (eq.rec nm_val h.left) h.right
     else
      l.fun_default_value args res
  end

/-- @mdl.fun_value args rhs@ returns the value associated with a
function that takes the given  arguments and returns the value denoted by @rhs@.
-/
def fun_value {l:logic}
: Π(mdl : model l) (args : list (symbol × sort)) {res : sort} (rhs : term res),
   l.fun_domain (args.map prod.snd) res
| mdl [] res rhs := rhs.interp mdl
| mdl (⟨nm,s⟩::args) res rhs := λ(x:l.type_of s), (mdl.bind_const nm x).fun_value args rhs

end
end model

section term

/-- Create a term from a  symbol and sort -/
def var (nm : symbol) {s:sort} : term s :=
{ repr := sexpr.mk_atom ⟨nm.to_char_buffer⟩
, interp := λ_ m, m.symbol_value nm [] s
}

/-- Generate term that two terms are equal. -/
def eq {s:sort} (x y : term s) : term bool :=
{ repr := sexpr.bin_app (by coerce "=" sexpr) x.repr y.repr
, interp := λ_ m, x.interp m = y.interp m
}

end term

------------------------------------------------------------------------
-- Additional data types

/--
A symbol representing a Boolean name or its negation.

Used in check-sat-ass
-/
inductive literal
-- Assertion named predicate is true
| is_true : symbol → literal
-- Assertion named predicate is false.
| is_false : symbol → literal

end smt2
