/-
This declares sorts, terms, and semantics for generating SMTLIB
expressions and reasoning about their interpretation.
-/
import galois.data.buffer
import galois.data.char
import galois.data.fin
import galois.data.nat
import galois.logic

import data.bitvec

import galois.sexpr

import tactic.find

namespace smt2

------------------------------------------------------------------------
-- is_printable

/-- Predicate that holds if character is considered an SMTLIB printable character. -/
def is_printable (c:char) : Prop := 0x20 ≤ c.val ∧ c.val ≠ 127

namespace is_printable
local attribute [reducible] is_printable
instance decidable_is_printable (c:char) : decidable (is_printable c) := by apply_instance
end is_printable

theorem alpha_is_printable {c:char} : c.is_alpha → is_printable c :=
begin
  unfold char.is_alpha, unfold is_printable,
  intro isa,
  cases isa;
  {
    simp [char.is_upper, char.is_lower] at isa,
    apply and.intro,
    { transitivity, tactic.swap, exact isa.left, exact dec_trivial, },
    { intro eq,
      simp [eq] at isa,
      exact  of_as_false isa trivial,
    }
  },
end

theorem digit_is_printable {c:char} : c.is_digit → is_printable c :=
begin
  unfold char.is_digit, unfold is_printable,
  intro isd,
  apply and.intro,
  { transitivity, tactic.swap, exact isd.left, exact dec_trivial, },
  { intro eq,
    simp [eq] at isd,
    exact  of_as_false isd trivial,
  },
end

------------------------------------------------------------------------
-- is_legal

/-- Legal characters are either printable characters or whitespace. -/
def is_legal (c:char) : Prop := is_printable c ∨ c ∈ ['\t', '\n', '\x0d']

namespace is_legal
local attribute [reducible] is_legal
instance is_legal_decidable (c:char) : decidable (is_legal c) := by apply_instance

end is_legal

------------------------------------------------------------------------
-- reserved_words

/--
This is the list of reserved words in SMTLIB.

TODO: Add all commands in Section 3.9
-/
def reserved_words : list string :=
  [ "BINARY"
  , "DECIMAL"
  , "HEXADECIMAL"
  , "NUMERAL"
  , "STRING"
  , "_"
  , "!"
  , "as"
  , "let"
  , "exists"
  , "forall"
  , "match"
  , "par"
  ]

def reserved_word := { s:string // s ∈ reserved_words }

instance reserved_word.repr : has_repr reserved_word := ⟨subtype.val⟩

/--
Construct a reserved word from a character buffer using the decidability of reserved word membership.
-/
def reserved_word.mk (s:string) (p:as_true (s ∈ reserved_words)) : reserved_word := ⟨s, of_as_true p⟩


/-- Reserved words as a list of character buffers. -/
def reserved_words_buffer : list char_buffer := reserved_words.map string.to_char_buffer

/-- Return true if buffer is a reserved word. -/
def is_reserved_word (b:char_buffer) : Prop :=
  b ∈ reserved_words_buffer

namespace is_reserved_word
local attribute [reducible] is_reserved_word
instance decidable : decidable_pred is_reserved_word := by apply_instance
end is_reserved_word

------------------------------------------------------------------------
-- symbol

namespace symbol

/-- Check character is allowed in a symbol. -/
def is_symbol_char (c:char) : Prop := is_legal c ∧ c ∉ ['|', '\\']

namespace is_symbol_char
local attribute [reducible] is_symbol_char
instance decidable : decidable_pred is_symbol_char := by apply_instance
end is_symbol_char

/-- A simple symbol character is a quoted symbol. -/
theorem digit_is_symbol_char {c:char}
: char.is_digit c → is_symbol_char c :=
begin
  intro h,
  unfold is_symbol_char,
  unfold is_legal,
  apply and.intro,
  exact or.inl (digit_is_printable h),
  { intro p, simp at p,
    cases p; simp only [p] at h; exact (of_as_false h trivial),
  },
end

/-- Check all characters in buffer can appear in quoted symbols. -/
def is_symbol (b:char_buffer) : Prop
  := ∀(i: fin b.size), is_symbol_char (b.read i)

namespace is_symbol
local attribute [reducible] is_symbol
instance decidable : decidable_pred is_symbol := by apply_instance
end is_symbol

end symbol

/-- This is a simple identifier that can be used in function or symbol names. -/
structure symbol :=
(to_char_buffer : char_buffer)
(valid : symbol.is_symbol to_char_buffer)

namespace symbol

instance decidable_eq : decidable_eq symbol := by tactic.mk_dec_eq_instance

protected def le (x y : symbol) : Prop := x.to_char_buffer ≤ y.to_char_buffer
instance : has_le symbol := ⟨symbol.le⟩
instance decidable_le
: Π(x y : symbol), decidable (x ≤ y)
| ⟨m,a⟩ ⟨n,b⟩ :=
begin
  simp [has_le.le, symbol.le],
  apply_instance,
end

protected def lt (x y : symbol) : Prop := x.to_char_buffer < y.to_char_buffer
instance : has_lt symbol := ⟨symbol.lt⟩
instance decidable_lt
: Π(x y : symbol), decidable (x < y)
| ⟨m,a⟩ ⟨n,b⟩ :=
begin
  simp [has_lt.lt, symbol.lt],
  apply_instance,
end

section simple_symbols

/-- Symbol characters allowed in simple symbols -/
def simple_char_symbols : list char :=
 ['~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?', '/' ]

/-- Predicate that checks if character is allowed in a simple symbol. -/
inductive is_simple_symbol_char (c:char) : Prop
| is_alpha : char.is_alpha c → is_simple_symbol_char
| is_digit : char.is_digit c → is_simple_symbol_char
| is_other : c ∈ simple_char_symbols → is_simple_symbol_char

-- Show is_simple_symbol_char is decidable.
open is_simple_symbol_char

open decidable

instance is_simple_symbol_char.decidable : decidable_pred is_simple_symbol_char
| c :=
  if f : c.is_alpha then
    is_true (is_alpha f)
  else if g : c.is_digit then
    is_true (is_digit g)
  else if h : c ∈ simple_char_symbols  then
    is_true (is_other h)
  else
    is_false begin intro p, cases p; contradiction, end

/-- A simple symbol character is a quoted symbol. -/
theorem is_simple_symbol_char.is_symbol_char {c:char}
: is_simple_symbol_char c → is_symbol_char c :=
begin
  intro h,
  cases h,
  case is_simple_symbol_char.is_alpha : h {
    unfold is_symbol_char,
    unfold is_legal,
    apply and.intro,
    exact or.inl (alpha_is_printable h),
    { intro p, simp at p,
      cases p; simp only [p] at h; exact (of_as_false h trivial),
    },
  },
  case is_simple_symbol_char.is_digit : h {
    exact digit_is_symbol_char h,
  },
  case is_simple_symbol_char.is_other : h {
    simp [simple_char_symbols] at h,
    -- Try all characters and show they are allowed.
    iterate { cases h, simp only [h], exact (of_as_true trivial), },
  },
end

/-- Return true if this is a valid simple symbol. -/
def is_simple_symbol (b:char_buffer) : Prop
  := b ≠ buffer.nil
  ∧ ¬(is_reserved_word b)
  ∧ ∀(i: fin b.size),
     let c := b.read i
      in is_simple_symbol_char c ∧ (i.val = 0 → ¬(c.is_digit))

local attribute [reducible] is_simple_symbol
instance is_simple_symbol.decidable : decidable_pred is_simple_symbol := by apply_instance

end simple_symbols

------------------------------------------------------------------------
-- repr

section repr

/-- Render a symbol as a simple symbol is possible and quoted symbol otherwise. -/
protected
def repr (s:symbol) : string :=
  if is_simple_symbol s.to_char_buffer then
    s.to_char_buffer.to_string
  else
    "|" ++ s.to_char_buffer.to_string ++ "|"

instance : has_repr symbol := ⟨symbol.repr⟩

end repr

------------------------------------------------------------------------
-- Parsing

section parsing

theorem simple_symbol_is_symbol {b:char_buffer} : is_simple_symbol b → is_symbol b := do
begin
  simp [is_simple_symbol, is_symbol],
  intros is_not_nil is_not_reserved char_pred,
  intro i,
  let p : is_simple_symbol_char (buffer.read b i) := (char_pred i).left,
  exact (is_simple_symbol_char.is_symbol_char p),
end

/--
A quoted symbol with the form "|???|" where '???' denotes
a list of legal characters '|' and '\\'.
-/
def is_quoted_symbol (b:char_buffer) : Prop
  := b.size ≥ 2
  ∧ ∀(i: fin b.size),
    if i.val = 0 ∨ i.val = b.size - 1 then
      b.read i = '|'
    else
      is_symbol_char (b.read i)

local attribute [reducible] is_quoted_symbol
instance is_quoted_symbol.decidable : decidable_pred is_quoted_symbol := by apply_instance

/- This parses the string as a symbol -/
protected
def parse (s:string) : except string symbol := do
  let b := s.to_char_buffer,
  if p:is_simple_symbol b then
    pure ⟨b, simple_symbol_is_symbol p⟩
  else if is_quoted_symbol b then (do
    let inner : char_buffer := (b.take (b.size - 1)).drop 1,
    if valid:is_symbol inner then
      pure ⟨inner, valid⟩
    else
      throw "internal symbol parsing inconsistency")
  else
    throw "Invalid symbol"

end parsing


/--
Construct a reserved word from a character buffer using the decidability of reserved word membership.
-/
def from_decidable (s:char_buffer) (p:as_true (is_symbol s)) : symbol := ⟨s, of_as_true p⟩

/-- Map an s-expression to a meta-level expression -/
protected
meta def to_expr : symbol → expr
| ⟨b, p⟩ := do
  let s : string := b.to_string,
  let r : reflected _ := `(from_decidable),
  let f : expr := (`(string.to_char_buffer) : expr).app `(s),
  ((r : expr).app f).app `(trivial)

meta instance : is_meta_string symbol :=
{ parse := symbol.parse
, to_expr := symbol.to_expr
}

/- Construct an atom from a string literal. -/
def of_string : Π(nm:string), (symbol.parse nm).is_ok → symbol
| _ p := p.value

theorem is_symbol_append {x y : char_buffer}
: is_symbol x → is_symbol y → is_symbol (x ++ y) :=
begin

  unfold is_symbol,
  intros p q i,
  simp only [buffer.read_append],
  apply (dite (i.val < buffer.size x)),
  {
    intro i_lt,
    simp [i_lt],
    exact (p _),
  },
  {
    intro i_ge,
    simp [i_ge],
    exact (q _),
  }
end

protected def append : symbol → symbol → symbol
| ⟨x,p⟩ ⟨y,q⟩ := ⟨x ++ y, is_symbol_append p q⟩

instance : has_append symbol := ⟨symbol.append⟩

theorem is_symbol_nat (v : ℕ) : is_symbol (string.to_char_buffer (repr v)) :=
begin
  unfold is_symbol,

  intro i_fin,
  cases i_fin with i i_lt,
  simp only [buffer.read_to_nth_le],

  simp only [repr, has_repr.repr, nat.repr],
  simp only [buffer.to_char_buffer_as_string],
  simp only [buffer.to_list_to_buffer],

  simp only [list.nth_le_reverse_simp],
  simp only [list.nth_le_map'],

  apply digit_is_symbol_char,
  apply char.digit_char_is_digit,
  exact (nat.nth_to_digits_is_lt (of_as_true trivial) _),
end

/- Construct an atom from a string literal. -/
def of_nat (v : ℕ) : symbol := ⟨string.to_char_buffer (repr v), is_symbol_nat v⟩

def of_prefixed_nat (pre:string) (p : (symbol.parse pre).is_ok) (v : ℕ) : symbol :=
  of_string pre p ++ of_nat v

end symbol

------------------------------------------------------------------------
-- atom

/- A atomic expression within an SMTLIB s-expression. -/
inductive atom
| reserved_word (b:char_buffer) : is_reserved_word b → atom
| symbol : symbol → atom
| numeral : ℕ → atom

namespace atom

protected
def repr : atom → string
| (reserved_word b _) := b.to_string
| (symbol s)   := s.repr
| (numeral s)  := s.repr

protected
def to_char_buffer : atom → char_buffer
| (reserved_word b _) := b
| (symbol s)  := s.repr.to_char_buffer
| (numeral s) := s.repr.to_char_buffer

protected
def read {m} [char_reader string m] (read_count:ℕ) : m atom := do
  mc ← char_reader.peek_char,
  match mc with
  | option.none := throw "Dog Unexpected end of stream."
  | option.some '|' := do
    char_reader.consume_char,
    b ← char_reader.read_while symbol.is_symbol_char read_count,
    last_char ← char_reader.read_char,
    (when (last_char ≠ '|') $
      throw ("Unexpected character " ++ repr last_char ++ "in quoted symbol.")),
    if valid:symbol.is_symbol b then
      pure (symbol ⟨b, valid⟩)
    else
      throw $ "Invalid symbol " ++ repr b
  | option.some c :=
    if c.is_digit then (do
      b ← char_reader.read_while char.is_digit read_count,
      pure (numeral b.to_string.to_nat))
    else if symbol.is_simple_symbol_char c then (do
      -- Read symbol characters
      b ← char_reader.read_while symbol.is_simple_symbol_char read_count,
      if is_res:is_reserved_word b then
        pure (reserved_word b is_res)
      else if valid:symbol.is_simple_symbol b then
        pure (symbol ⟨b, symbol.simple_symbol_is_symbol valid⟩)
      else
        throw $ "Invalid symbol " ++ repr b)
    else
      throw $ "Unexpected character " ++ repr c
  end

instance : sexpr.is_atom atom :=
{ to_char_buffer := atom.to_char_buffer
, read := @atom.read
}

/-
protected
meta def to_expr : atom → expr
| (symbol s) := `(symbol).to_expr.app s.to_expr
| (numeral n) := `(numeral).to_expr.app (reflect n).to_expr


meta instance has_to_expr_atom : has_to_expr atom := ⟨atom.to_expr⟩
-/

/- Construct an atom from a string literal. -/
def of_string : Π(nm:string), (char_reader.read_from_string nm (@atom.read _ _ nm.length)).is_ok → atom
| _ p := p.value

instance : has_coe atom (sexpr atom) := ⟨sexpr.atom⟩

end atom

namespace symbol

/-- Construct an atom from an s-expression. -/
def to_sexpr (s:symbol) : sexpr atom := sexpr.atom (atom.symbol s)

instance : has_coe symbol (sexpr atom) := ⟨to_sexpr⟩

end symbol

------------------------------------------------------------------------
-- identifier

namespace identifier

/- An argument to an identifier. -/
inductive index
| numeral : ℕ → index
| symbol : symbol → index

namespace index

instance : decidable_eq index := by tactic.mk_dec_eq_instance

protected def to_atom : index → atom
| (numeral n) := atom.numeral n
| (symbol s)  := atom.symbol s

protected def to_sexpr (i:index) : sexpr atom := sexpr.atom i.to_atom

end index

instance coe_nat_to_index : has_coe ℕ index := ⟨index.numeral⟩
instance coe_symbol_to_index : has_coe symbol index := ⟨index.symbol⟩

end identifier

/- An identifier in SMTLIB possibly with a list of indices as arguments. -/
structure identifier :=
(head : symbol)
(indices : list identifier.index)

namespace identifier

instance : decidable_eq identifier := by tactic.mk_dec_eq_instance

protected
def to_sexpr : identifier → sexpr atom
| ⟨s, []⟩ := s.to_sexpr
| ⟨s, l⟩  := sexpr.parens (sexpr.of_string "_" trivial :: s :: (index.to_sexpr <$> l))

instance : has_coe identifier (sexpr atom) := ⟨identifier.to_sexpr⟩

end identifier

------------------------------------------------------------------------
-- sort

/-- A type for terms in SMTLIB -/
def sort : Type := identifier

namespace sort
instance : decidable_eq sort := by { unfold sort, apply_instance }

protected
def to_sexpr : sort → sexpr atom := identifier.to_sexpr

instance sort_is_sexpr : has_coe sort (sexpr atom) := ⟨sort.to_sexpr⟩

end sort

/-- Denotes Booleans -/
def bool : sort := ⟨symbol.of_string "bool" trivial, []⟩

------------------------------------------------------------------------
-- inhabited_type

/-- A type with a default value in that type. -/
structure inhabited_type :=
(type : Type)
(value : type)

namespace inhabited_type

def bool : inhabited_type := { type := Prop, value := true }

/-- A type with natural numbers that can be used for uninterpreted values. -/
def uninterpreted : inhabited_type := { type := ℕ, value := 0 }

end inhabited_type

------------------------------------------------------------------------
-- logic

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
(interpretation : sort → inhabited_type)
(bool_correct : (interpretation bool).type = Prop)

namespace logic

--- Return the type associated with the given sort or Prop if not defined
def type_of (l:logic) (s:sort) : Type := (l.interpretation s).type

-- Assert proposition is assigned to Booleans
--def prop_is_bool_type (l:logic) : l.type_of bool = inhabited_type.bool := l.bool_correct

/-- Coercision from prop to l.type_of bool -/
def of_prop (l:logic) (x:Prop) : l.type_of bool := cast (eq.symm l.bool_correct) x

/-- Coercision from prop to l.type_of bool -/
def to_prop (l:logic) (x:l.type_of bool) : Prop := cast l.bool_correct x

/-- @fun_type args res@ dReturn the type assigned to functions. -/
def fun_domain (l:logic) : list sort → sort → Type
| [] res := l.type_of res
| (h::r) s := l.type_of h → fun_domain r s

--- Return the type associated with the given sort or Prop if not defined
def value_of (l:logic) (s:sort) : l.type_of s := (l.interpretation s).value

--- Default value for a function
def fun_default_value (l:logic) : Π(args:list sort) (res:sort), l.fun_domain args res
| [] res := l.value_of res
| (h::r) tp := λ(x : l.type_of h), fun_default_value r tp

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

namespace model

section
parameter {l:logic}

/-- Bind a function to symbol name in the module. -/
def bind (ctx:model l)  (nm:symbol) {args: list sort} {r:sort} (v:l.fun_domain args r) : model l :=
  ctx.insert nm ⟨args, r, v⟩

/-- Bind a constant to a symbol name in the module. -/
def bind_const (ctx:model l) (nm:symbol) {r:sort} (v:l.type_of r) : model l :=
  @bind ctx nm [] r v
end
end model

------------------------------------------------------------------------
-- evaluator

namespace evaluator

/-- Errors thrown during evaluation. -/
inductive error
| var_undefined (nm:symbol) : error
| incorrect_var_result_sort (nm:symbol) {defined read:sort} (ineq:defined ≠ read) : error
| incorrect_var_arg_sorts (nm:symbol) {defined read : list sort} (ineq:defined ≠ read) : error

end evaluator


def evaluator := except evaluator.error

namespace evaluator
local attribute [reducible] evaluator
instance : monad evaluator := by apply_instance
instance : monad_except error evaluator := by apply_instance

/-
instance (l:logic) : monad_reader (model l) (evaluator l) := by apply_instance
protected
def run {l} {α} (m:evaluator l α) (mdl:model l) : except evaluator.error α := m.run mdl
-/

end evaluator

namespace model

/-- Return the value associated with a symbol, or a default value if not defined. -/
def symbol_value {l:logic} (m:model l) (nm:symbol) (args:list sort) (res:sort)
: evaluator (l.fun_domain args res) :=
  match rbmap.find m nm with
  | option.none := throw (evaluator.error.var_undefined nm)
  | option.some ⟨nm_args, nm_res, nm_val⟩ :=
    if arg_eq : nm_args = args then
      if res_eq : nm_res = res then
        pure (eq.rec (eq.rec nm_val arg_eq) res_eq)
      else
        throw (evaluator.error.incorrect_var_result_sort nm res_eq)
     else
        throw (evaluator.error.incorrect_var_arg_sorts nm arg_eq)
  end

end model

------------------------------------------------------------------------
-- term

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
structure term (l:logic) (s : sort) :=
(repr : sexpr atom)
(interp : model l → l.type_of s)

namespace model

/-- @mdl.fun_value args rhs@ returns the value associated with a
function that takes the given  arguments and returns the value denoted by @rhs@.
-/
def fun_value {l:logic}
: Π(mdl:model l) (args : list (symbol × sort)) {res : sort} (rhs : term l res),
   l.fun_domain (args.map prod.snd) res
| mdl [] res rhs := rhs.interp mdl
| mdl (⟨nm,s⟩::args) res rhs := (λ(x:l.type_of s), fun_value (mdl.bind_const nm x) args rhs)

end model


namespace term


instance (l:logic) (s:sort) : has_coe (term l s) (sexpr atom) := ⟨term.repr⟩

end term

/-- Create a term from a  symbol and sort -/
def var {l:logic} (nm : symbol) (s:sort) : term l s :=
{ repr := nm.to_sexpr
, interp := λ(m:model l),
   match m.symbol_value nm [] s with
   | (except.ok r) := r
   | (except.error e) := l.value_of s
   end
}

/-- Generate term that two terms are equal. -/
protected
def eq {l:logic} {s:sort} (x y : term l s) : term l bool :=
{ repr := sexpr.bin_app (sexpr.of_string "=" trivial) x.repr y.repr
, interp := λmdl, l.of_prop (x.interp == y.interp)
}


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

------------------------------------------------------------------------
-- string_literal

/-- Return true if each character is legal in a string lit. -/
def is_string_lit_char (c:char)
  := c.is_ascii7_printable
  ∨ c ∈ ['\t', '\n', char.of_nat 13]

def is_string_lit (b:char_buffer) : Prop :=
  ∀(i:fin b.size), is_string_lit_char (b.read i)

end smt2
