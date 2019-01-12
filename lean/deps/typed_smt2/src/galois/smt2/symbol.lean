import galois.logic
import galois.category.except
import galois.data.fin

import galois.data.buffer

meta def exact_trivial_tac : tactic unit := `[exact trivial]

-- Defines the SMT symbol type
namespace smt2

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
  , "assert"
  , "check-sat"
  , "declare-const"
  , "declare-fun"
  , "define-fun"
  ]

--- Reserved words as a list of character buffers.
def reserved_words_buffer : list char_buffer := reserved_words.map string.to_char_buffer

structure reserved_word :=
(buffer : char_buffer)
(proof : buffer ∈ reserved_words_buffer)

--- Predicate that holds if buffer is a reserved word.
def is_reserved_word (b:char_buffer) : Prop :=
  b ∈ reserved_words_buffer

namespace is_reserved_word
local attribute [reducible] is_reserved_word
instance decidable : decidable_pred is_reserved_word := by apply_instance
end is_reserved_word

namespace reserved_word

protected def of_buffer (b:char_buffer) (p:is_reserved_word b) : reserved_word := ⟨b, p⟩

protected def repr (w:reserved_word) : string := w.buffer.to_string

instance has_repr : has_repr reserved_word := ⟨reserved_word.repr⟩

/--
Construct a reserved word from a character buffer using the decidability of reserved word membership.
-/
def of_string (s:string) (p:as_true (s ∈ reserved_words) . exact_trivial_tac) : reserved_word :=
  let q : s.to_char_buffer ∈ reserved_words_buffer :=
        begin
          simp [reserved_words_buffer],
          apply (Exists.intro s),
          simp [of_as_true p],
        end in
  ⟨s.to_char_buffer, q⟩

end reserved_word


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

/-- A symbol is used to identify function or sort names. -/
structure symbol :=
(to_char_buffer : char_buffer)
(valid : symbol.is_symbol to_char_buffer)

#print prefix smt2.symbol

namespace symbol

instance decidable_eq : decidable_eq symbol := by tactic.mk_dec_eq_instance

--- Reflexive lexicographic ordering of symbols.
protected def le (x y : symbol) : Prop := x.to_char_buffer ≤ y.to_char_buffer
instance : has_le symbol := ⟨symbol.le⟩
instance decidable_le
: Π(x y : symbol), decidable (x ≤ y)
| ⟨m,a⟩ ⟨n,b⟩ :=
begin
  simp [has_le.le, symbol.le],
  apply_instance,
end

--- Strict lexicographic ordering of symbols.
protected def lt (x y : symbol) : Prop := x.to_char_buffer < y.to_char_buffer
instance : has_lt symbol := ⟨symbol.lt⟩
instance decidable_lt
: Π(x y : symbol), decidable (x < y)
| ⟨m,a⟩ ⟨n,b⟩ :=
begin
  simp [has_lt.lt, symbol.lt],
  apply_instance,
end

/- Sizeof always returns a number greater than 0. -/
theorem sizeof_gt0 (s:symbol) : symbol.sizeof s > 0 :=
begin
  cases s,
  dsimp [symbol.sizeof],
  exact dec_trivial,
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


theorem is_quoted_symbol.size_ok {b:char_buffer} : is_quoted_symbol b → 1 ≤ b.size - 1 :=
begin
  intro is_sym,
  apply nat.le_sub_right_of_add_le,
  dsimp [nat.add_succ],
  dsimp [is_quoted_symbol] at is_sym,
  exact is_sym.left,
end

theorem is_quoted_symbol.symbol_ok {b:char_buffer} (is_sym:is_quoted_symbol b)
: is_symbol (b.slice 1 (b.size - 1) (is_quoted_symbol.size_ok is_sym)) :=
begin
  dsimp [is_symbol],
  intro i,
  cases i with i i_lt,
  simp only [buffer.read_slice],

  --simp [buffer.size_slice] at i_lt,

  have i_p_1 : 1 + i < b.size := buffer.slice_index_bound ⟨i, i_lt⟩,

  -- Introduce forall constraint
  have q := is_sym.right ⟨1 + i, i_p_1⟩,

  have pr : ¬(1 + i = 0) := by simp,

  have min_le : buffer.size b - 1 ≤ buffer.size b := by apply nat.sub_le_self,

  have sz_pos : b.size > 0 :=
    calc b.size ≥ 2 : is_sym.left
            ... > 0 : of_as_true trivial,

  have qr : ¬(1 + i= buffer.size b - 1),
  { intro q,
    simp [buffer.size_slice, min_eq_left min_le] at i_lt,
    simp only [nat.lt_sub_left_iff_add_lt, q] at i_lt,
    simp [nat.succ_add, nat.sub_succ, nat.succ_pred_eq_of_pos sz_pos, lt_irrefl] at i_lt,
    exact i_lt,
  },
  simp only [fin.val, pr, qr, false_or, if_false] at q,
  exact q,
end


local attribute [reducible] is_quoted_symbol
instance is_quoted_symbol.decidable : decidable_pred is_quoted_symbol := by apply_instance

/- This parses the string as a symbol -/
protected
def parse (s:string) : except string symbol := do
  let b := s.to_char_buffer,
  if pr:is_quoted_symbol b then
    pure ⟨ b.slice 1 (b.size - 1) (is_quoted_symbol.size_ok pr)
         , is_quoted_symbol.symbol_ok pr
         ⟩
  else if p:is_simple_symbol b then
    pure ⟨b, simple_symbol_is_symbol p⟩
  else
    throw "Invalid symbol"

/-- Check all characters in buffer can appear in quoted symbols. -/
def string_is_symbol (s:string) : Prop := symbol.is_symbol s.to_char_buffer

@[simp]
theorem string_to_char_buffer (b:char_buffer) : string.to_char_buffer (buffer.to_string b) = b :=
begin
  apply buffer.ext,
  simp [buffer.to_string],
  simp [string.to_char_buffer_as_string],
  simp [buffer.to_list_to_buffer],
  simp [buffer.to_list],
end

/- This parses the string as a symbol -/
protected
def fast_parse (s:string) : except string string := do
  let b := s.to_char_buffer,
  if pr:is_quoted_symbol b then
    pure (b.slice 1 (b.size - 1) (is_quoted_symbol.size_ok pr)).to_string
  else if p:is_simple_symbol b then
    pure b.to_string
  else
    throw "Invalid symbol"

end parsing

--def is_ok {α} {β} : except α β → Prop

axiom by_reflection (α:Prop)  : α

section tactic
open tactic

-- meta constant eval_expr (α : Type u) [reflected α] : expr → tactic α

/- Return the value given a proof the result is ok -/
def is_ok_value : Π{e:except string symbol}, except.is_ok e → string
| (except.error l) p := false.elim p
| (except.ok r) p := r.to_char_buffer.to_string

/- Construct a symbol from a string literal. -/
def of_string (nm:string) (p : (symbol.parse nm).is_ok  . exact_trivial_tac) : symbol := p.value

meta def enable_vm_tac : tactic unit := do
  opt ← get_options,
  set_options (opt.set_bool "vm_tac" tt)

meta def disable_vm_tac : tactic unit := do
  opt ← get_options,
  set_options (opt.set_bool "vm_tac" ff)

meta def use_vm_tac : tactic bool := do
  opt ← get_options,
  pure $ opt.get_bool "vm_tac" ff

/- This generate a symbol from a string using a tactic that runs in the VM. -/
meta def of_string_tac (s:string) : tactic unit := do
  disable_vm_tac,
  b <- use_vm_tac,
  if b then
    match symbol.parse s with
    | (except.error e) := fail e
    | (except.ok sym) :=
       let r : expr := sym.to_char_buffer.to_string.reflect in
       exact `(smt2.symbol.mk (string.to_char_buffer %%r) (by_reflection _))
    end
  else
    exact (expr.app (`(@of_string %%(s.reflect))) `(trivial))

end tactic

theorem is_symbol_append {x y : char_buffer}
: is_symbol x → is_symbol y → is_symbol (x ++ y) :=
begin

  unfold is_symbol,
  intros p q i,
  simp only [buffer.read_append],
  apply (dite (i.val < buffer.size x)),
  { intro i_lt,
    simp [i_lt],
    exact (p _),
  },
  { intro i_ge,
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

/- Construct a symbol from a string literal. -/
def of_nat (v : ℕ) : symbol := ⟨string.to_char_buffer (repr v), is_symbol_nat v⟩

end symbol

end smt2
