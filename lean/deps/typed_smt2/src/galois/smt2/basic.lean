/-
This declares sorts, terms, and semantics for generating SMTLIB
expressions and reasoning about their interpretation.
-/
import data.bitvec
import galois.category.except
import galois.data.buffer
import galois.data.option
import galois.logic
import galois.sexpr

import tactic.find

universes u v

inductive PropExists {α : Prop} (p : α → Prop) : Prop
| intro (w : α) (h : p w) : PropExists


namespace list

def map_with_mem {α} {β: Sort _} : Π(l:list α), (Π(x:α), x ∈ l → β) → list β
| [] f := []
| (h::r) f
  := f h (or.inl rfl)
  :: map_with_mem r (λ(x:α) (p:x ∈ r), f x (or.inr p))

/- Elements in a list have a smaller size than the list. -/
theorem mem_sizeof {α} [s : has_sizeof α] {x : α} {l : list α} (p : x ∈ l)
: sizeof x < l.sizeof :=
begin
  induction l,
  case nil {
    exact false.elim p,
  },
  case cons : h r ind {
    simp [has_mem.mem, list.mem] at p,
    simp [list.sizeof, nat.succ_add],
    apply nat.succ_le_succ,
    cases p,
    case or.inl : x_eq_h {
      simp [x_eq_h],
    },
    case or.inr : x_in_r {
      transitivity, exact le_of_lt (ind x_in_r),
      apply nat.le_add_right,
    },
  },
end

--- A decidable test for lists using a test for elements that
-- includes proof only list elements are queried.
def has_dec_eq_with_mem {α}
: Π (k l : list α) (p : Π{a : α}, a ∈ k → Π{b:α}, b ∈ l → decidable (a = b)),
    decidable (k = l)
| []      [] p    := is_true rfl
| (a::as) [] p    := is_false (λ h, list.no_confusion h)
| []      (b::bs) p := is_false (λ h, list.no_confusion h)
| (a::as) (b::bs) p :=
  let ma : a ∈ (a::as) := or.inl rfl in
  let mb : b ∈ (b::bs) := or.inl rfl in
  match p ma mb with  | is_true hab :=
    let q (x:α) (xm:x ∈ as) (y:α) (ym:y ∈ bs) :=
          p (or.inr xm) (or.inr ym) in
    match has_dec_eq_with_mem as bs q with
    | is_true habs  :=
      is_true (eq.subst hab (eq.subst habs rfl))
    | is_false nabs :=
      is_false (λ h, list.no_confusion h (λ _ habs, absurd habs nabs))
    end
  | is_false nab := is_false (λ h, list.no_confusion h (λ hab _, absurd hab nab))
  end

/-
Predicate that returns true if two lists have same length and all
 pairswise elements are equivalent.
-/
inductive holds_pairwise {α} {β} (P : α → β → Prop)
: list α -> list β -> Prop
| nil {} : holds_pairwise [] []
| cons {} {x:α} {xr : list α} {y:β} {yr:list β}
  : P x y
  → holds_pairwise xr yr
  → holds_pairwise (x::xr) (y::yr)

namespace holds_pairwise
open decidable

/- Decide the holds pairwise relation. -/
def decide_with_mem {α} {β} (r : α → β → Prop)
: Π(x:list α) (y:list β),
   (Π(a:α), a ∈ x → Pi(b:β), b ∈ y → decidable (r a b))
    → decidable (holds_pairwise r x y)
| [] [] _ := is_true nil
| [] (yh::yr) _ := is_false (by { intro p, cases p, })
| (xh::xr) [] _ := is_false (by { intro p, cases p, })
| (xh::xr) (yh::yr) p :=
  match p xh (or.inl rfl) yh (or.inl rfl) with
  | is_true ph :=
    let q := λa am b bm, p a (or.inr am) b (or.inr bm) in
    match decide_with_mem xr yr q with
    | is_true pr := is_true (cons ph pr)
    | is_false npr := is_false
      begin
        intro p,
        cases p with x yr y yr ph pr,
        exact npr pr,
      end
    end
  | is_false nph := is_false
    begin
      intro p,
      cases p with x yr y yr ph pr,
      exact nph ph,
    end
  end

end holds_pairwise

end list

/- A list whose element types are constructed from applying a function to another list. -/
inductive indexed_list {α:Type u} (f:α → Sort v) : list α → Sort (max (u+1) v)
| nil {} : indexed_list []
| cons {h:α} {r:list α} : f h → indexed_list r → indexed_list (h::r)

namespace indexed_list
section

parameter {α:Type u}
parameter {f:α → Sort v}

/- Return the nth_le element in the list. -/
def nth_le : Π{l:list α}, indexed_list f l → Π(i:ℕ) (i_lt:i < l.length), f (l.nth_le i i_lt)
| ._ nil      n     h := absurd h (nat.not_lt_zero n)
| ._ (cons a l) 0     h := a
| ._ (cons a l) (n+1) h := nth_le l n (nat.le_of_succ_le_succ h)

end
end indexed_list

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

--- Reserved words as a list of character buffers.
def reserved_words_buffer : list char_buffer := reserved_words.map string.to_char_buffer

--- Predicate that holds if buffer is a reserved word.
def is_reserved_word (b:char_buffer) : Prop :=
  b ∈ reserved_words_buffer

namespace is_reserved_word
local attribute [reducible] is_reserved_word
instance decidable : decidable_pred is_reserved_word := by apply_instance
end is_reserved_word

namespace reserved_word

protected def repr : reserved_word → string := subtype.val

instance has_repr : has_repr reserved_word := ⟨reserved_word.repr⟩

/--
Construct a reserved word from a character buffer using the decidability of reserved word membership.
-/
def of_string (s:string) (p:as_true (s ∈ reserved_words)) : reserved_word := ⟨s, of_as_true p⟩

end reserved_word

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

end parsing

#print tactic.exact_dec_trivial
-- Construct a reserved word from a character buffer using the decidability of reserved word membership.
-- def from_decidable (s:char_buffer) (p:as_true (is_symbol s)) : symbol := ⟨s, of_as_true p⟩

meta def of_string_tac : tactic unit := `[exact trivial]

/- Construct a symbol from a string literal. -/
def of_string (nm:string) (p : (symbol.parse nm).is_ok  . of_string_tac) : symbol := p.value


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
-- sort_arg

/-
This datatype represents potential arguments to sort paramters, and includes
parameters, natural number literals, and other sorts.

No requirement is made that the sort is well-formed with respect to a signature.
-/
inductive sort_arg (ctx:list kind) : Type
| nat   {} : ℕ → sort_arg
| sort  {} : symbol → list sort_arg → sort_arg
| param {} (i : fin ctx.length) : sort_arg


namespace sort_arg

------------------------------------------------------------------------
-- is_child

/- is_child c x holds if one sort_arg appears as an argument to another. -/
inductive is_child {ctx:list kind} : sort_arg ctx → sort_arg ctx → Prop
| mem : Π{x : sort_arg ctx} {nm : symbol} {args : list (sort_arg ctx)}
          (is_mem : x ∈ args),
          is_child x (sort_arg.sort nm args)

/- Prove is_child relationship is well-founded. -/
def is_child.wf {ctx:list kind} : well_founded (@is_child ctx) :=
begin
  apply well_founded.intro,
  intro z,
  apply well_founded.fix (sizeof_measure_wf (sort_arg ctx)) _ z,
  intros y rec,
  dsimp [sizeof_measure, measure, inv_image] at rec,
  apply acc.intro,
  intros x x_lt_y,
  cases y with n nm args,
  { cases x_lt_y, },
  { cases x_lt_y with a b c x_in_args,
    apply rec,
    simp [sizeof, has_sizeof.sizeof, sort_arg.sizeof, nat.succ_add ],
    transitivity, exact (list.mem_sizeof x_in_args),
    apply nat.lt_of_le_of_lt (nat.le_add_left _ nm.sizeof),
    exact (nat.succ_le_succ (nat.le_refl _)),
  },
  { cases x_lt_y, },
end

------------------------------------------------------------------------
-- fixpoint function based on is_child.

section

parameter {ctx : list kind}
parameter {C : sort_arg ctx → Sort _}
parameter (nat_eval : Π(n:ℕ), C (nat n))
parameter (sort_eval : Π(nm:symbol) (args:list (sort_arg ctx)),
               (Π(y : sort_arg ctx), y ∈ args → C y)
               → C (sort nm args))
parameter (param_eval : Π(i:fin ctx.length), C (param i))

def fix.f
  : Π (x : sort_arg ctx), (Π (y : sort_arg ctx), sort_arg.is_child y x → C y) -> C x
| (nat n) _ := nat_eval n
| (sort nm args) ind := sort_eval nm args (λy h, ind y (is_child.mem h))
| (param i) _ := param_eval i

@[elab_with_expected_type]
def fix
  : Π(x : sort_arg ctx), C x :=
  well_founded.fix is_child.wf fix.f

end

------------------------------------------------------------------------
--

/-- Convert a sort_arg to an s-expression. -/
protected
def to_sexpr : sort_arg [] → sexpr atom :=
  let num (n:ℕ) := sexpr.atom (atom.numeral n) in
  let app (nm : symbol) (args : list (sort_arg [])) rec :=
        sexpr.parens
          (sexpr.atom (atom.symbol nm) :: args.map_with_mem rec) in
  let param_eval (i:fin 0) : sexpr atom := i.elim0 in
  fix num app param_eval

section decidable
parameter {ctx : list kind}

def decidable_eq.nat (m:ℕ) : Π(y:sort_arg ctx), decidable (nat m = y)
| (nat n) :=
  if p : m = n then
    is_true (congr_arg nat p)
  else
    is_false (λh, p (sort_arg.nat.inj h))
| (sort nm args) := is_false (by contradiction)
| (param i)      := is_false (by contradiction)

def decidable_eq.app (nm : symbol) (args : list (sort_arg ctx))
        (rec : Π(y:sort_arg ctx), y ∈ args → Πz, decidable (y = z))
 : Π(y:sort_arg ctx), decidable (sort nm args = y)
 | (nat n) := is_false (by contradiction)
 | (sort ynm yargs) :=
   if pnm : nm = ynm then
     let p (xe) (xmem) (ye) (ymem : ye ∈ yargs)
          : decidable (xe = ye) := rec xe xmem ye in
     match list.has_dec_eq_with_mem args yargs p with
     | is_true pr   := is_true (eq.subst pnm (eq.subst pr rfl))
     | is_false npr := is_false (λh, npr (sort_arg.sort.inj h).right)
     end
   else
     is_false (λh, pnm (sort_arg.sort.inj h).left)
| (param i)      := is_false (by contradiction)

def decidable_eq.eval_param (i:fin ctx.length) : Π(y:sort_arg ctx), decidable (param i = y)
| (nat n) := is_false (by contradiction)
| (sort nm args) := is_false (by contradiction)
| (param j)      :=
  if p : i = j then
    is_true (congr_arg _ p)
  else
    is_false (λh, p (sort_arg.param.inj h))

protected
def has_dec_eq : decidable_eq (sort_arg ctx) :=
  fix decidable_eq.nat decidable_eq.app decidable_eq.eval_param

instance : decidable_eq (sort_arg ctx) := sort_arg.has_dec_eq

end decidable

end sort_arg

/- Symbol associated with Boolean values. -/
def symbol.bool : symbol := symbol.of_string "Bool"

------------------------------------------------------------------------
-- uncurry

/- Map list of kinds for arguments to their interpretation as a function. -/
def sort_interp (l:list kind) (r:Type 1) : Type 1 := l.foldr (λh r, h.interp → r) r

------------------------------------------------------------------------
-- sort_model

namespace sort_model

/- Information about a specific sort in the model. -/
structure info :=
(params : list kind)
(interp  : sort_interp params Type)

def bool_info : info := {params := [], interp := Prop}

end sort_model

/-- Defines the mapping from sorts to their parameters and interpretation in Lean. -/
structure sort_model :=
(map : rbmap symbol sort_model.info)
(extends_core : map.find symbol.bool = option.some sort_model.bool_info)

namespace sort_model

/- Defines the core signature, all signatures should extend this. -/
def core : sort_model :=
{ map := rbmap.from_list [⟨symbol.bool, sort_model.bool_info⟩]
, extends_core := rfl
}

/- Returns the parameters associated with the symbol if any. -/
def lookup_sort (sig:sort_model) (s:symbol) : option info := sig.map.find s

/- Restate extends_Core in terms of lookup_sort -/
@[simp]
theorem lookup_sort_bool (sig:sort_model)
: lookup_sort sig symbol.bool = option.some sort_model.bool_info := sig.extends_core



end sort_model


------------------------------------------------------------------------
-- well_formed sort_arg

namespace sort_arg

/- Predicate that indicates if a sort satisfies typing constraints. -/
inductive well_formed (mdl:sort_model) {ctx : list kind}
: sort_arg ctx → kind → Prop
| nat {} (x:ℕ) : well_formed (sort_arg.nat x) kind.nat
| sort (nm:symbol) (args:list (sort_arg ctx))
  (p : option.is_some_prop (mdl.lookup_sort nm))
  : list.holds_pairwise well_formed args p.get.params
  → well_formed (sort_arg.sort nm args) kind.sort
| param {} (i:fin ctx.length)
  : well_formed (param i) (ctx.nth_le i.val i.is_lt)

/- Introduces property implied when we know a sort_arg is a well-defined sort. -/
theorem well_formed_sort_proof {mdl:sort_model} {ctx : list kind} {nm:symbol} {args:list (sort_arg ctx)}
(p: well_formed mdl (sort nm args) kind.sort)
: PropExists
   (λ(is:option.is_some_prop (mdl.lookup_sort nm)),
    list.holds_pairwise (well_formed mdl) args is.get.params) :=
begin
  cases p with a b c p_p p_a,
  apply PropExists.intro p_p p_a,
end

/- Introduces property implied when we know a sort_arg is a well-defined sort. -/
theorem well_formed.param_proof {mdl:sort_model} {ctx : list kind} {i:fin ctx.length} {k:kind}
(p: well_formed mdl (param i) k)
: k = ctx.nth_le i.val i.is_lt :=
begin
  cases p,
  exact rfl,
end

namespace well_formed

section
parameter (mdl:sort_model)
parameter {ctx:list kind}

def decidable.nat (x:ℕ)
: Π(i:kind), decidable (@well_formed mdl ctx (sort_arg.nat x) i)
| kind.nat  := is_true (well_formed.nat x)
| kind.sort := is_false (by {intro p, cases p,})

def decidable.sort
  (nm:symbol) (args:list (sort_arg ctx))
  (rec : Π(y), y ∈ args
    → Π(i:kind), decidable (well_formed mdl y i))
: Π(i:kind), decidable (well_formed mdl (sort_arg.sort nm args) i)
| kind.nat  := is_false (by { intro p, cases p, })
| kind.sort :=
   if in_f : option.is_some_prop (mdl.lookup_sort nm) then
     match list.holds_pairwise.decide_with_mem (well_formed mdl) args in_f.get.params
              (λa am j jm, rec a am j) with
     | (is_true args_ok) := is_true (well_formed.sort nm args in_f args_ok)
     | (is_false args_not_ok) :=
       is_false
       begin
         intro p,
         cases p with a b c psome prest,
         exact (args_not_ok prest),
       end
     end
   else
     is_false
     begin
       intro p,
       cases p with a b c psome prest,
       exact (in_f psome)
     end

def decidable.eval_param (i:fin ctx.length) (idx:kind)
: decidable (@well_formed mdl ctx (sort_arg.param i) idx) :=
  if h : ctx.nth_le i.val i.is_lt = idx then
    is_true (eq.subst h (well_formed.param i))
  else
    is_false begin
      intro x,
      cases x,
      apply h (eq.refl _),
    end

/-- This returns the type of terms with the given sort. -/
def decidable
: Π(s:sort_arg ctx) (i:kind), decidable (well_formed mdl s i) :=
  @fix ctx
       (λx, Π(i:kind), decidable (@well_formed mdl ctx x i))
       decidable.nat
       decidable.sort
       decidable.eval_param

end
end well_formed

------------------------------------------------------------------------
-- interpretation


section term

parameter {mdl:sort_model}
parameter {ctx : list kind}
parameter {ctx_args : indexed_list kind.interp ctx}

def type_of.app_args
        : Π(args : list (sort_arg ctx))
           (indices : list kind)
           (i : sort_interp indices Type)
           (p:list.holds_pairwise (well_formed mdl) args indices)
           (rec : Π(y), y ∈ args → Π(j:kind), well_formed mdl y j → kind.interp j),
           Type
| [] [] d _ rec := d
| [] (h::r) d p rec := false.elim (by cases p)
| (h::rest) [] d p rec := false.elim (by cases p)
| (arg::rest) (idx::r) d p rec := do
   let is_ok : well_formed mdl arg idx :=
         begin
           cases p with a b c d ph pr,
           exact ph,
         end in
   let rest_ok : list.holds_pairwise (well_formed mdl) rest r :=
         begin
           cases p with a b c d ph pr,
           exact pr,
         end in
   let v := rec arg (or.inl rfl) idx is_ok in
   type_of.app_args rest r (d v) rest_ok (λ(y) (p:y ∈ rest), rec y (or.inr p))

def type_of.app (nm:symbol)
             (args:list (sort_arg ctx))
             (rec : Π(y), y ∈ args → Π(k:kind), well_formed mdl y k → k.interp)
: Π(k:kind), well_formed mdl (sort_arg.sort nm args) k → k.interp
| kind.nat p :=
  begin
    apply false.elim,
    cases p,
  end
| kind.sort p :=
  match well_formed_sort_proof p with
  | ⟨nm_ok, args_ok⟩ :=
    let i := nm_ok.get in
    type_of.app_args args i.params i.interp args_ok rec
  end

def type_of.num  (n:ℕ)
: Π(k:kind), well_formed mdl (@sort_arg.nat ctx n) k → k.interp
| kind.nat _ := ulift.up n
| kind.sort p :=
  begin
    apply false.elim,
    cases p,
  end

def type_of.param (i:fin ctx.length)
: Π(k:kind), well_formed mdl (@sort_arg.param ctx i) k → k.interp
| k p :=
  let r := well_formed.param_proof p in
  cast (congr_arg kind.interp r.symm)
       (ctx_args.nth_le i.val i.is_lt)

/-- This returns the type of terms with the given sort. -/
def type_of  : Π(s:sort_arg ctx) (i:kind), well_formed mdl s i → i.interp :=
  @sort_arg.fix ctx (λs, Π(i), well_formed mdl s i → i.interp) type_of.num type_of.app type_of.param

end term

end sort_arg

------------------------------------------------------------------------
-- sort

/-- A type for terms in SMTLIB -/
inductive sort (mdl:sort_model) (ctx:list kind)
| named (name  : symbol) (args  : list (sort_arg ctx))
        (valid : sort_arg.well_formed mdl (sort_arg.sort name args) kind.sort)
        : sort
| param {} (i:fin ctx.length) (valid : ctx.nth_le i.val i.is_lt = kind.sort) : sort

namespace sort

section
parameter {mdl : sort_model}
parameter {ctx : list kind}

def to_arg : sort mdl ctx → sort_arg ctx
| (sort.named nm args _) := sort_arg.sort nm args
| (sort.param i _)       := sort_arg.param i

instance : has_coe (sort mdl ctx) (sort_arg ctx) := ⟨to_arg⟩

end

protected
def to_sexpr {mdl : sort_model} (s:sort mdl []) : sexpr atom := s.to_arg.to_sexpr

instance sort_is_sexpr (mdl : sort_model) : has_coe (sort mdl []) (sexpr atom) := ⟨sort.to_sexpr⟩

section
parameter {mdl : sort_model}
parameter {ctx : list kind}

protected
def has_dec_eq : decidable_eq (sort mdl ctx)
| (sort.named xnm xargs _) (sort.named ynm yargs _) :=
  if ph : xnm = ynm then
    if pr : xargs = yargs then
      is_true (by simp [ph, pr])
    else
      is_false (λh, pr (sort.named.inj h).right)
  else
    is_false (λh, ph (sort.named.inj h).left)
| (sort.named _ _ _) (sort.param _ _) := is_false (λh, sort.no_confusion h)
| (sort.param _ _) (sort.named _ _ _) := is_false (λh, sort.no_confusion h)
| (sort.param i _) (sort.param j _) :=
  if ph:i = j then
    is_true (by simp [ph])
  else
    is_false (λh, ph (sort.param.inj h))

instance : decidable_eq (sort mdl ctx) := sort.has_dec_eq

end

/- Attempt to construct a parameter using decidabile relations. -/
def by_param {mdl:sort_model}
                   (ctx:list kind)
                   (i:ℕ)
                   (p : as_true (i < ctx.length) . symbol.of_string_tac)
                   (q : as_true (ctx.nth_le i (of_as_true p) = kind.sort) . symbol.of_string_tac)
: sort mdl ctx := sort.param ⟨i, of_as_true p⟩ (of_as_true q)

end sort

/-- Sort associated with Boolean values. -/
def sort.bool {mdl:sort_model} {ctx:list kind} : sort mdl ctx :=
  sort.named symbol.bool []
    (@sort_arg.well_formed.sort mdl ctx symbol.bool []
       (begin simp [sort_model.lookup_sort_bool], exact dec_trivial, end)
       (begin simp [sort_model.lookup_sort_bool], apply list.holds_pairwise.nil, end))

------------------------------------------------------------------------
-- signature

inductive fun_attr
| left_assoc : fun_attr
| right_assoc : fun_attr
| chainable : fun_attr
| pairwise : fun_attr

structure fun_signature (sig:sort_model) : Type 1 :=
(params : list kind := [])
(args   : list (sort sig params) := [])
(return : sort sig params)
(attrs : option fun_attr := none)

/- A function declaration. -/
def fun_decl (sig:sort_model) := symbol × fun_signature sig

def declare_fun {sig:sort_model} (nm:string)
   (params : list kind)
   (args   : list (sort sig params))
   (ret:sort sig params)
   (attrs : option fun_attr := none)
   (p : (symbol.parse nm).is_ok  . symbol.of_string_tac)
   : fun_decl sig :=
  (symbol.of_string nm p, { params := params, args := args, return := ret, attrs := attrs })

def declare_bin {sig:sort_model} (nm:string)
   (params : list kind)
   (s     : sort sig params)
   (attrs : option fun_attr := none)
   (p : (symbol.parse nm).is_ok  . symbol.of_string_tac)
   : fun_decl sig :=
  declare_fun nm params [s,s] s attrs p

inductive sort_args : list kind → Type 1
| nil : sort_args []
| cons {h:kind} {r:list kind} (x:h.interp) (l:sort_args r) : sort_args (h::r)

def provide : Π(ctx:list kind), (sort_args ctx → Type 1) → Type 1
| [] f := f sort_args.nil
| (h::r) f := Π(x:h.interp), provide r (λargs, f (sort_args.cons x args))

def sort_arg.interp {sig:sort_model}
: Π{ctx:list kind} (s:sort_arg ctx) (k:kind), sort_arg.well_formed sig s k → sort_args ctx → Type 1
| ._ (sort_arg.sort _ _) _ _ sort_args.nil := sorry
| ._ s (sort_args.cons h r) := sorry


def declare_rel {sig:sort_model} (nm:string)
   (params : list kind)
   (s     : sort sig params)
   (d     : provide params (λargs, s.interp args → s.interp args → Prop))
   (attrs : option fun_attr := none)
   (p : (symbol.parse nm).is_ok  . symbol.of_string_tac)
   : fun_decl sig :=
  declare_fun nm params [s,s] sort.bool attrs p


open fun_attr

/-- The core function declarations. -/
def core_fun_decls (sig:sort_model) : list (fun_decl sig) :=
  let ctx := [kind.sort] in
  let param0 : sort sig ctx := sort.by_param ctx 0 in
  [ declare_fun "true"  [] []  sort.bool
  , declare_fun "false" [] []  sort.bool
  , declare_fun "not"   [] [sort.bool]  sort.bool
  , declare_bin "=>"    [] sort.bool right_assoc
  , declare_bin "and"   [] sort.bool left_assoc
  , declare_bin "or"    [] sort.bool left_assoc
  , declare_bin "xor"   [] sort.bool left_assoc
  , declare_rel "="        ctx param0 chainable
  , declare_rel "distinct" ctx param0 pairwise
  , declare_fun "ite"      ctx [sort.bool, param0, param0] param0
  ]

/-- This is a signature for sorts and functions. -/
structure signature :=
(sorts : sort_model)
(functions : rbmap symbol (fun_signature sorts))

namespace signature

def from_fun_decls (sig:sort_model)


def core : signature := sorry

/-
def fun_signature (sig:signature) :

/-- Return the indices associated with the given symbol. -/
def sort_interp (m:sort_interp_map) (nm:symbol) : option sort_interp := m.map.find nm

/-- Return the indices associated with the given symbol. -/
def symbol_indices (m:sort_interp_map) (nm:symbol) : option (list kind) :=
  option.map sort_interp.indices (m.sort_interp nm)

/-- Holds when the sort arg is well formed with the given kind type. -/
def sort_arg_ok (m:sort_interp_map) : sort_arg → kind → Prop :=
  sort_arg.well_defined (symbol_indices m)
-/

end signature


namespace sort_arg

/-
section term

parameter (m:sort_interp_map)

def term.app_args
        : Π(args:list sort_arg)
           (i:sort_interp)
           (p:holds_pairwise m.sort_arg_ok
                             args
                             i.indices)
           (rec : Π(y), y ∈ args → Π(j:kind), m.sort_arg_ok y j → kind.domain j),
           Type
| [] ⟨[],d⟩ _ rec := d
| [] ⟨h::r,d⟩ p rec := false.elim (by cases p)
| (h::rest) ⟨[],d⟩ p rec := false.elim (by cases p)
| (arg::rest) ⟨idx::r,d⟩ p rec := do
   let is_ok : m.sort_arg_ok arg idx :=
         begin
           cases p with a b c d ph pr,
           exact ph,
         end in
   let rest_ok : holds_pairwise m.sort_arg_ok  rest r :=
         begin
           cases p with a b c d ph pr,
           exact pr,
         end in
   let v := rec arg (or.inl rfl) idx is_ok in
   term.app_args rest ⟨r,d v⟩ rest_ok (λ(y) (p:y ∈ rest), rec y (or.inr p))

theorem well_defined_sort_proof {nm:symbol} {args:list sort_arg}
(p: sort_arg.well_defined m.symbol_indices (sort_arg.sort_app nm args) kind.sort)
: PropExists
   (λ(is:option.is_some_prop (m.symbol_indices nm)),
    holds_pairwise (sort_arg.well_defined m.symbol_indices) args is.get) :=
begin
  cases p with a b c p_p p_a,
  apply PropExists.intro p_p p_a,
end

def term.app (nm:symbol) (args:list sort_arg)
             (rec : Π(y), y ∈ args → Π(i:kind), m.sort_arg_ok y i → kind.domain i)
: Π(i:kind), m.sort_arg_ok (sort_arg.sort_app nm args) i → kind.domain i
| kind.numeral p :=
  begin
    apply false.elim,
    simp [sort_interp_map.sort_arg_ok] at p,
    cases p,
  end
| kind.sort p :=
  match well_defined_sort_proof p with
  | ⟨nm_ok, args_ok⟩ :=
    let interp : sort_interp := ((option.is_some_prop_map (m.sort_interp nm) sort_interp.indices).mp nm_ok).get in
    let args_ok' : holds_pairwise (sort_arg.well_defined m.symbol_indices) args interp.indices :=
          begin
            simp [ option.get_is_some_prop_map (m.sort_interp nm) sort_interp.indices],
            exact args_ok,
          end in
    term.app_args args interp args_ok' rec
  end

def term.num (x:ℕ)
: Π(i:kind), m.sort_arg_ok (sort_arg.numeral x) i → kind.domain i
| kind.numeral _ := ulift.up x
| kind.sort p :=
  begin
    apply false.elim,
    simp [sort_interp_map.sort_arg_ok] at p,
    cases p,
  end


/-- This returns the type of terms with the given sort. -/
def term : Π(s:sort_arg) (i:kind), m.sort_arg_ok s i → i.domain :=
  @sort_arg.fix (λs, Π(i), m.sort_arg_ok s i → i.domain) term.num term.app

end term
-/

end sort_arg

namespace term

section

parameter (m:sort_interp_map)

def well_formed (s:sort) : Prop := sort_arg.well_defined m.symbol_indices s kind.sort

def term (s:sort) (p:well_formed s) : Type := sort_arg.term m (s.to_arg) kind.sort p

end

end term

/-
section get_term

parameter (m:rbmap symbol sort_interp)

def get_term.app_args (nm:symbol)
        : sort_interp
        → Π(args:list sort_arg) (rec : Π(y), y ∈ args → except string Type),
           except string Type
| ⟨[],d⟩ [] rec := except.ok (d : Type)
| ⟨h::r,d⟩ [] rec := except.error ("Not enough arguments to " ++ repr nm)
| ⟨[],d⟩ (h::rest) rec := except.error ("Too many arguments to " ++ repr nm)
| ⟨kind.numeral::r,d⟩ (arg :: rest) rec := do
   match arg with
   | (numeral n) :=
     get_term.app_args ⟨r,d ⟨n⟩⟩ rest (λ(y) (p:y ∈ rest), rec y (or.inr p))
   | (sort_app nm args) :=
      except.error "Cannot supply sort to numeric sort parameter."
   end
| ⟨kind.sort::r,d⟩ (arg::rest) rec := do
   v ← rec arg (or.inl rfl),
   get_term.app_args ⟨r,d v⟩ rest (λ(y) (p:y ∈ rest), rec y (or.inr p))

def get_term.app (nm:symbol) (args:list sort_arg)
                (rec : Π(y), y ∈ args → except string Type)
: except string Type :=
  match rbmap.find m nm with
  | option.none := except.error ("Undefined sort " ++ repr nm)
  | (option.some d) := get_term.app_args nm d args rec
  end

def get_term.num (x:ℕ) : except string Type :=
  except.error "Cannot get type of numeric argument."

/-- This returns the type of terms with the given sort. -/
def get_term (s:sort_arg) : except string Type :=
  @fix (λx, except string Type) get_term.num (get_term.app m) s

end get_term
-/

inductive bool_term (m:sort_interp_map) (f : Π(s:sort), sort.well_formed m s → Type) : Type
| eq (s:sort) (x y : f s) : bool_term


def sort_interp.bool (f : sort → Type) : sort_interp :=
{ indices := [], term := bool_term f }


/--
This defines an interpretation of sorts.

It maps each sort to an inhabited type, and the mapping for bool must
be Prop.

As there are an unbounded number of sorts, implementations should map
the ones they recognize to the appropriate type, then map the others
to `inhabited_type.uninterpreted` to represent uninterpreted types.
-/
structure logic :=
(sort_map : rbmap symbol sort_interp)
(bool_correct :  sort_arg.term bool.to_arg sort_map = bool_term )

namespace sort

/-- This returns the type of sort arguments (and errors for numeric ones) -/
def get_type_of (s:sort) (l:logic) : except string Type :=
  s.to_arg.type_of l.sort_map

-- This returns the type of sort arguments (and errors for numeric ones)
def type_of (s:sort) (l:logic) (p:(get_type_of s l).is_ok) : Type := p.value

end sort


namespace logic

-- Coercision from prop to l.type_of bool
--def of_prop (l:logic) (x:Prop) : bool.type_of l := cast (eq.symm l.bool_correct) x

-- Coercision from prop to l.type_of bool
--def to_prop (l:logic) (x:l.type_of bool) : Prop := cast l.bool_correct x

-- @fun_type args res@ dReturn the type assigned to functions. -/
--def fun_domain (l:logic) : list sort → sort → Type
--| [] res := l.type_of res
--| (h::r) s := l.type_of h → fun_domain r s

-- Return the type associated with the given sort or Prop if not defined
--def value_of (l:logic) (s:sort) : l.type_of s := (l.interpretation s).value

-- Default value for a function
--def fun_default_value (l:logic) : Π(args:list sort) (res:sort), l.fun_domain args res
--| [] res := l.value_of res
--| (h::r) tp := λ(x : l.type_of h), fun_default_value r tp

end logic

------------------------------------------------------------------------
-- Model

/-- Provides a valuation of symbols in a SMT formula.  This is
parameterized by a logic, which defines how SMTLIB sorts should be
mapped to Lean types.

This maps symbols (which could be functions) to their type information
and a valuation with the correct domain according to the logic.  -/

def model (l:logic) : Type := rbmap symbol (Σ(args:list sort) (s:sort),
l.fun_domain args s)

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
