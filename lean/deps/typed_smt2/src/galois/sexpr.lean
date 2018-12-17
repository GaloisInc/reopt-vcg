/-
This declares an s-expression datatype for generating
expressions and reasoning about their interpretation.
-/
import system.io
import data.array.lemmas -- from mathlib

import galois.data.array
import galois.data.buffer
import galois.data.list
import galois.data.nat

import .char_reader

meta def dec_trivial_tac : tactic unit := do
  tgt ← tactic.target,
  let e := (`(@of_as_true) : expr) tgt,
  r ← tactic.apply e,
  tactic.exact `(trivial)

universes u v w

/--
Meta class for compile-time parsing of strings to data types.
-/
meta class is_meta_string (α : Type) :=
(parse : string → except string α)
(to_expr {} : α → tactic expr)

/-- Tactic for constructing a term by parsing a string. -/
meta def coerce (s:string) (α:Type) [is_meta_string α]  : tactic unit := do
  match is_meta_string.parse α s with
  | (except.ok r) := do
    e ← is_meta_string.to_expr r,
    tactic.exact e
  | (except.error msg) := do
    tactic.fail msg
  end

namespace sexpr

namespace atom

/-- Recognize legal characters in s-expressions. -/
def is_legal_char (c:char) : Prop := not (c ∈ ['(', ')', ' ', '\t', '\n'])

instance is_legal_char.decidable : decidable_pred is_legal_char :=
begin
  intro c,
  unfold atom.is_legal_char,
  apply_instance
end

theorem is_legal_digit_char (n:ℕ) : is_legal_char (nat.digit_char n) :=
begin
  unfold nat.digit_char,
  by_cases (n =  0); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n =  1); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n =  2); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n =  3); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n =  4); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n =  5); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n =  6); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n =  7); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n =  8); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n =  9); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n = 10); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n = 11); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n = 12); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n = 13); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n = 14); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  by_cases (n = 15); simp only [h,if_pos, if_false], {dec_trivial_tac,},
  dec_trivial_tac,
end

/-- Indicate if all characters in buffer are well-formed. -/
def well_formed (b:char_buffer) : Prop
  := ∀i, atom.is_legal_char (b.read i)
  ∧ b ≠ buffer.nil

namespace well_formed

local attribute [reducible] well_formed
instance decidable : decidable_pred well_formed := by apply_instance

end well_formed
end atom

/-- This denotes an atom in the s-expression syntax.

We have not done this yet, but we will need to adds
-/
structure atom :=
(to_char_buffer : char_buffer)
(valid : atom.well_formed to_char_buffer)

namespace atom

protected def to_repr (a:atom) : string := a.to_char_buffer.to_string

instance : has_repr atom := { repr := atom.to_repr }

instance : decidable_eq atom := by tactic.mk_dec_eq_instance

protected def lt (x y : atom) : Prop := x.to_char_buffer.to_string < y.to_char_buffer.to_string

instance has_lt : has_lt atom := { lt := atom.lt }

instance has_decidable_lt (x y : atom) : decidable (x < y) :=
begin
  simp [has_lt.lt, atom.lt],
  apply_instance
end

/-- Map an s-expression to a meta-level expression -/
protected
meta def to_expr (c:atom) : tactic expr := do
  let s := reflected.to_expr (string.reflect c.to_char_buffer.to_string),
  let b := `(string.to_char_buffer %%s),
  gs ← tactic.get_goals,
  proof_var ← tactic.mk_meta_var `(atom.well_formed %%b),
  tactic.set_goals [proof_var],
  tgt ← tactic.target,
  tactic.apply `(@of_as_true %%tgt),
  success ← tactic.try_core (tactic.exact `(trivial)),
  tactic.set_goals gs,
  match success with
  | option.none := tactic.fail $ repr c ++ " is an invalid s-expr atom."
  | (option.some _):= do
    pure `({ atom . to_char_buffer := %%b, valid := %%proof_var })
  end

@[simp]
theorem size_push_back {α} (b:buffer α) (c:α)
: (buffer.push_back b c).size = b.size + 1 :=
begin
  cases b,
  trivial,
end

@[simp]
theorem size_append_list {α} (b:buffer α) (l:list α)
: (buffer.append_list b l).size = l.length + b.size :=
begin
  revert b,
  induction l,
  case list.nil {
    intro b,
    simp [buffer.append_list, nat.zero_add],
  },
  case list.cons : x r ind {
    intro b,
    simp only [buffer.append_list, ind, size_push_back, list.length_cons,
               nat.add_succ, nat.add_zero, nat.succ_add],
  },
end

theorem read_append_list_bound {α} {i:ℕ} {b:buffer α} {l:list α}
: not (i < b.size)
→ i < (buffer.append_list b l).size
→ i - b.size < l.length :=
begin
  intros i_not_lt i_lt_append,
  simp at i_not_lt,
  simp only [size_append_list] at i_lt_append,
  simp only [nat.sub_lt_to_add, i_lt_append, i_not_lt],
  dec_trivial_tac,
end

/--
This converts a nat to a char_buffer in decimal notation.

Note. nat.repr seems to be builtin to the Lean VM magic, so it
is much faster to invoke directly rather than using the functions
used to define it.
-/
protected def nat_to_decimal_buffer (n : ℕ) : char_buffer :=
  n.repr.to_char_buffer


/-- Show that decimal numbers will be well-formed atoms. -/
theorem nat_to_decimal_buffer_is_well_formed (x:ℕ) : atom.well_formed (atom.nat_to_decimal_buffer x) :=
begin
  unfold atom.well_formed,

  intro i_fin,
  cases i_fin with i i_lt,
  dsimp only [atom.nat_to_decimal_buffer],
  dsimp only [nat.repr],
  simp only [buffer.read_to_nth_le],
  simp only [buffer.to_char_buffer_as_string],
  apply and.intro,
  -- Show repr only returns valid characters.
  { simp only [buffer.to_list_to_buffer],
    simp only [list.nth_le_reverse_simp],
    simp only [list.nth_le_map'],
    apply is_legal_digit_char
  },
  -- Show repr is non-empty
  { apply mt (congr_arg buffer.to_list),
    -- For some reason, the simplification rules below require ne is explicitly used
    apply ne.elim,
    simp only [buffer.to_list_to_buffer, buffer.nil_to_list],
    -- The other rules work better with the ne eliminated.
    simp only [ne, list.reverse_eq_nil],
    simp only [list.map_eq_nil],
    apply nat.to_digits_ne_nil,
  },
end

/- Construct a atom from the decimal notation of a nat. -/
def nat_to_decimal (x:ℕ) : atom := ⟨atom.nat_to_decimal_buffer x, atom.nat_to_decimal_buffer_is_well_formed x⟩

end atom

/--
This is a data-structure for representing non-empty lists of
well-formed s-expressions.  It does not allow dotted lists directly,
and they would instead be parsed as a list with a dot followed by
an atom.

The term is structured to both simplify serialization and
top-down/left-to-right parsing.
-/
inductive sexpr_list : Type
| atom : atom → sexpr_list
| nil  : sexpr_list
| parens : sexpr_list → sexpr_list
| prepend_atom : atom → sexpr_list → sexpr_list
| prepend_nil : sexpr_list → sexpr_list
-- @prepend_parens x y@ denotes @(x) y@.
| prepend_parens : sexpr_list → sexpr_list → sexpr_list

namespace sexpr_list

protected
def render {α} [has_append α] (rend : char_buffer → α) : sexpr_list → α
| (atom b) := rend b.to_char_buffer
| nil := rend "()".to_char_buffer
| (parens s) := rend "(".to_char_buffer ++ (s.render ++ rend ")".to_char_buffer)
| (prepend_atom b s) := rend b.to_char_buffer ++ (rend " ".to_char_buffer ++ s.render)
| (prepend_nil s) := rend "() ".to_char_buffer ++ s.render
| (prepend_parens p s) :=
  rend "(".to_char_buffer ++ (p.render ++ (rend ") ".to_char_buffer ++ s.render))

protected
def to_repr (l:sexpr_list) : string := (sexpr_list.render id l).to_string

/-- Return true if this is a single s-expression -/
protected
def is_single : sexpr_list → Prop
| (atom _) := true
| nil := true
| (parens _) := true
| (prepend_atom _ _) := false
| (prepend_nil _) := false
| (prepend_parens _ _) := false

instance (e:sexpr_list) : decidable (e.is_single) :=
begin
  cases e; { unfold sexpr_list.is_single, apply_instance},
end

/-- Map an s-expression to a meta-level expression -/
protected
meta def to_expr : sexpr_list → tactic expr
| (sexpr_list.atom a) := do
  ae ← a.to_expr,
  pure `(atom %%ae)
| nil := do
  pure `(nil)
| (parens s) := do
  e ← to_expr s,
  pure `(parens %%e)
| (prepend_atom a y) := do
  ae ← a.to_expr,
  e ← to_expr y,
  pure `(prepend_atom %%ae %%e)
| (prepend_nil y) := do
  e ← to_expr y,
  pure `(prepend_nil %%e)
| (prepend_parens x y) := do
  xe ← to_expr x,
  ye ← to_expr y,
  pure `(prepend_parens %%xe %%ye)

instance : decidable_eq sexpr_list := by tactic.mk_dec_eq_instance

end sexpr_list

end sexpr

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
structure sexpr : Type :=
(val  : sexpr.sexpr_list)
(pr   : val.is_single)

namespace sexpr

protected
def mk_atom (c:atom) : sexpr := ⟨sexpr_list.atom c, by {unfold sexpr_list.is_single}⟩

protected
def nil : sexpr := ⟨sexpr_list.nil, by {unfold sexpr_list.is_single}⟩

protected
def parens (c:sexpr_list) : sexpr := ⟨sexpr_list.parens c, by {unfold sexpr_list.is_single}⟩

namespace sexpr_list

/-- Prepend sexpression to list -/
def prepend : sexpr → sexpr_list → sexpr_list
| ⟨sexpr_list.atom c, _⟩ y := prepend_atom c y
| ⟨sexpr_list.nil,_⟩ y := prepend_nil y
| ⟨sexpr_list.parens x, _⟩ y := prepend_parens x y

end sexpr_list

open sexpr_list

/-- Render s-expression as a string -/
protected def to_repr (s:sexpr) : string := s.val.to_repr

instance : has_repr sexpr :=
{ repr := sexpr.to_repr }

protected
def of_list_core : sexpr → list sexpr → sexpr_list
| f [] := f.val
| f (h::r) := prepend f (of_list_core h r)

/-- Construct an s-expression from a list -/
protected
def of_list : list sexpr → sexpr
| [] := sexpr.nil
| (h::r) := sexpr.parens (sexpr.of_list_core h r)

def read_atom {m} [char_reader string m] (n:ℕ) (b:char_buffer) : m atom := do
  b1 ← char_reader.read_append_while atom.is_legal_char n b,
  if h : atom.well_formed b1 then
    pure ⟨b1, h⟩
  else
    throw $ repr b ++ " is not a valid atom."


/-- A frame represents the first part of an s-expression that started with a open-paren -/
structure frame :=
(exprs : list sexpr)

namespace frame

/-- Create an empty frame -/
def nil : frame := ⟨[]⟩

/-- Close a frame by appending close paren -/
def close : frame → sexpr
| ⟨[]⟩ := sexpr.nil
| ⟨h::r⟩ := sexpr.parens (list.foldl (λx y, prepend y x) h.val r)

/-- This adds the partial token as an sexpression if the token is non-empty -/
def append_sexpr (f:frame) (t:sexpr) : frame := ⟨ t :: f.exprs⟩

/-- This adds the partial token as an sexpression if the token is non-empty -/
def append_frame (f:frame) (t:frame) : frame := ⟨ t.close :: f.exprs⟩

end frame


section
open char_reader

/-- Read the s-expression from the handle/ -/
def read_core {m} [char_reader string m]
  : ℕ → list frame → m sexpr
| nat.zero frames := do
  throw "out of gas"
| (nat.succ n) frames := do
  mc ← peek_char,
  match mc with
  | option.none :=
    throw "Unexpected end of expression."
  | option.some '(' := do
      consume_char *> read_core n (frame.nil :: frames)
  | option.some ')' := do
    match frames with
    | [] :=
      throw "unexpected close paren"
    | (top_frame::lower_frames) := do
      consume_char,
      match lower_frames with
      | [] := do
        pure top_frame.close
      | (return_frame::rest_frames) :=
        read_core n (frame.append_frame return_frame top_frame :: rest_frames)
      end
    end
  | option.some c :=
    if c.is_whitespace then do
      consume_char,
      read_core n frames
    else do
      consume_char,
      a ← sexpr.mk_atom <$> read_atom n (buffer.nil.push_back c),
      match frames with
      | [] := pure a
      | (top_frame::lower_frames) := do
        read_core n (top_frame.append_sexpr a :: lower_frames)
      end
  end

/-- Read the s-expression from the handle/ -/
def read {m} [char_reader string m] (gas : ℕ) : m sexpr := do
  read_core gas []

end

local attribute [instance] handle_char_reader.string_is_char_reader

/-- Read the s-expression from the handle/ -/
def read_from_handle (h:io.handle) : io (except string sexpr) := do
  let gas : ℕ := 2^64-1 in
  handle_char_reader.read_to_newline h (sexpr.read gas)

local attribute [instance] string_char_reader.string_is_char_reader

def parse (s:string) : except string sexpr :=
  let gas : ℕ := 2^64-1 in
  string_char_reader.read_to_end s (sexpr.read gas)

meta def to_expr : sexpr → tactic expr
| ⟨sexpr_list.atom a,_⟩ := do
   ae <- a.to_expr,
   pure `(sexpr.mk_atom %%ae)
| ⟨nil,_⟩ := do
  pure `(sexpr.nil)
| ⟨parens s, _⟩ := do
  e ← s.to_expr,
  pure `(sexpr.parens %%e)

meta instance : is_meta_string sexpr :=
{ parse := sexpr.parse
, to_expr := sexpr.to_expr
}

/-- Write the s-expression to the handle. -/
def write (h:io.handle) (s:sexpr) : io unit :=
  @sexpr_list.render (io unit) {append := λx y, x >> y} (io.fs.write h) s.val

local infixr  `<+>`:50 := sexpr.append

-- Create an operation applied to some argumen  ts.
def app (op:sexpr) (args : list sexpr) : sexpr := sexpr.parens (sexpr.of_list_core op args)

/-- Apply an binary operation to two sexpressions. -/
def bin_app (op:sexpr) (x y : sexpr) : sexpr :=
  sexpr.parens (prepend op (prepend x y.val))

def from_nat (n:ℕ) : sexpr := sexpr.mk_atom (atom.nat_to_decimal n)

instance : decidable_eq sexpr := by tactic.mk_dec_eq_instance

end sexpr
