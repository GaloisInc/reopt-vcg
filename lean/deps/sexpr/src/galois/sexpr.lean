/-
This declares an s-expression datatype for generating
expressions and reasoning about their interpretation.
-/
import system.io
import data.array.lemmas -- from mathlib
import galois.category.except

import galois.data.array
import galois.data.buffer
import galois.data.list
import galois.data.nat

import .char_reader

universes u v w

namespace sexpr

class is_atom (α : Type) :=
(to_char_buffer : α → char_buffer)
(read {m:Type → Type} [char_reader string m] (n:ℕ) : m α)

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
inductive sexpr (α:Type)
| atom : α -> sexpr
| parens : list sexpr -> sexpr

namespace sexpr

protected
def mk_atom {α:Type} (c:α) : sexpr α := sexpr.atom c

protected
def nil {α:Type} : sexpr α := sexpr.parens []

/-- Render s-expression as a string -/
mutual def render, list_render {α:Type} [h : is_atom α] {β} [has_append β] (rend : char_buffer → β)
with render : sexpr α -> β
     | (atom s) := rend (@is_atom.to_char_buffer _ h s)
     | (parens []) := rend "()".to_char_buffer
     | (parens (h::t)) := rend "(".to_char_buffer ++ render h ++ list_render t
with list_render : list (sexpr α) -> β
     | [] := rend ")".to_char_buffer
     | (s :: ss) := rend " ".to_char_buffer ++ render s ++ list_render ss

/-- Render s-expression as a string -/
def repr {α:Type} [h : is_atom α] : sexpr α -> string := render buffer.to_string

instance {α} [is_atom α] : has_repr (sexpr α) := { repr := sexpr.repr }

/-- Construct an s-expression from a list of s-expressions -/
protected
def of_list {α} : list (sexpr α) → sexpr α := sexpr.parens

/-- A frame represents the first part of an s-expression that started with a open-paren -/
structure frame (α:Type) :=
(exprs : list (sexpr α))

namespace frame

/-- Create an empty frame -/
def nil {α} : frame α := ⟨[]⟩

/-- Close a frame by appending close paren -/
def close {α} (f:frame α) : sexpr α := sexpr.parens f.exprs.reverse

/-- This adds the partial token as an sexpression if the token is non-empty -/
def append_sexpr {α} (f:frame α) (t:sexpr α) : frame α := ⟨ t :: f.exprs⟩

/-- This adds the partial token as an sexpression if the token is non-empty -/
def append_frame {α} (f:frame α) (t:frame α) : frame α := append_sexpr f t.close

end frame

section
open char_reader

/-- The character after an atom should be empty or a close paren or whitespace. -/
def check_atom_term {m} [char_reader string m] : m unit := do
  mc ← peek_char,
 match mc with
 | option.none := pure ()
 | (option.some c) := do
    when (c ∉ ['(', ')'] ∧ ¬c.is_whitespace)
      (throw ("Unexpected character "++ c.repr))
 end

/-- Read the s-expression from the handle/ -/
def read_core {α:Type} [is_atom α] {m} [char_reader string m]
  : ℕ → list (frame α) → m (sexpr α)
| nat.zero frames := do
  throw "out of gas"
| (nat.succ n) frames := (do
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
      a ← sexpr.mk_atom <$> is_atom.read α n,
      check_atom_term,
      match frames with
      | [] := pure a
      | (top_frame::lower_frames) := do
        read_core n (top_frame.append_sexpr a :: lower_frames)
      end
  end)

/-- Read the s-expression from the handle/ -/
def read (α:Type) [i:is_atom α] {m} [char_reader string m] (gas : ℕ) : m (sexpr α) :=
  @read_core α i _ _ gas []

end

local attribute [instance] char_reader.handle_char_reader.string_is_char_reader

/-- Read the s-expression from the handle/ -/
def read_from_handle {α} [i:is_atom α] (h:io.handle) : io (except string (sexpr α)) := do
  let gas : ℕ := 2^64-1 in
  char_reader.read_from_handle h (@sexpr.read α i _ _ gas)

--local attribute [instance] string_char_reader.string_is_char_reader

/-- Parse the string as an s-expression -/
def parse {α:Type} [i:is_atom α] (s:string) : except string (sexpr α) :=
  let gas : ℕ := 2^64-1 in
  char_reader.read_from_string s (@sexpr.read α i _ _ gas)

/-- Write the s-expression to the handle. -/
def write {α} [is_atom α] (h:io.handle) (s:sexpr α) : io unit :=
  @sexpr.render α _ (io unit) {append := λx y, x >> y} (io.fs.write h) s

local infixr  `<+>`:50 := sexpr.append

-- Create an operation applied to some argumen  ts.
def app {α} (op:sexpr α) (args : list (sexpr α)) : sexpr α :=
  sexpr.parens (op :: args)

/-- Apply an binary operation to two sexpressions. -/
def bin_app {α} (op:sexpr α) (x y : sexpr α) : sexpr α := sexpr.parens [op, x,y]

instance (α) [decidable_eq α] : decidable_eq (sexpr α) := by tactic.mk_dec_eq_instance

meta def exact_trivial_tac : tactic unit := `[exact trivial]

/- Construct an atom from a string literal. -/
def of_string {α} [i:is_atom α] (nm:string)
      (p : except.is_ok (char_reader.read_from_string nm (@sexpr.read α i _ _ 1024)) . exact_trivial_tac)
: sexpr α := p.value

end sexpr
