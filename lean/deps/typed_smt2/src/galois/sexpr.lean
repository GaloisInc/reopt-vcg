/-
This declares an s-expression datatype for generating
expressions and reasoning about their interpretation.
-/
import system.io
import galois.data.buffer

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

structure atom :=
(to_char_buffer : char_buffer)

namespace atom

instance : decidable_eq atom := by tactic.mk_dec_eq_instance

end atom

/--
This is a data-structure for representing non-empty

The internal types are strictly general than what one may ordinarily
expect of s-expressions to allow arbitrary strings to be converted into
s-expressions, and concatenating two s-expressions.

We do add a decidable_eq instance for s-expressions, but it is structural
and two s expressions may be distinct, but render to the same string.
The intent is to allow one to efficiently generate s-expressions,
do lightweight pattern matching on them, and write them to handles.
-/
inductive sexpr_list : Type
| atom : atom → sexpr_list
| empty_parens : sexpr_list
| parens : sexpr_list → sexpr_list
-- This appends two s-expressions with a space in between.
| prepend_atom : atom → sexpr_list → sexpr_list
| prepend_empty_parens : sexpr_list → sexpr_list
| prepend_parens : sexpr_list → sexpr_list → sexpr_list

namespace sexpr_list

protected
def render {α} [has_append α] (rend : char_buffer → α) : sexpr_list → α
| (atom b) := rend b.to_char_buffer
| empty_parens := rend "()".to_char_buffer
| (parens s) := rend "(".to_char_buffer ++ (s.render ++ rend ")".to_char_buffer)
| (prepend_atom b s) := rend b.to_char_buffer ++ (rend " ".to_char_buffer ++ s.render)
| (prepend_empty_parens s) := rend "() ".to_char_buffer ++ s.render
| (prepend_parens p s) :=
  rend "(".to_char_buffer ++ (p.render ++ (rend ") ".to_char_buffer ++ s.render))

protected
def to_repr (l:sexpr_list) : string := (sexpr_list.render id l).to_string


/-- Return true if this is a single s-expression -/
protected
def is_single : sexpr_list → Prop
| (atom _) := true
| empty_parens := true
| (parens _) := true
| (prepend_atom _ _) := false
| (prepend_empty_parens _) := false
| (prepend_parens _ _) := false

instance (e:sexpr_list) : decidable (e.is_single) :=
begin
  cases e; { unfold sexpr_list.is_single, apply_instance},
end

/-- Map an s-expression to a meta-level expression -/
protected
meta def to_expr : sexpr_list → tactic expr
| (sexpr_list.atom ⟨c⟩) := do
  let s := reflected.to_expr (string.reflect c.to_string) in
  pure `(atom ⟨string.to_char_buffer %%s⟩)
| empty_parens := do
  pure `(empty_parens)
| (parens s) := do
  e ← to_expr s,
  pure `(parens %%e)
| (prepend_atom ⟨c⟩ y) := do
  let s := reflected.to_expr (string.reflect c.to_string),
  e ← to_expr y,
  pure `(prepend_atom ⟨string.to_char_buffer %%s⟩ %%e)
| (prepend_empty_parens y) := do
  e ← to_expr y,
  pure `(prepend_empty_parens %%e)
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
def empty_parens : sexpr := ⟨sexpr_list.empty_parens, by {unfold sexpr_list.is_single}⟩

protected
def parens (c:sexpr_list) : sexpr := ⟨sexpr_list.parens c, by {unfold sexpr_list.is_single}⟩

namespace sexpr_list

/-- Prepend sexpression to list -/
def prepend : sexpr → sexpr_list → sexpr_list
| ⟨sexpr_list.atom c, _⟩ y := prepend_atom c y
| ⟨sexpr_list.empty_parens,_⟩ y := prepend_empty_parens y
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
| [] := sexpr.empty_parens
| (h::r) := sexpr.parens (sexpr.of_list_core h r)

/-- A token read up so far -/
structure partial_token :=
(reversed_chars : list char)

namespace partial_token

/-- Create empty partial token -/
def nil : partial_token := {reversed_chars := []}

/-- Check if partial token is empty -/
def empty (t:partial_token) : bool := t.reversed_chars.empty

/-- Append a character to the end of a partial token -/
def append (t:partial_token) (c:char) : partial_token :=
  { reversed_chars := c :: t.reversed_chars }

/-- Generate an s-expression from a partial token. -/
def to_sexpr (t:partial_token) : sexpr :=
  sexpr.mk_atom ⟨t.reversed_chars.reverse.as_string.to_char_buffer⟩

end partial_token

/-- A frame represents the first part of an s-expression that started with a open-paren -/
structure frame :=
(exprs : list sexpr)

namespace frame

/-- Create an empty frame -/
def nil : frame := ⟨[]⟩

/-- This adds the partial token as an sexpression if the token is non-empty -/
def append_partial (f:frame) (t:partial_token) : frame :=
  if t.empty then
    f
  else
    ⟨t.to_sexpr :: f.exprs⟩

/-- Close a frame by appending close paren -/
def close : frame → sexpr
| ⟨[]⟩ := sexpr.empty_parens
| ⟨h::r⟩ := sexpr.parens (list.foldl (λx y, prepend y x) h.val r)

/-- This adds the partial token as an sexpression if the token is non-empty -/
def append_frame (f:frame) (t:frame) : frame := ⟨ t.close :: f.exprs⟩

--| frame.empty := parens sexpr.empty
--| (frame.non_empty s) := parens s

end frame

/-- Read to newline -/
def read_to_newline {m} [monad m] [monad_except string m] (get_char : m char) : ℕ → m unit
| nat.zero := throw "out of gas"
| (nat.succ n) := do
  c ← monad_lift get_char,
  if c = '\n' then
    pure ()
  else if c.is_whitespace then
    read_to_newline n
  else
    throw $ "Unexpected character at end of expression " ++ c.to_string

/-- Read the s-expression from the handle/ -/
def read_inner {m} [monad m] [monad_except string m] (get_char : m char)
  : ℕ → partial_token → list frame → m sexpr
| nat.zero prev frames := do
  throw "out of gas"
| (nat.succ n) prev frames := do
  c ← monad_lift get_char,
  if c = '(' then
    match frames with
    | [] :=
      if prev.empty then
        read_inner n partial_token.nil [frame.nil]
      else
        throw "Unexpected open paren"
    | (top_frame::rest_frames) :=
      read_inner n partial_token.nil (frame.nil :: top_frame.append_partial prev :: rest_frames)
    end
  else if c = ')' then
    match frames with
    | [] :=
      throw "unexpected close paren"
    | (top_frame::lower_frames) :=
      let new_top := (top_frame.append_partial prev) in
      match lower_frames with
      | [] := do
        read_to_newline get_char n,
        pure new_top.close
      | (return_frame::rest_frames) :=
        read_inner n partial_token.nil (frame.append_frame return_frame new_top :: rest_frames)
      end
    end
  else if c = '\n' then
    match frames with
    | [] := do
      pure prev.to_sexpr
    | (top_frame::lower_frames) := do
      throw "end of line reached before close paren"
    end
  else if c.is_whitespace then
    match frames with
    | [] := do
      read_to_newline get_char n,
      pure prev.to_sexpr
    | (top_frame::lower_frames) := do
      read_inner n partial_token.nil (top_frame.append_partial prev :: lower_frames)
    end
  else
    read_inner n (prev.append c) frames

/-- Read the s-expression from the handle/ -/
def read {m} [monad m] [monad_except string m] (get_char : m char) (gas : ℕ) : m sexpr := do
  read_inner get_char gas partial_token.nil []

/-- Read the s-expression from the handle/ -/
def read_from_handle (h:io.handle) : io (except string sexpr) := do
  let get_char : except_t string io char := monad_lift $ io.fs.get_char h in
  (read get_char (2^64-1)).run

def parse (s:string) : except string sexpr :=
  let get_char : except_t string (state (list char)) char := do
        s <- get,
        match s with
        | [] := throw "Unexpected end of string"
        | (h::r) := do put r, pure h
        end in
  match (read get_char (s.length+2)).run.run (s.to_list ++ ['\n']) with
  | ⟨r, _⟩ := r
  end

meta def to_expr : sexpr → tactic expr
| ⟨sexpr_list.atom ⟨b⟩,_⟩ := do
  let s := reflected.to_expr (string.reflect b.to_string) in
  pure `(sexpr.mk_atom ⟨string.to_char_buffer %%s⟩)
| ⟨empty_parens,_⟩ := do
  pure `(sexpr.empty_parens)
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

def from_nat (x:ℕ) : sexpr := sexpr.mk_atom ⟨x.repr.to_char_buffer⟩

instance : decidable_eq sexpr := by tactic.mk_dec_eq_instance

end sexpr
