
-- Here we defined data and functions for
-- well-formed s-expressions (i.e., s-expressions
-- which exclude improper lists by construction).
namespace WellFormedSExp


section
universe u

inductive SExp (α : Type u)
| atom : α → SExp
| list : List SExp → SExp


-- FIXME consider using wf rec here when it's enabled in lean4
partial def SExp.toString {α : Type u} [HasToString α] : SExp α → String
| SExp.atom a => toString a
| SExp.list ss => "(" ++ (String.join $ (ss.map SExp.toString).intersperse " ")++ ")"


namespace SExp

open SExp

inductive Tag
| atom
| nonAtom

inductive ParseState (α : Type u) : Tag → Type u
| init : ParseState Tag.nonAtom
| inAtom : Char → List Char → ParseState Tag.nonAtom → ParseState Tag.atom
| inList : List (SExp α) → ParseState Tag.nonAtom → ParseState Tag.nonAtom

open ParseState

private def parseFail {α : Type u} (specific: String) : Except String (SExp α × String) :=
Except.error $ "Failed to parse s-expression: " ++ specific ++ "."

private def revStr (c:Char) (cs:List Char) : String := (c::cs).reverse.asString

private def isDelim (c:Char) : Bool := c.isWhitespace || c == '(' || c == ')'


def readAux {α : Type u} (parseAtom : String → Except String α) :
List Char →
Sigma (ParseState α) → 
Except String (SExp α × String)
| [], state => 
  match state with
  | ⟨_, init _⟩ => parseFail $ "input was empty"
  | ⟨_, inAtom x xs aPrev⟩ =>
    match aPrev with
    | init _ => do
      a ← parseAtom $ revStr x xs;
      pure (atom a, "")
    | inList _ _ => parseFail "missing closing parenthesis"
  | ⟨_, inList _ _⟩ => parseFail "missing closing parenthesis"
| (c::cs), state =>
  match state with
  | ⟨_, init _⟩ =>
    if c.isWhitespace then readAux cs ⟨Tag.nonAtom, init α⟩
    else if c == '(' then readAux cs $ ⟨Tag.nonAtom, inList [] (init α)⟩
    else if c == ')' then parseFail "unexpected closing parenthesis"
    else readAux cs $ ⟨Tag.atom, inAtom c [] (init α)⟩
  | ⟨_, inAtom x xs prev⟩ =>
    if c.isWhitespace then 
      match prev with
      | init _ => do
        a ← parseAtom $ revStr x xs;
        pure (atom a, "")
      | inList ys ysPrev => do
        a ← parseAtom $ revStr x xs;
        readAux cs $ ⟨Tag.nonAtom, inList (atom a::ys) ysPrev⟩
    else if c == '(' then do
        a ← parseAtom $ revStr x xs;
        match prev with
        | init _ => pure (atom a, (c::cs).asString)
        | inList zs zsPrev => readAux cs $ ⟨Tag.nonAtom, inList [] (inList (atom a::zs) zsPrev)⟩
    else if c == ')' then do
        a ← (parseAtom $ revStr x xs).map atom;
        match prev with
        | init _ => pure (a, (c::cs).asString)
        | inList ys ysPrev =>
          let l := list (a::ys).reverse;
          match ysPrev with
          | init _ => pure (l, cs.asString)
          | inList zs zsPrev => readAux cs $ ⟨Tag.nonAtom, inList (l::zs) zsPrev⟩
    else readAux cs $ ⟨Tag.atom, inAtom c (x::xs) prev⟩
  | ⟨_, inList xs xsPrev⟩ =>
    if c.isWhitespace then readAux cs $ state
    else if c == '(' then readAux cs $ ⟨Tag.nonAtom, inList [] $ inList xs xsPrev⟩
    else if c == ')' then
      match xsPrev with
      | init _ => pure (list xs.reverse, cs.asString)
      | inList zs zsPrev => readAux cs $ ⟨Tag.nonAtom, inList ((list xs.reverse)::zs) zsPrev⟩
    else readAux cs $ ⟨Tag.atom, inAtom c [] $ inList xs xsPrev⟩


-- Attempts to read the an s-expression from the given string,
-- returning either the first s-expression encountered and remainder
-- of the string or an error message.
def read 
{α : Type u}
(parseAtom : String → Except String α)
(str: String) 
: Except String (SExp α × String) :=
readAux parseAtom str.data ⟨Tag.nonAtom, init α⟩

-- Attempts to read the an s-expression from the given string,
-- returning either the first s-expression encountered and remainder
-- of the string or an error message.
def read1
{α : Type u}
(parseAtom : String → Except String α)
(str: String) 
: Except String (SExp α) := do
(s, _) ← read parseAtom str;
pure s

end SExp

end

end WellFormedSExp
