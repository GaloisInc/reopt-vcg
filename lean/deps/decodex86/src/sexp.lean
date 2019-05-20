
import system.io -- debug

import data.buffer.parser

inductive sexp
  | atom : string -> sexp
  | list : list sexp -> sexp

mutual def sexp_to_string, sexp_to_string_list
with sexp_to_string : sexp -> string
  | (sexp.atom s) := s
  | (sexp.list ss) := "(" ++ sexp_to_string_list ss ++ ")"
with sexp_to_string_list : list sexp -> string
  | [] := ""
  | (s :: ss) := 
    sexp_to_string s ++ (match ss with | [] := "" | _ := " " end) ++ sexp_to_string_list ss

instance sexp_has_repr: has_repr sexp := ⟨sexp_to_string⟩

namespace sexp

section 

open parser

@[reducible] def is_whitespace (c : char) : Prop :=
  c = ' ' ∨ c = '\t' ∨ c = '\n'

def whitespace : parser unit := many (sat is_whitespace) >> return ()

def whitespaced {a} (p : parser a) : parser a :=
  whitespace *> p <* whitespace

def atom_parser : parser sexp :=
    sexp.atom <$> list.as_string <$> many1 (sat (λc, ¬ is_whitespace c ∧ c ≠ '(' ∧ c ≠ ')'))

def list_parser : parser sexp -> parser sexp := λrec,  
    do ch '(',
       vs <- many rec,
       ch ')',
       pure (sexp.list vs)
 
def sexp_parser : parser sexp := 
  fix (λrec, whitespaced (atom_parser <|> list_parser rec))

def from_string := run_string sexp_parser
def from_buffer := run sexp_parser
end

end sexp
 /-
def main : io unit := do
  args ← io.cmdline_args,
  stdin <- io.stdin,
  buf <- io.fs.read_to_end stdin,  
  match sexp.from_buffer buf with
  | (sum.inl e) := io.fail ("Decode error: " ++ e)
  | (sum.inr r) := io.put_str_ln (repr r)
  end
-/
