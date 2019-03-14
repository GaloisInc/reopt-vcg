import galois.sexpr
import .symbol

namespace smt2

------------------------------------------------------------------------
-- atom

/- A atomic expression within an SMTLIB s-expression. -/
inductive atom
| reserved_word (r:reserved_word) :  atom
| symbol : symbol → atom
| numeral : ℕ → atom


namespace symbol
/-- Construct an atom from an s-expression. -/
def to_atom (s:symbol) : atom := atom.symbol s
instance : has_coe symbol atom := ⟨to_atom⟩
end symbol

namespace reserved_word
protected def to_atom (r:reserved_word) : atom := atom.reserved_word r
instance reserved_word_is_sexpr : has_coe reserved_word atom := ⟨reserved_word.to_atom⟩
end reserved_word

namespace atom

protected
def repr : atom → string
| (reserved_word w) := w.repr
| (symbol s)   := s.repr
| (numeral s)  := s.repr

protected
def to_char_buffer : atom → char_buffer
| (reserved_word w) := w.repr.to_char_buffer
| (symbol s)  := s.repr.to_char_buffer
| (numeral s) := s.repr.to_char_buffer

protected
def read {m} [char_reader string m] (read_count:ℕ) : m atom := do
  mc ← char_reader.peek_char,
  match mc with
  | option.none := throw "Unexpected end of stream."
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
        pure (reserved_word (reserved_word.of_buffer b is_res))
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

end smt2
