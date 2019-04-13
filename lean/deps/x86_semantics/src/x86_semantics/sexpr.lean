import .common

namespace mc_semantics

namespace sexpr_rep

def symbol := string

instance : has_append symbol := ⟨string.append⟩

/- A atomic expression within an s-expression. -/
inductive atom
| symbol   : symbol → atom
| numeral  : ℕ      → atom
| string   : string → atom

protected
def repr : atom → string
| (atom.symbol s) := s
| (atom.numeral n) := n.repr
| (atom.string s) := "̈\"" ++ s ++ "\""

protected
def symbol.sexpr : symbol → sexpr atom
| s := sexpr.mk_atom (atom.symbol s)

protected
def numeral.sexpr : ℕ → sexpr atom
| n := sexpr.mk_atom (atom.numeral n)

protected
def string.sexpr : string → sexpr atom
| s := sexpr.mk_atom (atom.string s)

protected
def to_char_buffer : atom → char_buffer
| (atom.symbol s) := s.to_char_buffer
| (atom.numeral s) := s.repr.to_char_buffer
| (atom.string s) := ("\"" ++ s ++ "\"").to_char_buffer

/-- Symbol characters allowed in simple symbols -/
def char_symbols : list char := ['$', '_']

/-- Predicate that checks if character is allowed in a simple symbol. -/
inductive is_symbol_char (c:char) : Prop
| is_alpha : char.is_alpha c → is_symbol_char
| is_digit : char.is_digit c → is_symbol_char
| is_other : c ∈ char_symbols → is_symbol_char

namespace is_symbol_char

instance is_decidable : decidable_pred is_symbol_char
| c :=
  if f : c.is_alpha then
    is_true (is_alpha f)
  else if g : c.is_digit then
    is_true (is_digit g)
  else if h : c ∈ char_symbols  then
    is_true (is_other h)
  else
    is_false begin intro p, cases p; contradiction, end

end is_symbol_char

protected
def read {m} [char_reader string m] (read_count:ℕ) : m atom := do
  mc ← char_reader.peek_char,
  match mc with
  | option.none := throw "Unexpected end of stream."
  | option.some '\"' := do
    char_reader.consume_char,
    b ← char_reader.read_while (λc, c ≠ '\"') read_count,
    char_reader.consume_char,
    pure (atom.string b.to_string)
  | option.some c :=
    if c.is_digit then (do
      b ← char_reader.read_while char.is_digit read_count,
      pure (atom.numeral b.to_string.to_nat))
    else if is_symbol_char c then (do
      -- Read symbol characters
      b ← char_reader.read_while is_symbol_char read_count,
     pure (atom.symbol b.to_string))
    else
      throw $ "Unexpected character " ++ c.to_string
  end

instance atom_is_atom : sexpr.is_atom atom :=
{ to_char_buffer := sexpr_rep.to_char_buffer
, read := @sexpr_rep.read
}

def app (s:symbol) (l:list (sexpr atom)) := sexpr.app s.sexpr l

end sexpr_rep

open sexpr_rep

def arg_index.sexpr (idx:arg_index) : sexpr atom :=
  app "arg" [numeral.sexpr idx]

namespace nat_expr

protected def sexpr : nat_expr → sexpr atom
| (lit x) := numeral.sexpr x
| (var x) := x.sexpr
| (add x y) := app "add" [x.sexpr, y.sexpr]
| (sub x y) := app "sub" [x.sexpr, y.sexpr]
| (mul x y) := app "mul" [x.sexpr, y.sexpr]
| (div x y) := app "div" [x.sexpr, y.sexpr]

instance : has_repr nat_expr := ⟨sexpr.repr ∘ nat_expr.sexpr⟩

end nat_expr

namespace one_of

protected def pp {l:list ℕ} : one_of l → string
| (var i) := i.sexpr.repr

protected def sexpr {l:list ℕ} (x:one_of l) := x.to_nat_expr.sexpr

end one_of

namespace type

protected
def sexpr' : Π(in_fun:bool), type → sexpr atom
| _ (bv w) := app "bv" [w.sexpr]
| _ bit    := symbol.sexpr "bit"
| _ float  := symbol.sexpr "float"
| _ double := symbol.sexpr "double"
| _ x86_80 := symbol.sexpr "x86_80"
| _ (vec w tp) := app "vec" [w.sexpr, tp.sexpr' ff]
| _ (pair x y) := app "pair" [x.sexpr' ff, y.sexpr' ff]
| in_fun (fn a r) :=
  if in_fun then
    sexpr.parens [a.sexpr' ff, r.sexpr' tt]
  else
    app "fun" [a.sexpr' ff, r.sexpr' tt]

protected
def sexpr : type → sexpr atom := type.sexpr' ff

protected
def pp : type → string := sexpr.repr ∘ type.sexpr

end type

end mc_semantics

namespace x86
open mc_semantics
open mc_semantics.sexpr_rep
open mc_semantics.type

namespace reg

/-
protected def sexpr : Π{tp:type}, reg tp → sexpr atom
| ._ (concrete_gpreg idx tp) := symbol.sexpr $ "$" ++
  match tp with
  | gpreg_type.reg8l := list.nth_le reg.r8l_names idx.val idx.is_lt
  | gpreg_type.reg16 := list.nth_le reg.r16_names idx.val idx.is_lt
  | gpreg_type.reg32 := list.nth_le reg.r32_names idx.val idx.is_lt
  | gpreg_type.reg64 := list.nth_le reg.r64_names idx.val idx.is_lt
  end
| ._ (concrete_flagreg idx) := symbol.sexpr $ "$" ++
   match list.nth reg.flag_names idx.val with
   | (option.some nm) := nm
   | option.none :=  "REVERSED_" ++ idx.val.repr
   end
-/

--protected def repr : Π{tp:type}, reg tp → string := λ_, sexpr.repr ∘ reg.sexpr

end reg

namespace addr

protected def sexpr {tp:type} : addr tp → sexpr atom
| (arg idx) := idx.sexpr

end addr

namespace prim

def sexpr : Π{tp:type}, prim tp → sexpr atom
| ._ (eq tp) := app "eq" [tp.sexpr]
| ._ (neq tp) := app "neq" [tp.sexpr]
| ._ (mux tp) := app "mux" [tp.sexpr]

| ._ bit_zero := symbol.sexpr "bit0"
| ._ bit_one  := symbol.sexpr "bit1"
| ._ bit_or  := symbol.sexpr "bit_or"
| ._ bit_and := symbol.sexpr "bit_and"
| ._ bit_xor := symbol.sexpr "bit_xor"

| ._ (bv_nat w n) := app "bv_nat" [w.sexpr, n.sexpr]
| ._ (add i) := app "add" [i.sexpr]
| ._ (adc i) := app "adc" [i.sexpr]
| ._ (uadc_overflows i) := app "uadc_overflows" [i.sexpr]
| ._ (sadc_overflows i) := app "sadc_overflows" [i.sexpr]
| ._ (sub i) := app "sub" [i.sexpr]
| ._ (ssbb_overflows i) := app "ssbb_overflows" [i.sexpr]
| ._ (usbb_overflows i) := app "usbb_overflows" [i.sexpr]
| ._ (neg tp) := app "neg" [tp.sexpr]
| ._ (mul i) := app "mul" [i.sexpr]
| ._ (quotRem i) := app "quotRem" [i.sexpr]
| ._ (squotRem i) := app "squotRem" [i.sexpr]

| ._ (ule i) := app "ule" [i.sexpr]
| ._ (ult i) := app "ult" [i.sexpr]

| ._ (slice w u l) := app "slice" [w.sexpr, u.sexpr, l.sexpr]
| ._ (sext i o) := app "sext" [i.sexpr, o.sexpr]
| ._ (uext i o) := app "uext" [i.sexpr, o.sexpr]
| ._ (trunc i o) := app "trunc" [i.sexpr, o.sexpr]
| ._ (cat i) := app "cat" [i.sexpr]
| ._ (msb i) := app "msb" [i.sexpr]

| ._ (bv_and i) := app "bv_and" [i.sexpr]
| ._ (bv_or  i) := app "bv_or"  [i.sexpr]
| ._ (bv_xor i) := app "bv_xor" [i.sexpr]
| ._ (bv_complement i) := app "bv_complement" [i.sexpr]

| ._ (shl i) := app "shl" [i.sexpr]
| ._ (shl_carry i) := app "shl_carry" [i.sexpr]

| ._ (shr i) := app "shr" [i.sexpr]
| ._ (shr_carry i) := app "shr_carry" [i.sexpr]

| ._ (sar i) := app "sar" [i.sexpr]
| ._ (sar_carry i) := app "sar_carry" [i.sexpr]

| ._ (even_parity i) := app "even_parity" [i.sexpr]
| ._ (bsf i) := app "bsf" [i.sexpr]
| ._ (bsr i) := app "bsr" [i.sexpr]
| ._ (bswap i) := app "bswap" [i.sexpr]

| ._ (btc w j) := app "btc" [w.sexpr, j.sexpr]
| ._ (btr w j) := app "btr" [w.sexpr, j.sexpr]
| ._ (bts w j) := app "bts" [w.sexpr, j.sexpr]

| ._ (bv_to_x86_80 w) := app "sext" [w.sexpr]
| ._ float_to_x86_80 := symbol.sexpr "float_to_x86_80"
| ._ double_to_x86_80 := symbol.sexpr "double_to_X86_80"
| ._ x87_fadd := symbol.sexpr "x87_fadd"
| ._ (pair_fst x y) := app "pair_fst" [x.sexpr, y.sexpr]
| ._ (pair_snd x y) := app "pair_snd" [x.sexpr, y.sexpr]


end prim

namespace gpreg_type

protected def sexpr : gpreg_type → sexpr atom
| reg8l := symbol.sexpr "reg8l"
| reg8h := symbol.sexpr "reg8h"
| reg16 := symbol.sexpr "reg16"
| reg32 := symbol.sexpr "reg32"
| reg64 := symbol.sexpr "reg64"

end gpreg_type

namespace concrete_reg

protected def sexpr : Π{tp:type}, concrete_reg tp → sexpr atom
| ._ (gpreg i tp) := app "gpreg" [numeral.sexpr i.val, tp.sexpr]
| ._ (flagreg i)  := app "flagreg" [numeral.sexpr i.val]

end concrete_reg

namespace expression

protected
def sexpr' : Π{tp:type} (v:expression tp), list (sexpr atom) → sexpr atom
| ._ (primitive o) l := sexpr.app o.sexpr l
| ._ (@bit_test wr wi r i) l := sexpr_rep.app "bit_test" [wr.sexpr, wi.sexpr, r.sexpr' [], i.sexpr' []]
| ._ (@mulc  m x)   l := sexpr_rep.app "mulc"  [m.sexpr, x.sexpr' []]
| ._ (@quotc m x)   l := sexpr_rep.app "quotc" [m.sexpr, x.sexpr' []]
| ._ (@undef tp)    l := sexpr_rep.app "undef" [tp.sexpr]
| ._ (@app _ _ f x) l := sexpr' f (x.sexpr' [] :: l)
| ._ (@get_reg _ r) l := sexpr_rep.app "get_reg" [r.sexpr]
| ._ (@read tp a)   l := sexpr_rep.app "read" [tp.sexpr, a.sexpr' []]
| ._ (@streg i)     l := sexpr_rep.app "streg" [numeral.sexpr i.val]
| ._ (@get_local i tp) l := sexpr_rep.app "read"    [numeral.sexpr i, tp.sexpr]
| ._ (@imm_arg  i tp)  l := sexpr_rep.app "imm_arg"  [i.sexpr, tp.sexpr]
| ._ (@addr_arg i)     l := sexpr_rep.app "addr_arg" [i.sexpr]
| ._ (@read_arg i tp)  l := sexpr_rep.app "read_arg" [i.sexpr, tp.sexpr]

protected def sexpr {tp:type} (e:expression tp) : sexpr atom := e.sexpr' []

end expression

namespace lhs

protected def sexpr : Π{tp:type}, lhs tp → sexpr atom
| ._ (set_reg r) := app "set_reg" [r.sexpr]
| ._ (write_addr a tp)  := app "write_addr" [a.sexpr, tp.sexpr]
| ._ (write_arg idx tp) := app "write_arg" [idx.sexpr, tp.sexpr]
| ._ (streg idx) := app "streg" [numeral.sexpr idx.val]

end lhs

namespace event

protected def sexpr : event → sexpr atom
| syscall := app "syscall" []
| (unsupported msg) := app "unsupported" [string.sexpr msg]
| pop_x87_register_stack := app "pop_x87_register_stack" []
| (call addr) := app "call" [addr.sexpr]
| (jmp  addr) := app "jmp"  [addr.sexpr]
| (branch cond addr) := app "branch" [cond.sexpr, addr.sexpr]
| hlt := app "hlt" []
| (xchg addr1 addr2) := app "xchg" [addr1.sexpr, addr2.sexpr]

end event

namespace action

protected def sexpr : action → sexpr atom
| (set l r)            := app "set" [l.sexpr, r.sexpr]
| (set_cond l c v)     := app "set_cond" [l.sexpr, c.sexpr, v.sexpr]
| (set_aligned l r a)  := app "set_aligned" [l.sexpr, r.sexpr, a.sexpr]
| (local_def idx v)    := app "var" [numeral.sexpr idx, v.sexpr]
| (event e)            := e.sexpr

end action

namespace binding

def sexpr : binding → sexpr atom
| (one_of l) := app "one_of" (numeral.sexpr <$> l)
| (reg  tp) := app "reg"  [tp.sexpr]
| (addr tp) := app "addr" [tp.sexpr]
| (imm  tp) := app "imm"  [tp.sexpr]
| (lhs  tp) := app "lhs"  [tp.sexpr]
| (expression tp) := app "expr" [tp.sexpr]


--def pp : binding → string := sexpr.repr ∘ binding.sexpr

end binding

namespace pattern

private
def sexpr_bindings : list binding → list (sexpr atom) → list (sexpr atom)
| [] r := r
| (b::r) l := sexpr_bindings r (b.sexpr :: l)

protected
def sexpr (p:pattern) : sexpr atom
  := app "pattern" $ sexpr.parens (sexpr_bindings p.context.bindings [])
                     :: (action.sexpr <$> p.actions)

end pattern

namespace instruction

def sexpr (i:instruction) : sexpr atom :=
  app "instruction" (symbol.sexpr i.mnemonic :: pattern.sexpr <$> i.patterns)

def repr : instruction → string := sexpr.repr ∘ instruction.sexpr

instance : has_repr instruction := ⟨instruction.repr⟩

end instruction


end x86
