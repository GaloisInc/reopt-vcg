
import .sexp

namespace decodex86

def regN := string

structure register :=
  (top : regN)
  (reg : regN)
  (width : ℕ)
  (offset : ℕ)

def register_to_string : register -> string := λr, 
  string.intercalate " " ["(", "R", r.top, r.reg, repr r.width, repr r.offset, ")"]

instance register_has_repr : has_repr register := ⟨register_to_string⟩

inductive operand
  | register : register -> operand
  | segment  : option register -> register -> operand
  | immediate : ℕ -> ℕ -> operand
  | rel_immediate : ℕ -> ℕ -> ℕ -> operand
  | memloc : option register -> option register -> ℕ -> option register -> ℕ -> operand

def operand_to_string : operand -> string
  | (operand.register r) := repr r
  | (operand.segment s r)    := "(" ++ repr s ++ ":" ++ repr r ++ ")"
  | (operand.immediate n v)  := repr v ++ "[" ++ repr n ++ "]"
  | (operand.rel_immediate off n v) := "(" ++ repr v ++ " + " ++ repr off ++ ")[" ++ repr n ++ "]"
  | (operand.memloc seg b s i d)    := "(" ++ repr seg ++ ":" ++ repr b ++ " + " ++ repr s ++ "*" ++ repr i ++ " + " ++ repr d ++ ")"

instance operand_has_repr : has_repr operand := ⟨operand_to_string⟩

structure instruction :=
  (mnemonic : string)
  (operands : list operand)

instance instruction_has_repr : has_repr instruction := ⟨λi, i.mnemonic ++ " " ++ repr i.operands⟩

structure unknown_byte :=
  (byte : ℕ)
  (bytes_tried : ℕ)

instance unknown_bytes_has_repr : has_repr unknown_byte := ⟨λi, "???" ++ repr i.byte ++ "(" ++ repr i.bytes_tried ++ ")"⟩

def document := list (ℕ × sum unknown_byte instruction)
instance document_has_repr : has_repr document := ⟨ string.intercalate "\n" ∘ list.map repr  ⟩

structure parser (a : Type) :=
  (run : list sexp -> option (a × list sexp))

instance : functor parser := 
  { map := λa b (f : a -> b) (p : parser a),
              {run := λs, (λ(x : a × (list sexp)), (f x.fst, x.snd)) <$> p.run s } }

instance : has_pure parser :=
  { pure := λa (v : a), { run := λs, some (v, s) } }

instance : has_seq parser :=
  { seq := λa b (f : parser (a -> b)) (p : parser a), 
        {run := λs, match f.run s with
                      | none := none
                      | (some (g, s')) := (g <$> p).run s'
                    end } 
  }

instance : applicative parser := {}

instance : alternative parser :=
  { failure := λa, { run := λs, none }
  , orelse  := λa (p q : parser a), { run := λs, p.run s <|> q.run s }
  }

def run_parser {a} (p : parser a) (s : sexp) : option (a × list sexp) := p.run [s]
def exec_parser {a} (p : parser a) (s : sexp) : option a :=
    (λ(x : a × list sexp), x.fst) <$> run_parser p s

namespace parser

def atomp {a} (f : string -> option a) : parser a :=
    { run := λs, match s with 
                 | (sexp.atom a :: rest) := (λv, (v, rest)) <$> f a
                 | _ := none
                 end 
    }

def listp {a} (p : parser a) : parser a :=
    { run := λs, match s with
                 | (sexp.list s' :: rest) := 
                   match p.run s' with
                   | some (v, []) := some (v, rest)
                   | _ := none
                   end
                 | _ := none
                 end
    }

-- If p consumes no input, it returns the empty list.
--
--  FIXME: this is slooooow, mainly due to calculating length all the
-- time.  We could calcuate this as we go... i.e, parser a is now:
-- Π(s : list s), option { val : a, rest : list s, n : ℕ, pf : n = length s - length rest }

def raw_many {a} (p : parser a) : list sexp -> option (list a × list sexp) :=
  well_founded.fix (measure_wf list.length) 
                   (λs f, match p.run s with
                          | none         := some ([], s)
                          | some (v, s') := if h : list.length s' < list.length s 
                                            then (λ(r : list a × list sexp), (v :: r.fst, r.snd)) <$> f s' h
                                            else some ([], s)
                          end
                   )

def manyp {a} (p : parser a) : parser (list a) := { run := raw_many p }

def stringp (s : string) : parser string := atomp (λs', if s = s' then some s' else none)

def taggedp {a} (tag : string) (p : parser a) : parser a := listp (stringp tag *> p)

/- FIXME: check all digits -/
def natp := atomp (λs, some (string.to_nat s))
  
def anyatomp : parser string := atomp some

def registerp : parser register :=
  taggedp "register" (register.mk <$> anyatomp <*> anyatomp <*> natp <*> natp)

-- def operandp : parser operand :=
  
def option_registerp : parser (option register) :=
    (pure none <* stringp "no-register") <|> (some <$> registerp)

def operandp : parser operand :=
  (operand.register <$> registerp)
  <|> (taggedp "segment-index" (operand.segment <$> option_registerp <*> registerp))
  <|> (taggedp "immediate" (operand.immediate <$> natp <*> natp))
  <|> (taggedp "rel-immediate" (operand.rel_immediate <$> natp <*> natp <*> natp))
  <|> (taggedp "memloc" (operand.memloc <$> option_registerp <*> option_registerp <*> natp <*> option_registerp <*> natp))
    
def instructionp : parser instruction :=
  taggedp "instruction" (instruction.mk <$> anyatomp <*> manyp operandp)

def unknown_bytep : parser unknown_byte :=
  taggedp "unknown-byte" (unknown_byte.mk <$> natp <*> natp)

def entryp : parser (ℕ × sum unknown_byte instruction) :=
  listp ((λoff _ i, (off, i)) <$> natp <*> natp <*> 
                                  ((sum.inl <$> unknown_bytep) <|> (sum.inr <$> instructionp)))

def documentp : parser document := listp (manyp entryp)

/-
def get_sexp : string -> sexp := λst, 
    match sexp.from_string st with
      | (sum.inr s) := s
      | _ := sorry
    end

#eval get_sexp "(rel-immediate 7823 4 18446744073709542481)"

#eval (exec_parser instructionp (get_sexp "(instruction CALL64pcrel32 (rel-immediate 7823 4 18446744073709542481))"))

def foo : string := 
"((7691 3 (instruction SETNEr (register RAX AL 8 0)))
  (7694 1 (instruction RETQ))
  (7695 1 (instruction NOOP))
  (7696 4 (instruction SUB64ri8 (register RSP RSP 0 0) (register RSP RSP 0 0) (immediate 1 24)))
  (7700 7 (instruction LEA64r (register R8 R8 0 0) (memloc no-register (register RIP RIP 0 0) 1 no-register 73631)))
  (7707 2 (instruction XOR32rr (register RDX EDX 32 0) (register RDX EDX 32 0) (register RDX EDX 32 0)))
  (7709 2 (instruction XOR32rr (register RSI ESI 32 0) (register RSI ESI 32 0) (register RSI ESI 32 0)))
  (7711 3 (instruction MOV64rr (register RCX RCX 0 0) (register RSP RSP 0 0)))
  (7714 9 (instruction MOV64rm (register RAX RAX 0 0) (memloc (register FS FS 0 0) no-register 1 no-register 40)))
  (7723 5 (instruction MOV64mr (memloc no-register (register RSP RSP 0 0) 1 no-register 8) (register RAX RAX 0 0)))
  (7728 2 (instruction XOR32rr (register RAX EAX 32 0) (register RAX EAX 32 0) (register RAX EAX 32 0)))
  (7730 5 (instruction CALL64pcrel32 (rel-immediate 7735 4 61785)))
  (7735 2 (instruction TEST32rr (register RAX EAX 32 0) (register RAX EAX 32 0)))
  (7737 2 (instruction JE_1 (rel-immediate 7739 1 61)))
  (7739 3 (instruction CMP32ri8 (register RAX EAX 32 0) (immediate 1 1)))
  (7742 2 (instruction JE_1 (rel-immediate 7744 1 32)))
  (7744 2 (instruction XOR32rr (register RAX EAX 32 0) (register RAX EAX 32 0) (register RAX EAX 32 0)))
  (7746 5 (instruction MOV64rm (register RDX RDX 0 0) (memloc no-register (register RSP RSP 0 0) 1 no-register 8)))
  (7751 9 (instruction XOR64rm (register RDX RDX 0 0) (register RDX RDX 0 0) (memloc (register FS FS 0 0) no-register 1 no-register 40)))
  (7760 2 (instruction JNE_1 (rel-immediate 7762 1 56)))
  (7762 4 (instruction ADD64ri8 (register RSP RSP 0 0) (register RSP RSP 0 0) (immediate 1 24)))
  (7766 1 (instruction RETQ))
  (7767 9 (instruction NOOPW (memloc no-register (register RAX RAX 0 0) 1 (register RAX RAX 0 0) 0)))
  (7776 11 (instruction MOV64mi32 (memloc no-register (register RIP RIP 0 0) 1 no-register 2209205) (immediate 4 18446744073709551615)))
  (7787 5 (instruction MOV32ri (register RAX EAX 32 0) (immediate 4 1)))
  (7792 2 (instruction JMP_1 (rel-immediate 7794 1 18446744073709551568)))
  (7794 6 (instruction NOOPW (memloc no-register (register RAX RAX 0 0) 1 (register RAX RAX 0 0) 0)))
  (7800 4 (instruction MOV64rm (register RAX RAX 0 0) (memloc no-register (register RSP RSP 0 0) 1 no-register 0)))
  (7804 7 (instruction MOV64mr (memloc no-register (register RIP RIP 0 0) 1 no-register 2209181) (register RAX RAX 0 0)))
  (7811 5 (instruction MOV32ri (register RAX EAX 32 0) (immediate 4 1)))
  (7816 2 (instruction JMP_1 (rel-immediate 7818 1 18446744073709551544)))
  (7818 5 (instruction CALL64pcrel32 (rel-immediate 7823 4 18446744073709542481))))"

#eval (exec_parser documentp (get_sexp foo))



#eval bar
-/

end parser

def from_buffer (buf : char_buffer) : sum string document :=
  match sexp.from_buffer buf with
  | (sum.inl e) := sum.inl e
  | (sum.inr r) := match exec_parser parser.documentp r with
                   | none := sum.inl "Couldn't parse instructions"
                   | (some d) := sum.inr d
                   end
  end

end decodex86
