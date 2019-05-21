
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

-- We don't care about most of these.
-- static const char * oNArr[] = {
--     "AVX512ICC",
--     "AVX512RC",
--     "AVXCC",
--     "BNDR",
--     "CCR",
--     "CONTROL_REG",
--     "DEBUG_REG",
--     "DFCCR",
--     "FPCCR",
--     "FR32",
--     "FR32X",
--     "FR64",
--     "FR64X",
--     "GR16",
--     "GR16_ABCD",
--     "GR16_NOREX",
--     "GR32",
--     "GR32_ABCD",
--     "GR32_AD",
--     "GR32_NOREX",
--     "GR32_NOREX_NOSP",
--     "GR32_NOSP",
--     "GR32_TC",
--     "GR32orGR64",
--     "GR64",
--     "GR64_ABCD",
--     "GR64_AD",
--     "GR64_NOREX",
--     "GR64_NOREX_NOSP",
--     "GR64_NOSP",
--     "GR64_TC",
--     "GR64_TCW64",
--     "GR8",
--     "GR8_ABCD_H",
--     "GR8_ABCD_L",
--     "GR8_NOREX",
--     "GRH16",
--     "GRH8",
--     "LOW32_ADDR_ACCESS",
--     "LOW32_ADDR_ACCESS_RBP",
--     "RFP32",
--     "RFP64",
--     "RFP80",
--     "RST",
--     "SEGMENT_REG",
--     "SSECC",
--     "VK1",
--     "VK16",
--     "VK16WM",
--     "VK1WM",
--     "VK2",
--     "VK2WM",
--     "VK32",
--     "VK32WM",
--     "VK4",
--     "VK4WM",
--     "VK64",
--     "VK64WM",
--     "VK8",
--     "VK8WM",
--     "VR128",
--     "VR128H",
--     "VR128L",
--     "VR128X",
--     "VR256",
--     "VR256H",
--     "VR256L",
--     "VR256X",
--     "VR512",
--     "VR64",
--     "XOPCC",
--     "anymem",
--     "brtarget",
--     "brtarget16",
--     "brtarget32",
--     "brtarget8",
--     "dstidx16",
--     "dstidx32",
--     "dstidx64",
--     "dstidx8",
--     "f128mem",
--     "f256mem",
--     "f32imm",
--     "f32mem",
--     "f512mem",
--     "f64imm",
--     "f64mem",
--     "f80mem",
--     "i128mem",
--     "i16i8imm",
--     "i16imm",
--     "i16imm_pcrel",
--     "i16mem",
--     "i1imm",
--     "i256mem",
--     "i32i8imm",
--     "i32imm",
--     "i32imm_pcrel",
--     "i32mem",
--     "i32mem_TC",
--     "i32u8imm",
--     "i512mem",
--     "i64i32imm",
--     "i64i32imm_pcrel",
--     "i64i8imm",
--     "i64imm",
--     "i64mem",
--     "i64mem_TC",
--     "i8imm",
--     "i8mem",
--     "i8mem_NOREX",
--     "lea64_32mem",
--     "lea64mem",
--     "offset16_16",
--     "offset16_32",
--     "offset16_8",
--     "offset32_16",
--     "offset32_32",
--     "offset32_64",
--     "offset32_8",
--     "offset64_16",
--     "offset64_32",
--     "offset64_64",
--     "offset64_8",
--     "opaquemem",
--     "ptype0",
--     "ptype1",
--     "ptype2",
--     "ptype3",
--     "ptype4",
--     "ptype5",
--     "sdmem",
--     "srcidx16",
--     "srcidx32",
--     "srcidx64",
--     "srcidx8",
--     "ssmem",
--     "type0",
--     "type1",
--     "type2",
--     "type3",
--     "type4",
--     "type5",
--     "u8imm",
--     "v512mem",
--     "vx128mem",
--     "vx128xmem",
--     "vx256mem",
--     "vx256xmem",
--     "vx64mem",
--     "vx64xmem",
--     "vy128mem",
--     "vy128xmem",
--     "vy256mem",
--     "vy256xmem",
--     "vy512xmem",
--     "vz256mem",
--     "vz512mem",
--     "ptr_rc",
--     "ptr_rc_norex",
--     "ptr_rc_norex_nosp",
--     "ptr_rc_nosp",
--     "ptr_rc_tailcall",
--     "unknown",
--     "variable_ops"
-- };

inductive operand_type 
  | mem : ℕ -> operand_type
  | other : operand_type

def operand_type_to_string : operand_type -> string
  | (operand_type.mem n) := "(mem " ++ repr n ++ ")"
  | (operand_type.other) := "other"

instance operand_type_has_repr : has_repr operand_type := ⟨operand_type_to_string⟩

inductive operand_value
  | register : register -> operand_value
  | segment  : option register -> register -> operand_value
  | immediate : ℕ -> ℕ -> operand_value
  | rel_immediate : ℕ -> ℕ -> ℕ -> operand_value
  | memloc : option register -> option register -> ℕ -> option register -> ℕ -> operand_value

def operand_value_to_string : operand_value -> string
  | (operand_value.register r) := repr r
  | (operand_value.segment s r)    := "(" ++ repr s ++ ":" ++ repr r ++ ")"
  | (operand_value.immediate n v)  := repr v ++ "[" ++ repr n ++ "]"
  | (operand_value.rel_immediate off n v) := "(" ++ repr v ++ " + " ++ repr off ++ ")[" ++ repr n ++ "]"
  | (operand_value.memloc seg b s i d)  := "(" ++ repr seg ++ ":" ++ repr b ++ " + " ++ repr s ++ "*" ++ repr i ++ " + " ++ repr d ++ ")"

instance operand_value_has_repr : has_repr operand_value := ⟨operand_value_to_string⟩

structure operand := 
  (type  : operand_type)
  (value : operand_value)

def operand_to_string : operand -> string := λop, 
  "(" ++ repr op.value ++ " :: " ++ repr op.type ++ ")"

instance operand_has_repr : has_repr operand := ⟨operand_to_string⟩

structure instruction :=
  (nbytes   : ℕ)
  (mnemonic : string)
  (operands : list operand)

instance instruction_has_repr : has_repr instruction := ⟨λi, i.mnemonic ++ " " ++ repr i.operands⟩

structure unknown_byte :=
  (byte : ℕ)
  (bytes_tried : ℕ)

instance unknown_bytes_has_repr : has_repr unknown_byte := ⟨λi, "???" ++ repr i.byte ++ "(" ++ repr i.bytes_tried ++ ")"⟩

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

def operand_valuep : parser operand_value :=
  (operand_value.register <$> registerp)
  <|> (taggedp "segment-index" (operand_value.segment <$> option_registerp <*> registerp))
  <|> (taggedp "immediate" (operand_value.immediate <$> natp <*> natp))
  <|> (taggedp "rel-immediate" (operand_value.rel_immediate <$> natp <*> natp <*> natp))
  <|> (taggedp "memloc" (operand_value.memloc <$> option_registerp <*> option_registerp <*> natp <*> option_registerp <*> natp))

-- FIXME: some of these could be autogenerated?
def operand_typep : parser operand_type :=
  let memp n sz := stringp n *> pure (operand_type.mem sz) 
  in  memp "anymem"       0 -- ??
  <|> memp "f128mem"      128
  <|> memp "f256mem"      256
  <|> memp "f32mem"       32
  <|> memp "f512mem"      512
  <|> memp "f64mem"       64
  <|> memp "f80mem"       80 --??
  <|> memp "i128mem"      128
  <|> memp "i16mem"       16
  <|> memp "i256mem"      256
  <|> memp "i32mem"       32
  <|> memp "i32mem_TC"    32
  <|> memp "i512mem"      512
  <|> memp "i64mem"       64
  <|> memp "i64mem_TC"    64
  <|> memp "i8mem"        8
  <|> memp "i8mem_NOREX"  8
--  <|> memp "lea64_32mem"  
  <|> memp "lea64mem"     64
--  <|> memp "opaquemem",
  <|> memp "sdmem"        64
  <|> memp "ssmem"        32
  <|> memp "v512mem"      512
  <|> memp "vx128mem"     128
  <|> memp "vx128xmem"    128
  <|> memp "vx256mem"     256
  <|> memp "vx256xmem"    256
  <|> memp "vx64mem"      64
  <|> memp "vx64xmem"     64
  <|> memp "vy128mem"     128
  <|> memp "vy128xmem"    128
  <|> memp "vy256mem"     256
  <|> memp "vy256xmem"    256
  <|> memp "vy512xmem"    512
  <|> memp "vz256mem"     256
  <|> memp "vz512mem"     512
  <|> (anyatomp *> pure operand_type.other)

def operandp : parser operand :=
  listp (operand.mk <$> operand_typep <*> operand_valuep)
    
def instructionp : parser instruction :=
  taggedp "instruction" (instruction.mk <$> natp <*> anyatomp <*> manyp operandp)

def unknown_bytep : parser unknown_byte :=
  taggedp "unknown-byte" (unknown_byte.mk <$> natp <*> natp)

def entryp : parser (sum unknown_byte instruction) :=
  (sum.inl <$> unknown_bytep) <|> (sum.inr <$> instructionp)

end parser

def from_buffer (buf : char_buffer) : sum string (sum unknown_byte instruction) :=
  match sexp.from_buffer buf with
  | (sum.inl e) := sum.inl e
  | (sum.inr r) := match exec_parser parser.entryp r with
                   | none := sum.inl "Couldn't parse instructions"
                   | (some d) := sum.inr d
                   end
  end

end decodex86
