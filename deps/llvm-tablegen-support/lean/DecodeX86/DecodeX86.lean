
import Std.Data.RBMap
open Std (RBMap)

namespace decodex86

@[reducible]
def regN := String

structure register :=
  (top : regN)
  (reg : regN)
  (width : Nat)
  (offset : Nat)

def register_to_String : register -> String := fun r =>
  String.intercalate " " ["(", "R", r.top, r.reg, reprStr r.width, reprStr r.offset, ")"]

-- FIXME: behave wrt prec
instance register_has_repr : Repr register := ⟨fun r _n => register_to_String r⟩

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
  | mem : Nat -> operand_type
  | other : operand_type

def operand_type_to_String : operand_type -> String
  | (operand_type.mem n) => "(mem " ++ reprStr n ++ ")"
  | (operand_type.other) => "other"

-- FIXME: behave wrt prec
instance operand_type_has_repr : Repr operand_type := ⟨fun op _n => operand_type_to_String op⟩

inductive operand_value
  | register : register -> operand_value
  | segment  : Option register -> register -> operand_value
  | immediate : Nat -> Nat -> operand_value
  | rel_immediate : Nat -> Nat -> Nat -> operand_value
  | memloc : Option register -> Option register -> Nat -> Option register -> Nat -> operand_value

def operand_value_to_String : operand_value -> String
  | (operand_value.register r) => reprStr r
  | (operand_value.segment s r)    => "(" ++ reprStr s ++ ":" ++ reprStr r ++ ")"
  | (operand_value.immediate n v)  => reprStr v ++ "[" ++ reprStr n ++ "]"
  | (operand_value.rel_immediate off n v) => "(" ++ reprStr v ++ " + " ++ reprStr off ++ ")[" ++ reprStr n ++ "]"
  | (operand_value.memloc seg b s i d)  => "(" ++ reprStr seg ++ ":" ++ reprStr b ++ " + " ++ reprStr s ++ "*" ++ reprStr i ++ " + " ++ reprStr d ++ ")"

-- FIXME: behave wrt prec
instance operand_value_has_repr : Repr operand_value := ⟨fun ov _n => operand_value_to_String ov⟩

structure operand := 
  (type  : operand_type)
  (value : operand_value)

def operand_to_String : operand -> String := fun op =>
  "(" ++ reprStr op.value ++ " :: " ++ reprStr op.type ++ ")"

-- FIXME: behave wrt prec
instance operand_has_repr : Repr operand := ⟨fun op _n => operand_to_String op⟩

structure instruction :=
  (nbytes   : Nat)
  (mnemonic : String)
  (operands : List operand)

-- FIXME: behave wrt prec
instance instruction_has_repr : Repr instruction := 
  ⟨fun i _n => i.mnemonic ++ " " ++ repr i.operands⟩

structure unknown_byte :=
  (byte : Nat)
  (bytes_tried : Nat)

-- FIXME: behave wrt prec
instance unknown_bytes_has_repr : Repr unknown_byte := ⟨fun i _n => coe ("???" ++ reprStr i.byte ++ "(" ++ reprStr i.bytes_tried ++ ")")⟩

def operand_memtyp_map : RBMap String Nat (fun s1 s2 => decide (s1 < s2)) :=
  List.foldl (fun m (v : String × Nat) => m.insert v.fst v.snd) 
       Std.RBMap.empty
       [("anymem"       , 0  )   -- ??
       ,("f128mem"      , 128) 
       ,("f256mem"      , 256) 
       ,("f32mem"       , 32 ) 
       ,("f512mem"      , 512) 
       ,("f64mem"       , 64 ) 
       ,("f80mem"       , 80 )    --??
       ,("i128mem"      , 128) 
       ,("i16mem"       , 16 ) 
       ,("i256mem"      , 256) 
       ,("i32mem"       , 32 ) 
       ,("i32mem_TC"    , 32 ) 
       ,("i512mem"      , 512) 
       ,("i64mem"       , 64 ) 
       ,("i64mem_TC"    , 64 ) 
       ,("i8mem"        , 8  ) 
       ,("i8mem_NOREX"  , 8  ) 
       ,("lea64mem"     , 64 ) 
       ,("lea64_32mem"  , 64 ) 
       ,("sdmem"        , 64 ) 
       ,("ssmem"        , 32 ) 
       ,("v512mem"      , 512) 
       ,("vx128mem"     , 128) 
       ,("vx128xmem"    , 128) 
       ,("vx256mem"     , 256) 
       ,("vx256xmem"    , 256) 
       ,("vx64mem"      , 64 ) 
       ,("vx64xmem"     , 64 ) 
       ,("vy128mem"     , 128) 
       ,("vy128xmem"    , 128) 
       ,("vy256mem"     , 256) 
       ,("vy256xmem"    , 256) 
       ,("vy512xmem"    , 512) 
       ,("vz256mem"     , 256) 
       ,("vz512mem"     , 512) 
       ]

def operand_memtyp (tp : String) : operand_type :=
  match operand_memtyp_map.find? tp with 
  | (some n) => operand_type.mem n
  | none     => operand_type.other

-- Exported (to CPP) functions
@[export decodex86_exported_mk_reg]
def mk_reg (top : String) (reg : String) (width : Nat) (offset : Nat) : register :=
    register.mk top reg width offset

@[export decodex86_exported_mk_some_reg]
def mk_some_reg (r : register) : Option register := Option.some r

@[export decodex86_exported_mk_none_reg]
def mk_none_reg : Option register := Option.none

@[export decodex86_exported_mk_operand_register]
def mk_operand_register (tp : String) (r : register) : operand :=
    operand.mk (operand_memtyp tp) (operand_value.register r)

@[export decodex86_exported_mk_operand_segment]
def mk_operand_segment (tp : String) (seg : Option register) (r : register) : operand :=
    operand.mk (operand_memtyp tp) (operand_value.segment seg r)

@[export decodex86_exported_mk_operand_immediate]
def mk_operand_immediate (tp : String) (n : Nat) (v : Nat) : operand :=
    operand.mk (operand_memtyp tp) (operand_value.immediate n v)

@[export decodex86_exported_mk_operand_rel_immediate]
def mk_operand_rel_immediate (tp : String) (off : Nat) (n : Nat) (v : Nat) : operand :=
    operand.mk (operand_memtyp tp) (operand_value.rel_immediate off n v)

@[export decodex86_exported_mk_operand_memloc]
def mk_operand_memloc (tp : String) (seg : Option register) (b : Option register) (s : Nat) (i : Option register) (d : Nat) :=
    operand.mk (operand_memtyp tp) (operand_value.memloc seg b s i d)

@[export decodex86_exported_mk_instruction_0]
def mk_instruction_0 (n : Nat) (m : String) : instruction :=
  instruction.mk n m []

@[export decodex86_exported_mk_instruction_1]
def mk_instruction_1 (n : Nat) (m : String) (o1 : operand) : instruction :=
  instruction.mk n m [o1]

@[export decodex86_exported_mk_instruction_2]
def mk_instruction_2 (n : Nat) (m : String) (o1 : operand) (o2 : operand) : instruction :=
  instruction.mk n m [o1, o2]

@[export decodex86_exported_mk_instruction_3]
def mk_instruction_3 (n : Nat) (m : String) (o1 : operand) (o2 : operand) (o3 : operand) : instruction :=
  instruction.mk n m [o1, o2, o3]

-- Handling the result of decoding
@[reducible]
def decode_result := Sum Nat instruction

@[export decodex86_exported_mk_decode_success]
def mk_decode_success (i : instruction) : decode_result := Sum.inr i

@[export decodex86_exported_mk_decode_failure]
def mk_decode_failure (nbytes : Nat) : decode_result := Sum.inl nbytes

namespace prim

-- Imported (FFI) functions
@[extern "vadd_decode"]
def decode ( b : @& ByteArray ) (offset : @& Nat) : decode_result := arbitrary

end prim

structure decoder :=
  (bytes : ByteArray)
  (vaddr : Nat)

def mk_decoder (bs : ByteArray) (v : Nat) : decoder :=
  decoder.mk bs v

def decode (d : decoder) (v : Nat) : decode_result :=
  if v < d.vaddr 
  then Sum.inl 0
  else prim.decode d.bytes (v - d.vaddr)

end decodex86
