/-
This file contains the start of an Elf parser for Lean.  It currently has facilities for parsing
Elf
-/
-- import system.io
-- import init.category.reader
import Init.Control.State
import Std.Data.RBMap
import X86Semantics.MachineMemory
import X86Semantics.BufferMap
-- import .file_input
import Galois.Init.Io
import Galois.Init.Nat

def repeat {α : Type} {m : Type → Type} [Applicative m] : Nat → m α → m (List α)
| 0, m => pure []
| (Nat.succ n),  m => List.cons <$> m <*> repeat n m

def forM' {m : Type → Type} [Monad m] {α : Type} {β:Type} (l:List α) (f:α → m β) : m Unit :=
  List.mapM f l >>= fun _ => pure ()

def bracket {α β:Type} (c:IO α) (d:α → IO Unit) (f:α → IO β) : IO β := do
  x ← c;
  v <- catch (f x) (fun e => do d x; throw e);
  d x;
  pure v

-- @[reducible]
-- def uint8 := fin (nat.succ 0xff)

-- @[reducible]
-- def uint16 := fin (nat.succ 0xffff)

-- @[reducible]
-- def uint32 := fin (nat.succ 0xffffffff)

-- @[reducible]
-- def uint64 := fin (nat.succ 0xffffffffffffffff)


namespace ByteArray

protected
def toBytesPartialAux (bs : ByteArray) (off : Nat) : Nat -> List UInt8 -> List UInt8
  | 0,            acc => acc
  | (Nat.succ n), acc => toBytesPartialAux n (bs.get! (off + n)  :: acc)

def toBytesPartial (bs : ByteArray) (off : Nat) (n : Nat) : List UInt8 := 
  ByteArray.toBytesPartialAux bs off n []

-- FIXME: this is not a cheap way of doing this.
def append (b : ByteArray) (b' : ByteArray) : ByteArray :=
  ByteArray.mk (Array.append b.data b'.data)

end ByteArray

namespace buffer

@[reducible]
def reader := EStateM String (ByteArray × Nat)

namespace reader

protected
def read_bytes (n:Nat) : reader (List UInt8) := do
  s ← get;
  when (s.fst.size < s.snd + n) (throw "read_bytes eof");
  set { s with snd := s.snd + n };
  pure (s.fst.toBytesPartial s.snd n)

def skip (n:Nat) : reader Unit := do
  s ← get;
  when (s.fst.size < s.snd + n) (throw "skip eof");
  set { s with snd := s.snd + n }

def read_UInt8 : reader UInt8 := do
  l ← reader.read_bytes 1;
  match l with
  | [h] => pure h
  | _   => throw "internal: read_UInt8"

def from_handle {α} (h:Galois.Fs.handle) (n:Nat) (r:reader α) : IO α := do
  b ← Galois.IO.Prim.handle.read h n;
  match r.run (b, 0) with
  | (EStateM.Result.ok r _)    => pure r
  | (EStateM.Result.error e _) => throw (IO.userError e)

end reader
end buffer

namespace elf

def magic : List UInt8 := [0x7f, 0x45, 0x4c, 0x46 ] -- 'E' 'L' 'F'

inductive elf_class
| ELF32 : elf_class
| ELF64 : elf_class

namespace elf_class

protected def repr : elf_class → String
| ELF32 => "ELF32"
| ELF64 => "ELF64"

protected def bytes : elf_class → Nat
| ELF32 => 4
| ELF64 => 8

protected def bits : elf_class → Nat
| ELF32 => 32
| ELF64 => 64

end elf_class

inductive elf_data
| ELFDATA2LSB : elf_data
| ELFDATA2MSB : elf_data

namespace elf_data

protected def repr : elf_data → String
| ELFDATA2LSB => "ELFDATA2LSB"
| ELFDATA2MSB => "ELFDATA2MSB"

end elf_data

open elf_class
open elf_data

structure osabi :=
(val : UInt8)

namespace osabi

protected def repr (o:osabi) : String :=
  if o.val = 0 
  then "UNIX - System V"
  else repr o.val.toNat

protected def toString (o:osabi) : String := repr o.val.toNat

instance : HasToString osabi := ⟨osabi.toString⟩

instance : HasBeq osabi := ⟨λ x y => x.val == y.val⟩

def lt (o1 o2 : osabi) : Bool := o1.val < o2.val

/-- Elf OSABI constants --/
-- | No extensions or unspecified
def ELFOSABI_SYSV := osabi.mk 0
-- | Hewlett-Packard HP-UX
def ELFOSABI_HPUX := osabi.mk 1
-- | NetBSD
def ELFOSABI_NETBSD := osabi.mk 2
-- | Linux
def ELFOSABI_LINUX := osabi.mk 3
-- | Sun Solaris
def ELFOSABI_SOLARIS := osabi.mk 6
-- | AIX
def ELFOSABI_AIX := osabi.mk 7
-- | IRIX
def ELFOSABI_IRIS := osabi.mk 8
-- | FreeBSD
def ELFOSABI_FREEBSD := osabi.mk 9
-- | Compat TRU64 Unix
def ELFOSABI_TRU64 := osabi.mk 10
-- | Novell Modesto
def ELFOSABI_MODESTO := osabi.mk 11
-- | Open BSD
def ELFOSABI_OPENBSD := osabi.mk 12
-- | Open VMS
def ELFOSABI_OPENVMS := osabi.mk 13
-- | Hewlett-Packard Non-Stop Kernel
def ELFOSABI_NSK := osabi.mk 14
-- | Amiga Research OS
def ELFOSABI_AROS := osabi.mk 15
-- | ARM
def ELFOSABI_ARM := osabi.mk 97
-- | Standalone (embedded) application
def ELFOSABI_STANDALONE := osabi.mk 255


private def nameMap : RBMap osabi String osabi.lt :=
RBMap.fromList
  [ (ELFOSABI_SYSV, "SYSV")
  , (ELFOSABI_HPUX, "HPUX")
  , (ELFOSABI_NETBSD, "NETBSD")
  , (ELFOSABI_LINUX, "LINUX")
  , (ELFOSABI_SOLARIS, "SOLARIS")
  , (ELFOSABI_AIX, "AIX")
  , (ELFOSABI_IRIS, "IRIS")
  , (ELFOSABI_FREEBSD, "FREEBSD")
  , (ELFOSABI_TRU64, "TRU64")
  , (ELFOSABI_MODESTO, "MODESTO")
  , (ELFOSABI_OPENBSD, "OPENBSD")
  , (ELFOSABI_OPENVMS, "OPENVMS")
  , (ELFOSABI_NSK, "NSK")
  , (ELFOSABI_AROS, "AROS")
  , (ELFOSABI_ARM, "ARM")
  , (ELFOSABI_STANDALONE, "STANDALONE")
  ]
  osabi.lt

def name (o:osabi) : String := nameMap.findD o ("UNKNOWN("++o.val.toNat.repr++")")

end osabi

/-- Information from first 16-bytes of Elf file (allows reading rest of file)
    sans elf_class since we track that separately to index types. --/
structure info :=
(elf_class : elf_class)
(elf_data  : elf_data)
(osabi : osabi)
(abi_version : UInt8)

namespace info

protected def pp (e:info) : String
  := "Class:                             " ++ e.elf_class.repr ++ "\n"
  ++ "Data:                              " ++ e.elf_data.repr ++ "\n"
  ++ "OS/ABI:                            " ++ e.osabi.repr ++ "\n"
  ++ "ABI Version:                       " ++ repr e.abi_version.toNat ++ "\n"

open buffer

def read : reader info := do
  b ← reader.read_bytes 4;
  when (b ≠ magic) (throw "Not an elf file.");
  cl_val ← reader.read_UInt8;
  cl ←
    (match cl_val.toNat with
    | 1 => pure ELF32
    | 2 => pure ELF64
    | _ => throw "Invalid elf data.");
  dt_val ← reader.read_UInt8;
  dt ←
    (match dt_val.toNat with
    | 1 => pure ELFDATA2LSB
    | 2 => pure ELFDATA2MSB
    | _ => throw "Invalid elf data.");
  elf_version ← reader.read_UInt8;
  when (elf_version ≠ 1) (throw "Mismatched elf version.");
  osabi ← reader.read_UInt8;
  osabi_ver ← reader.read_UInt8;
  pure { elf_class := cl
       , elf_data := dt
       , osabi := ⟨osabi⟩
       , abi_version := osabi_ver
       }

end info

-- A reader for elf files
@[reducible]
def file_reader := ReaderT info buffer.reader

namespace file_reader

protected
def from_handle {α:Type} (i:info) (h:Galois.Fs.handle) (n:Nat) (r:file_reader α) : IO α := do
  b ← Galois.IO.Prim.handle.read h n;
  match (r.run i).run (b, 0) with
  | (EStateM.Result.ok r _)    => pure r
  | (EStateM.Result.error e _) => throw (IO.userError e)

def read_u8  : file_reader UInt8  :=
  ReaderT.lift $ buffer.reader.read_UInt8

protected
def read_chars_lsb (w:Nat) : file_reader (List UInt8) := do
  i ← read;
  let f (l:List UInt8) : List UInt8 :=
        match i.elf_data with
        | ELFDATA2LSB => l
        | ELFDATA2MSB => l.reverse;
        do
  ReaderT.lift $ f <$> buffer.reader.read_bytes w

def read_u16 : file_reader UInt16 := do
  l ← file_reader.read_chars_lsb 2;
  match l with
  | [x0,x1] =>
    pure $ UInt16.ofNat
      $ Nat.shiftl x1.toNat 8
      + x0.toNat
  | _ => throw "internal: read_UInt16"

def read_u32 : file_reader UInt32 := do
  l ← file_reader.read_chars_lsb 4;
  match l with
  | [x0,x1,x2,x3] =>
    pure $ UInt32.ofNat
      $ Nat.shiftl x3.toNat 24
      + Nat.shiftl x2.toNat 16
      + Nat.shiftl x1.toNat 8
      + x0.toNat
  | _ => throw "internal: read_UInt32"


def read_u64 : file_reader UInt64 := do
  l ← file_reader.read_chars_lsb 8;
  match l with
  | [x0,x1,x2,x3, x4, x5, x6, x7] =>
    pure $ UInt64.ofNat
      $ Nat.shiftl x7.toNat 56
      + Nat.shiftl x6.toNat 48
      + Nat.shiftl x5.toNat 40
      + Nat.shiftl x4.toNat 32
      + Nat.shiftl x3.toNat 24
      + Nat.shiftl x2.toNat 16
      + Nat.shiftl x1.toNat 8
      + x0.toNat
  | _ => throw "internal: read_UInt64"
 

end file_reader

class elf_file_data (α:Type) :=
(read {} : file_reader α)

instance UInt16_si_elf_file_data : elf_file_data UInt16 :=
{ read := file_reader.read_u16 }

/- Elf defines a set of types depending on the class, e.g. Elf32_Word, Elf32_Addr, etc.  
   Some of these are independent of the class, e.g. Elf32_Word = Elf64_Word = UInt32.  
-/

-- A 32 or 64-bit word dependent on the class.
def word (c:elf_class) :=
  match c with 
  | ELF32 => UInt32
  | ELF64 => UInt64

namespace word

def toNat : ∀{c : elf_class}, word c -> Nat
| ELF32, v => UInt32.toNat v
| ELF64, v => UInt64.toNat v


protected def fromNat (c : elf_class) (n : Nat) : Option (word c) :=
match c with
| ELF32 => 
  (if h : n < uint32Sz 
   then some $ UInt32.ofNat' n h
   else Option.none)
| ELF64 => 
  (if _h : n < uint64Sz
   then Option.some $ UInt64.ofNat n
   else Option.none)



-- Print word as decinal
protected def pp_dec {c:elf_class} (w : word c) : String := repr w.toNat
  
--- Print word as hex
protected def pp_hex : ∀{c:elf_class}, word c → String
| ELF32, v => Nat.ppHex v.toNat
| ELF64, v => Nat.ppHex v.toNat

protected def size : elf_class → Nat := elf_class.bytes

-- theorem dbl_is_bit0 (x y:Nat) : bit0 x*y = bit0 (x*y) :=
-- begin
--   simp [bit0, nat.right_distrib];
-- end

--- `bit1_dec d x` is a utility function that denotes `(d+1)*x-1`
-- It is primarily used
def bit1_dec : Nat →  Nat → Nat
| d, x => (d+1)*x-1

-- theorem bit0_sub_1_congr (x:Nat)  : bit0 x - 1 = bit1_dec 1 x :=
-- begin
--   simp [bit1_dec, bit1, bit0, nat.add_succ, nat.succ_mul];
-- end

-- theorem bit1_dec_bit0 (d x:Nat) : bit1_dec d (bit0 x) = bit1_dec (bit1 d) x :=
-- begin
--   simp [bit1_dec, bit1, bit0, nat.add_succ, nat.succ_mul;
--         nat.left_distrib, nat.right_distrib];
-- end

-- theorem bit1_dec_one (d:Nat) : bit1_dec d 1 = d :=
-- begin
--   simp [bit1_dec];
-- end

-- theorem word32_is_UInt32 : UInt32 = word ELF32 :=
-- begin
--   simp [UInt32, word, elf_class.bits, has_pow.pow, nat.pow, dbl_is_bit0, bit0_sub_1_congr
--        , bit1_dec_bit0, bit1_dec_one];
-- end

-- theorem word64_is_UInt64 : UInt64 = word ELF64 :=
-- begin
--   simp [UInt32, word, elf_class.bits, has_pow.pow, nat.pow, dbl_is_bit0, bit0_sub_1_congr
--        , bit1_dec_bit0, bit1_dec_one];
-- end

instance (c:elf_class) : elf_file_data (word c) :=
{ read := do
  match c with
  | ELF32 => file_reader.read_u32
  | ELF64 => file_reader.read_u64
}

end word

------------------------------------------------------------------------
-- phdr

-- @[derive DecidableEq HasOne]
def phdr_type := UInt32

instance : DecidableEq phdr_type := inferInstanceAs (DecidableEq UInt32)
instance : HasOne phdr_type := inferInstanceAs (HasOne UInt32)

namespace phdr_type

instance : elf_file_data phdr_type :=
{ read := file_reader.read_u32 }

def repr (pht : phdr_type) : String :=
  match pht.toNat with
  | 0 => "PT_NULL"                
  | 1 => "PT_LOAD"                 
  | 2 => "PT_DYNAMIC"              
  | 3 => "PT_INTERP"               
  | 4 => "PT_NOTE"                 
  | 5 => "PT_SHLIB"                
  | 6 => "PT_PHDR"                 
  | _ => "PT_PROC " ++ repr pht.toNat

instance : HasRepr phdr_type := ⟨repr⟩

def PT_LOAD : phdr_type := 1

end phdr_type

/-- Flags for a program header. -/
-- @[derive DecidableEq]
def phdr_flags := UInt32
instance phdr_flags_DecidableEq: DecidableEq phdr_flags := inferInstanceAs (DecidableEq UInt32)

namespace phdr_flags

instance : elf_file_data phdr_flags :=
{ read := file_reader.read_u32 }

def repr (phfs : phdr_flags) :  String := repr phfs.toNat

instance : HasRepr phdr_flags := ⟨repr⟩

def has_X (f : phdr_flags) : Bool := f.toNat.test_bit 0
def has_W (f : phdr_flags) : Bool := f.toNat.test_bit 1
def has_R (f : phdr_flags) : Bool := f.toNat.test_bit 2

end phdr_flags

structure phdr (c : elf_class) :=
(phdr_type  : phdr_type)
(flags      : phdr_flags)
(offset     : word c)
(vaddr      : word c)
(paddr      : word c)
(filesz     : word c)
(memsz      : word c)
(align      : word c)

namespace phdr

def size (c:elf_class) : Nat := 8 + 6 * word.size c

protected def pp {c:elf_class} (x:phdr c)
  := "Type:             " ++ x.phdr_type.repr ++ "\n"
  ++ "Flags:            " ++ x.flags.repr ++ "\n"
  ++ "File Offset:      " ++ x.offset.pp_dec ++ "\n"
  ++ "Virtual Address:  " ++ x.vaddr.pp_hex ++ "\n"
  ++ "Physical Address: " ++ x.paddr.pp_hex ++ "\n"
  ++ "File Size:        " ++ x.filesz.pp_dec ++ "\n"
  ++ "Memory Size:      " ++ x.memsz.pp_dec ++ "\n"
  ++ "Alignment:        " ++ x.memsz.pp_hex ++ "\n"

end phdr

def read_phdr : ∀(c:elf_class), file_reader (phdr c)
| ELF32 => do
  tp ← elf_file_data.read;
  offset ← elf_file_data.read;
  vaddr  ← elf_file_data.read;
  paddr  ← elf_file_data.read;
  filesz ← elf_file_data.read;
  memsz  ← elf_file_data.read;
  flags ← elf_file_data.read;
  align  ← elf_file_data.read;
  pure { phdr_type := tp
       , flags := flags
       , offset := offset
       , vaddr  := vaddr
       , paddr  := paddr
       , filesz := filesz
       , memsz  := memsz
       , align := align
       }
| ELF64 => do
  tp ← elf_file_data.read;
  flags ← elf_file_data.read;
  offset ← elf_file_data.read;
  vaddr  ← elf_file_data.read;
  paddr  ← elf_file_data.read;
  filesz ← elf_file_data.read;
  memsz  ← elf_file_data.read;
  align  ← elf_file_data.read;
  pure { phdr_type := tp
       , flags := flags
       , offset := offset
       , vaddr  := vaddr
       , paddr  := paddr
       , filesz := filesz
       , memsz  := memsz
       , align := align
       }

------------------------------------------------------------------------
-- ehdr

/-- Elf file type -/
structure elf_type := 
(val : UInt16)

namespace elf_type

def NONE := elf_type.mk 0
def REL := elf_type.mk 1
def EXEC := elf_type.mk 2
def DYN := elf_type.mk 3
def CORE := elf_type.mk 4

instance : elf_file_data elf_type :=
{ read := file_reader.read_u16.map elf_type.mk }
end elf_type

/-- Elf header machine type. -/
structure machine := 
(val : UInt16)

namespace machine

instance : elf_file_data machine :=
{ read := file_reader.read_u16.map machine.mk }

instance : HasBeq machine := ⟨λ x y => x.val == y.val⟩

def lt (m1 m2 : machine) : Bool := m1.val < m2.val

def EM_NONE  := machine.mk 0
-- ^ No machine
def EM_M32  := machine.mk 1
-- ^ AT&T WE 32100
def EM_SPARC  := machine.mk 2
-- ^ SPARC
def EM_386  := machine.mk 3
-- ^ Intel 80386
def EM_68K  := machine.mk 4
-- ^ Motorola 68000
def EM_88K  := machine.mk 5
-- ^ Motorola 88000
def EM_486  := machine.mk 6
-- ^ Intel i486 (DO NOT USE THIS ONE)
def EM_860  := machine.mk 7
-- ^ Intel 80860
def EM_MIPS  := machine.mk 8
-- ^ MIPS I Architecture
def EM_S370  := machine.mk 9
-- ^ IBM System/370 Processor
def EM_MIPS_RS3_LE  := machine.mk 10
-- ^ MIPS RS3000 Little-endian
def EM_SPARC64  := machine.mk 11
-- ^ SPARC 64-bit
def EM_PARISC := machine.mk 15
-- ^ Hewlett-Packard PA-RISC
def EM_VPP500 := machine.mk 17
-- ^ Fujitsu VPP500
def EM_SPARC32PLUS := machine.mk 18
-- ^ Enhanced instruction set SPARC
def EM_960 := machine.mk 19
-- ^ Intel 80960
def EM_PPC := machine.mk 20
-- ^ PowerPC
def EM_PPC64 := machine.mk 21
-- ^ 64-bit PowerPC
def EM_S390  := machine.mk 22
-- ^ IBM System/390 Processor
def EM_SPU := machine.mk 23
-- ^ Cell SPU
def EM_V800  := machine.mk 36
-- ^ NEC V800
def EM_FR20  := machine.mk 37
-- ^ Fujitsu FR20
def EM_RH32  := machine.mk 38
-- ^ TRW RH-32
def EM_RCE   := machine.mk 39
-- ^ Motorola RCE
def EM_ARM   := machine.mk 40
-- ^ Advanced RISC Machines ARM
def EM_ALPHA := machine.mk 41
-- ^ Digital Alpha
def EM_SH    := machine.mk 42
-- ^ Hitachi SH
def EM_SPARCV9  := machine.mk 43
-- ^ SPARC Version 9
def EM_TRICORE  := machine.mk 44
-- ^ Siemens TriCore embedded processor
def EM_ARC      := machine.mk 45
-- ^ Argonaut RISC Core, Argonaut Technologies Inc.
def EM_H8_300   := machine.mk 46
-- ^ Hitachi H8/300
def EM_H8_300H  := machine.mk 47
-- ^ Hitachi H8/300H
def EM_H8S      := machine.mk 48
-- ^ Hitachi H8S
def EM_H8_500   := machine.mk 49
-- ^ Hitachi H8/500
def EM_IA_64    := machine.mk 50
-- ^ Intel IA-64 processor architecture
def EM_MIPS_X   := machine.mk 51
-- ^ Stanford MIPS-X
def EM_COLDFIRE := machine.mk 52
-- ^ Motorola ColdFire
def EM_68HC12   := machine.mk 53
-- ^ Motorola M68HC12
def EM_MMA      := machine.mk 54
-- ^ Fujitsu MMA Multimedia Accelerator
def EM_PCP      := machine.mk 55
-- ^ Siemens PCP
def EM_NCPU     := machine.mk 56
-- ^ Sony nCPU embedded RISC processor
def EM_NDR1     := machine.mk 57
-- ^ Denso NDR1 microprocessor
def EM_STARCORE := machine.mk 58
-- ^ Motorola Star*Core processor
def EM_ME16     := machine.mk 59
-- ^ Toyota ME16 processor
def EM_ST100    := machine.mk 60
-- ^ STMicroelectronics ST100 processor
def EM_TINYJ    := machine.mk 61
-- ^ Advanced Logic Corp. TinyJ embedded processor family
def EM_X86_64   := machine.mk 62
-- ^ AMD x86-64 architecture
def EM_PDSP     := machine.mk 63
-- ^ Sony DSP Processor
def EM_FX66     := machine.mk 66
-- ^ Siemens FX66 microcontroller
def EM_ST9PLUS  := machine.mk 67
-- ^ STMicroelectronics ST9+ 8/16 bit microcontroller
def EM_ST7      := machine.mk 68
-- ^ STMicroelectronics ST7 8-bit microcontroller
def EM_68HC16   := machine.mk 69
-- ^ Motorola MC68HC16 Microcontroller
def EM_68HC11      := machine.mk 70
-- ^ Motorola MC68HC11 Microcontroller
def EM_68HC08      := machine.mk 71
-- ^ Motorola MC68HC08 Microcontroller
def EM_68HC05      := machine.mk 72
-- ^ Motorola MC68HC05 Microcontroller
def EM_SVX         := machine.mk 73
-- ^ Silicon Graphics SVx
def EM_ST19        := machine.mk 74
-- ^ STMicroelectronics ST19 8-bit microcontroller
def EM_VAX         := machine.mk 75
-- ^ Digital VAX
def EM_CRIS        := machine.mk 76
-- ^ Axis Communications 32-bit embedded processor
def EM_JAVELIN     := machine.mk 77
-- ^ Infineon Technologies 32-bit embedded processor
def EM_FIREPATH    := machine.mk 78
-- ^ Element 14 64-bit DSP Processor
def EM_ZSP         := machine.mk 79
-- ^ LSI Logic 16-bit DSP Processor
def EM_MMIX        := machine.mk 80
-- ^ Donald Knuth's educational 64-bit processor
def EM_HUANY       := machine.mk 81
-- ^ Harvard University machine-independent object files
def EM_PRISM       := machine.mk 82
-- ^ SiTera Prism
def EM_AVR         := machine.mk 83
-- ^ Atmel AVR 8-bit microcontroller
def EM_FR30        := machine.mk 84
-- ^ Fujitsu FR30
def EM_D10V        := machine.mk 85
-- ^ Mitsubishi D10V
def EM_D30V        := machine.mk 86
-- ^ Mitsubishi D30V
def EM_V850        := machine.mk 87
-- ^ NEC v850
def EM_M32R        := machine.mk 88
-- ^ Mitsubishi M32R
def EM_MN10300     := machine.mk 89
-- ^ Matsushita MN10300
def EM_MN10200     := machine.mk 90
-- ^ Matsushita MN10200
def EM_PJ          := machine.mk 91
-- ^ picoJava
def EM_OPENRISC    := machine.mk 92
-- ^ OpenRISC 32-bit embedded processor
def EM_ARC_A5      := machine.mk 93
-- ^ ARC Cores Tangent-A5
def EM_XTENSA      := machine.mk 94
-- ^ Tensilica Xtensa Architecture
def EM_VIDEOCORE   := machine.mk 95
-- ^ Alphamosaic VideoCore processor
def EM_TMM_GPP     := machine.mk 96
-- ^ Thompson Multimedia General Purpose Processor
def EM_NS32K       := machine.mk 97
-- ^ National Semiconductor 32000 series
def EM_TPC         := machine.mk 98
-- ^ Tenor Network TPC processor
def EM_SNP1K       := machine.mk 99
-- ^ Trebia SNP 1000 processor
def EM_ST200       := machine.mk 100
-- ^ STMicroelectronics (www.st.com) ST200 microcontroller
def EM_IP2K        := machine.mk 101
-- ^ Ubicom IP2xxx microcontroller family
def EM_MAX         := machine.mk 102
-- ^ MAX Processor
def EM_CR          := machine.mk 103
-- ^ National Semiconductor CompactRISC microprocessor
def EM_F2MC16      := machine.mk 104
-- ^ Fujitsu F2MC16
def EM_MSP430      := machine.mk 105
-- ^ Texas Instruments embedded microcontroller msp430
def EM_BLACKFIN    := machine.mk 106
-- ^ Analog Devices Blackfin (DSP) processor
def EM_SE_C33      := machine.mk 107
-- ^ S1C33 Family of Seiko Epson processors
def EM_SEP         := machine.mk 108
-- ^ Sharp embedded microprocessor
def EM_ARCA        := machine.mk 109
-- ^ Arca RISC Microprocessor
def EM_UNICORE     := machine.mk 110
-- ^ Microprocessor series from PKU-Unity Ltd. and MPRC of Peking University
def EM_TI_C6000    := machine.mk 140
-- ^ Texas Instruments TMS320C6000 DSP family
def EM_QDSP6 := machine.mk 164
-- 
def EM_L1OM        := machine.mk 180
-- ^ Intel L10M
def EM_K1OM        := machine.mk 181
-- ^ Intel K10M
def EM_AARCH64     := machine.mk 183
-- ^ ARM 64-bit architecture (AARCH64)
def EM_AVR32       := machine.mk 185
-- ^ Atmel Corporation 32-bit microprocessor family
def EM_STM8        := machine.mk 186
-- ^ STMicroeletronics STM8 8-bit microcontroller
def EM_RISCV       := machine.mk 243
-- ^ RISC-V

private def nameMap : RBMap machine String machine.lt :=
RBMap.fromList 
  [ (EM_NONE, "EM_NONE") 
  , (EM_M32, "EM_M32")
  , (EM_SPARC, "EM_SPARC")
  , (EM_386, "EM_386")
  , (EM_68K, "EM_68K")
  , (EM_88K, "EM_88K")
  , (EM_486, "EM_486")
  , (EM_860, "EM_860")
  , (EM_MIPS, "EM_MIPS")
  , (EM_S370, "EM_S370")
  , (EM_MIPS_RS3_LE, "EM_MIPS_RS3_LE")
  , (EM_SPARC64, "EM_SPARC64")
  , (EM_PARISC, "EM_PARISC")
  , (EM_VPP500, "EM_VPP500")
  , (EM_SPARC32PLUS, "EM_SPARC32PLUS")
  , (EM_960, "EM_960")
  , (EM_PPC, "EM_PPC")
  , (EM_PPC64, "EM_PPC64")
  , (EM_S390, "EM_S390")
  , (EM_SPU, "EM_SPU")
  , (EM_V800, "EM_V800")
  , (EM_FR20, "EM_FR20")
  , (EM_RH32, "EM_RH32")
  , (EM_RCE, "EM_RCE")
  , (EM_ARM, "EM_ARM")
  , (EM_ALPHA, "EM_ALPHA")
  , (EM_SH, "EM_SH")
  , (EM_SPARCV9, "EM_SPARCV9")
  , (EM_TRICORE, "EM_TRICORE")
  , (EM_ARC, "EM_ARC")
  , (EM_H8_300, "EM_H8_300")
  , (EM_H8_300H, "EM_H8_300H")
  , (EM_H8S, "EM_H8S")
  , (EM_H8_500, "EM_H8_500")
  , (EM_IA_64, "EM_IA_64")
  , (EM_MIPS_X, "EM_MIPS_X")
  , (EM_COLDFIRE, "EM_COLDFIRE")
  , (EM_68HC12, "EM_68HC12")
  , (EM_MMA, "EM_MMA")
  , (EM_PCP, "EM_PCP")
  , (EM_NCPU, "EM_NCPU")
  , (EM_NDR1, "EM_NDR1")
  , (EM_STARCORE, "EM_STARCORE")
  , (EM_ME16, "EM_ME16")
  , (EM_ST100, "EM_ST100")
  , (EM_TINYJ, "EM_TINYJ")
  , (EM_X86_64, "EM_X86_64")
  , (EM_PDSP, "EM_PDSP")
  , (EM_FX66, "EM_FX66")
  , (EM_ST9PLUS, "EM_ST9PLUS")
  , (EM_ST7, "EM_ST7")
  , (EM_68HC16, "EM_68HC16")
  , (EM_68HC11, "EM_68HC11")
  , (EM_68HC08, "EM_68HC08")
  , (EM_68HC05, "EM_68HC05")
  , (EM_SVX, "EM_SVX")
  , (EM_ST19, "EM_ST19")
  , (EM_VAX, "EM_VAX")
  , (EM_CRIS, "EM_CRIS")
  , (EM_JAVELIN, "EM_JAVELIN")
  , (EM_FIREPATH, "EM_FIREPATH")
  , (EM_ZSP, "EM_ZSP")
  , (EM_MMIX, "EM_MMIX")
  , (EM_HUANY, "EM_HUANY")
  , (EM_PRISM, "EM_PRISM")
  , (EM_AVR, "EM_AVR")
  , (EM_FR30, "EM_FR30")
  , (EM_D10V, "EM_D10V")
  , (EM_D30V, "EM_D30V")
  , (EM_V850, "EM_V850")
  , (EM_M32R, "EM_M32R")
  , (EM_MN10300, "EM_MN10300")
  , (EM_MN10200, "EM_MN10200")
  , (EM_PJ, "EM_PJ")
  , (EM_OPENRISC, "EM_OPENRISC")
  , (EM_ARC_A5, "EM_ARC_A5")
  , (EM_XTENSA, "EM_XTENSA")
  , (EM_VIDEOCORE, "EM_VIDEOCORE")
  , (EM_TMM_GPP, "EM_TMM_GPP")
  , (EM_NS32K, "EM_NS32K")
  , (EM_TPC, "EM_TPC")
  , (EM_SNP1K, "EM_SNP1K")
  , (EM_ST200, "EM_ST200")
  , (EM_IP2K, "EM_IP2K")
  , (EM_MAX, "EM_MAX")
  , (EM_CR, "EM_CR")
  , (EM_F2MC16, "EM_F2MC16")
  , (EM_MSP430, "EM_MSP430")
  , (EM_BLACKFIN, "EM_BLACKFIN")
  , (EM_SE_C33, "EM_SE_C33")
  , (EM_SEP, "EM_SEP")
  , (EM_ARCA, "EM_ARCA")
  , (EM_UNICORE, "EM_UNICORE")
  , (EM_TI_C6000, "EM_TI_C6000")
  , (EM_QDSP6, "EM_QDSP6")
  , (EM_L1OM, "EM_L1OM")
  , (EM_K1OM, "EM_K1OM")
  , (EM_AARCH64, "EM_AARCH64")
  , (EM_AVR32, "EM_AVR32")
  , (EM_STM8, "EM_STM8")
  , (EM_RISCV, "EM_RISCV")
  ]
  machine.lt

def name (m:machine) : String := nameMap.findD m ("UNKNOWN("++m.val.toNat.repr++")")

end machine

/-- Flags for a elf header. -/
def ehdr_flags := UInt32

namespace ehdr_flags

instance : elf_file_data ehdr_flags :=
{ read := file_reader.read_u32 }

end ehdr_flags

/-- The elf header information -/
structure ehdr (c : elf_class) :=
(elf_data : elf_data)
(osabi    : osabi)
(abi_version : UInt8)
(elf_type : elf_type)
(machine  : machine)
(entry    : word c)
(phoff    : word c)
(shoff    : word c)
(flags    : ehdr_flags)
(phnum    : UInt16)
(shnum    : UInt16)
(shstrndx : UInt16)


namespace ehdr

-- Number of bytes in the ehdr after the 16 byte info.
protected def size (c:elf_class) : Nat := 16 + 24 + 3 * c.bytes
protected def info {c : elf_class} (e:ehdr c) : elf.info :=
{ elf_class := c
, elf_data := e.elf_data
, osabi := e.osabi
, abi_version := e.abi_version
}

protected def pp {c : elf_class} (e:ehdr c) : String
  := "Class:                             " ++ c.repr ++ "\n"
  ++ "Data:                              " ++ e.elf_data.repr ++ "\n"
  ++ "OS/ABI:                            " ++ e.osabi.repr ++ "\n"
  ++ "ABI Version:                       " ++ repr e.abi_version.toNat ++ "\n"
  ++ "Type:                              " ++ repr e.elf_type.val.toNat ++ "\n"
  ++ "Machine:                           " ++ repr e.machine.name ++ "\n"
  ++ "Entry point address:               " ++ e.entry.pp_hex ++ "\n"
  ++ "Start of program headers:          " ++ e.phoff.pp_hex ++ " (bytes into file)\n"
  ++ "Start of section headers:          " ++ e.shoff.pp_hex ++ " (bytes into file)\n"
  ++ "Flags:                             " ++ repr e.flags.toNat ++ "\n"
  ++ "Number of program headers:         " ++ repr e.phnum.toNat ++ "\n"
  ++ "Number of section headers:         " ++ repr e.shnum.toNat ++ "\n"
  ++ "Section header String table index: " ++ repr e.shstrndx.toNat ++ "\n"

end ehdr

-- Read the remainder of the elf header after the first 16 bytes for the info.
def read_ehdr_remainder (i : info) : file_reader (ehdr i.elf_class) := do
  tp ← elf_file_data.read;
  mach ← elf_file_data.read;
  ver ← file_reader.read_u32;
  when (ver ≠ 1) (throw $ "Unexpected version: " ++ repr ver.toNat);
  entry ← elf_file_data.read;
  phoff ← elf_file_data.read;
  shoff ← elf_file_data.read;
  flags ← elf_file_data.read;
  _ehsize ← file_reader.read_u16;
  _phentsize ← file_reader.read_u16;
  phnum ← elf_file_data.read;
  _shentsize ← file_reader.read_u16;
  shnum ← elf_file_data.read;
  shstrndx ← elf_file_data.read;
  pure { elf_data := i.elf_data
       , osabi    := i.osabi
       , abi_version := i.abi_version
       , elf_type := tp
       , machine  := mach
       , entry    := entry
       , phoff    := phoff
       , shoff    := shoff
       , flags    := flags
       , phnum    := phnum
       , shnum    := shnum
       , shstrndx := shstrndx
       }

-- The the elf header from the handle (which should be at the
-- beginning of the file.
def read_ehdr_from_handle (h:Galois.Fs.handle) : IO (Sigma ehdr) := do
 i ← buffer.reader.from_handle h 16 info.read;
 let ehdr_size := ehdr.size i.elf_class; do
 hdr ← file_reader.from_handle i h (ehdr_size - 16) (read_ehdr_remainder i);
 pure $ Sigma.mk i.elf_class hdr

-- Pure size of phdr table
def phdr_table_size {c : elf_class} (e:ehdr c) : Nat := (phdr.size c) * (e.phnum.toNat)

def read_phdrs_from_handle {c : elf_class} (e:ehdr c) (h:Galois.Fs.handle)  : IO (List (phdr c)) :=
   file_reader.from_handle (e.info) h (phdr_table_size e) (
      repeat (e.phnum.toNat) $ read_phdr c)

-- Move from current offset to target offset.
def move_to_target (h:Galois.Fs.handle) (target_off:Nat) : IO Unit :=
  do _ <- Galois.IO.Prim.handle.lseek h (Int.ofNat target_off) Galois.Fs.Whence.set;
    pure ()

def pp_phdrs {c:elf_class} (phdrs:List (phdr c)) : IO Unit := do
  forM' (List.zip (List.range phdrs.length) phdrs) (fun phdr => do
    let idx := phdr.fst; do
    IO.println $ "Index:            " ++ repr idx;
    IO.println phdr.snd.pp)

-- A region is the contents of memory as it appears at load time.
@[reducible] def region := ByteArray

-- An elfmem represents the load-time address space represented by
-- the elf file.  It is indexed by virtual address
@[reducible]
def elfmem : Type := init_memory

-- Helper for read_elfmem: add the region corresponding to the phdr in ph
def read_one_elfmem (h : Galois.Fs.handle) {c : elf_class} (m : elfmem) (ph : phdr c) : IO elfmem :=
  if ph.phdr_type = phdr_type.PT_LOAD 
  then do
    _ <- Galois.IO.Prim.handle.lseek h  (Int.ofNat ph.offset.toNat) Galois.Fs.Whence.set;
    fbs <- Galois.IO.Prim.handle.read h (if ph.filesz.toNat < ph.memsz.toNat then ph.filesz.toNat else ph.memsz.toNat);
    let zeroes : memory.region := ByteArray.mk (Array.mkArray (ph.memsz.toNat - ph.filesz.toNat) 0);
    pure $ m.insert ph.vaddr.toNat (ByteArray.append fbs zeroes)
  else pure m

def read_elfmem {c : elf_class} (h : Galois.Fs.handle) (phdrs : List (phdr c)) : IO elfmem  := do
    List.foldlM (read_one_elfmem h) buffer_map.empty phdrs

/---
Read the elf file from the given path, and print out ehdr and
program headers.
-/
def read_info_from_file (path : String) : IO ((Sigma (fun (c : elf_class) => (ehdr c) × List (phdr c))) × elfmem) := do
  bracket (Galois.IO.Prim.handle.mk path Galois.Fs.Mode.read true) Galois.IO.Prim.handle.close $ fun h => do
  ⟨c, e⟩ ← read_ehdr_from_handle h;
  let ehdr_size := ehdr.size c;
  move_to_target h e.phoff.toNat;
  phdrs ← read_phdrs_from_handle e h;
  mem <- read_elfmem h phdrs;
  pure (Sigma.mk c (e, phdrs), mem)

end elf

