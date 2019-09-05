/-
This file contains the start of an Elf parser for Lean.  It currently has facilities for parsing
Elf
-/
-- import system.io
-- import init.category.reader
import init.control.state
import x86_semantics.machine_memory
import x86_semantics.buffer_map
-- import .file_input
import galois.init.io
import galois.init.nat

def repeat {α : Type} {m : Type → Type} [Applicative m] : Nat → m α → m (List α)
| 0, m => pure []
| (Nat.succ n),  m => List.cons <$> m <*> repeat n m

def forM' {m : Type → Type} [Monad m] {α : Type} {β:Type} (l:List α) (f:α → m β) : m Unit :=
  List.mmap f l >>= fun _ => pure ()

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
  | (Nat.succ n), acc => toBytesPartialAux n (bs.get (off + n)  :: acc)

def toBytesPartial (bs : ByteArray) (off : Nat) (n : Nat) : List UInt8 := 
  ByteArray.toBytesPartialAux bs off n []

-- FIXME: this is not a cheap way of doing this.
def append (b : ByteArray) (b' : ByteArray) : ByteArray :=
  ByteArray.mk (Array.append b.data b'.data)

end ByteArray

namespace buffer

@[reducible]
def reader := EState String (ByteArray × Nat)

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
  | (EState.Result.ok r _)    => pure r
  | (EState.Result.error e _) => throw e

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

end osabi

-- Information from first 16-bytes of Elf file (allows reading rest of file).
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
  | (EState.Result.ok r _)    => pure r
  | (EState.Result.error e _) => throw e

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

protected def to_hex_with_leading_zeros : List Char → Nat → Nat → String
| prev, 0, _ => prev.asString
| prev, (Nat.succ w), x =>
  let c := (Nat.land x 0xf).digitChar;
  to_hex_with_leading_zeros (c::prev) w (Nat.shiftr x 4)

protected def to_hex' : List Char → Nat → Nat → String
| prev, 0, _ => prev.asString
| prev, w, 0 => prev.asString
| prev, (Nat.succ w), x =>
  let c := (Nat.land x 0xf).digitChar;
  to_hex' (c::prev) w (Nat.shiftr x 4)

-- Print word as decinal
protected def pp_dec {c:elf_class} (w : word c) : String := repr w.toNat
  
--- Print word as hex
protected def pp_hex : ∀{c:elf_class}, word c → String
| ELF32, v => "0x" ++ word.to_hex' []  8 v.toNat
| ELF64, v => "0x" ++ word.to_hex' [] 16 v.toNat

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
def elf_type := UInt16

namespace elf_type
instance : elf_file_data elf_type :=
{ read := file_reader.read_u16 }
end elf_type

/-- Elf header machine type. -/
def machine := UInt16

namespace machine
instance : elf_file_data machine :=
{ read := file_reader.read_u16 }
end machine

/-- Flags for a elf header. -/
def ehdr_flags := UInt32

namespace ehdr_flags

instance : elf_file_data ehdr_flags :=
{ read := file_reader.read_u32 }

end ehdr_flags

/-- The elf header information -/
structure ehdr :=
(info     : info)
(elf_type : elf_type)
(machine  : machine)
(entry    : word info.elf_class)
(phoff    : word info.elf_class)
(shoff    : word info.elf_class)
(flags    : ehdr_flags)
(phnum    : UInt16)
(shnum    : UInt16)
(shstrndx : UInt16)

namespace ehdr

-- Number of bytes in the ehdr after the 16 byte info.
protected def size (c:elf_class) : Nat := 16 + 24 + 3 * c.bytes

protected def elf_class (e:ehdr) := e.info.elf_class

protected def pp (e:ehdr)
  := e.info.pp
  ++ "Type:                              " ++ repr e.elf_type.toNat ++ "\n"
  ++ "Machine:                           " ++ repr e.machine.toNat ++ "\n"
  ++ "Entry point address:               " ++ e.entry.pp_hex ++ "\n"
  ++ "Start of program headers:          " ++ e.phoff.pp_hex ++ " (bytes into file)\n"
  ++ "Start of section headers:          " ++ e.shoff.pp_hex ++ " (bytes into file)\n"
  ++ "Flags:                             " ++ repr e.flags.toNat ++ "\n"
  ++ "Number of program headers:         " ++ repr e.phnum.toNat ++ "\n"
  ++ "Number of section headers:         " ++ repr e.shnum.toNat ++ "\n"
  ++ "Section header String table index: " ++ repr e.shstrndx.toNat ++ "\n"

end ehdr

-- Read the remainder of the elf header after the first 16 bytes for the info.
def read_ehdr_remainder : file_reader ehdr := do
  i ← read;
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
  pure { info := i
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
def read_ehdr_from_handle (h:Galois.Fs.handle) : IO ehdr := do
 i ← buffer.reader.from_handle h 16 info.read;
 let ehdr_size := ehdr.size i.elf_class; do
 file_reader.from_handle i h (ehdr_size - 16) read_ehdr_remainder

-- Pure size of phdr table
def phdr_table_size (e:ehdr) : Nat := phdr.size e.elf_class * e.phnum.toNat

def read_phdrs_from_handle (e:ehdr) (h:Galois.Fs.handle)  : IO (List (phdr e.elf_class)) :=
   file_reader.from_handle (e.info) h (phdr_table_size e) (
      repeat (e.phnum.toNat) $ read_phdr e.elf_class)

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
    List.mfoldl (read_one_elfmem h) buffer_map.empty phdrs

/---
Read the elf file from the given path, and print out ehdr and
program headers.
-/
def read_info_from_file (path : String) : IO ((Sigma (fun (e : ehdr) => List (phdr e.elf_class)) × elfmem)) := do
  bracket (Galois.IO.Prim.handle.mk path Galois.Fs.Mode.read true) Galois.IO.Prim.handle.close $ fun h => do
  e ← read_ehdr_from_handle h;
  let i := e.info; do
  let ehdr_size := ehdr.size i.elf_class; do
  move_to_target h e.phoff.toNat;
  phdrs ← read_phdrs_from_handle e h;
  mem <- read_elfmem h phdrs;
  pure ((Sigma.mk e phdrs), mem)
  -- pp_phdrs phdrs

end elf

