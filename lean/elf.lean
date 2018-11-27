/-
This file contains the start of an Elf parser for Lean.  It currently has facilities for parsing
Elf
-/
import system.io
import init.category.reader
import init.category.state
import decodex86
import .imap
import .file_input

def repeat {α : Type} {m : Type → Type} [applicative m] : ℕ → m α → m (list α)
| 0 m := pure []
| (nat.succ n)  m := list.cons <$> m <*> repeat n m

def forM' {m : Type → Type} [monad m] {α : Type} {β:Type} (l:list α) (f:α → m β) : m unit :=
  list.mmap' f l

def bracket {α β:Type} (c:io α) (d:α → io unit) (f:α → io β) := do
  x ← c,
  io.finally (f x) (d x)

@[reducible]
def uint8 := fin (nat.succ 0xff)

@[reducible]
def uint16 := fin (nat.succ 0xffff)

@[reducible]
def uint32 := fin (nat.succ 0xffffffff)

@[reducible]
def uint64 := fin (nat.succ 0xffffffffffffffff)

namespace buffer

@[reducible]
def reader := except_t string (state char_buffer)

namespace reader

protected
def read_chars (n:ℕ) : reader (list char) := do
  s ← get,
  when (s.size < n) (throw "read_chars eof"),
  put $ s.drop n,
  return ((s.take n).to_list)

def skip (n:ℕ) : reader unit := do
  s ← get,
  when (s.size < n) (throw "skip eof"),
  put $ s.drop n

def read_uint8 : reader uint8 := do
  l ← reader.read_chars 1,
  match l with
  | [h] := do
    return $ fin.of_nat h.val
  | _ := throw "internal: read_uint8"
  end

def from_handle {α} (h:io.handle) (n:ℕ) (r:reader α) : io α := do
  b ← io.fs.read h n,
  match r.run.run b with
  | ⟨except.ok r,b'⟩ := do
    pure r
  | ⟨except.error e, b'⟩ := do
    io.fail e
  end

end reader
end buffer

namespace elf

def magic : list char := ['\x7f', 'E', 'L', 'F' ]

inductive elf_class
| ELF32 : elf_class
| ELF64 : elf_class

namespace elf_class

protected def repr : elf_class → string
| ELF32 := "ELF32"
| ELF64 := "ELF64"

protected def bytes : elf_class → ℕ
| ELF32 := 4
| ELF64 := 8

protected def bits : elf_class → ℕ
| ELF32 := 32
| ELF64 := 64

end elf_class

inductive elf_data
| ELFDATA2LSB : elf_data
| ELFDATA2MSB : elf_data

namespace elf_data

protected def repr : elf_data → string
| ELFDATA2LSB := "ELFDATA2LSB"
| ELFDATA2MSB := "ELFDATA2MSB"

end elf_data

open elf_class
open elf_data

structure osabi :=
(val : uint8)

namespace osabi

protected def repr (o:osabi) : string :=
  match o.val.val with
  | 0 := "UNIX - System V"
  | v := v.repr
  end

end osabi

-- Information from first 16-bytes of Elf file (allows reading rest of file).
structure info :=
(elf_class : elf_class)
(elf_data  : elf_data)
(osabi : osabi)
(abi_version : uint8)

namespace info

protected def pp (e:info) : string
  := "Class:                             " ++ e.elf_class.repr ++ "\n"
  ++ "Data:                              " ++ e.elf_data.repr ++ "\n"
  ++ "OS/ABI:                            " ++ e.osabi.repr ++ "\n"
  ++ "ABI Version:                       " ++ e.abi_version.val.repr ++ "\n"

open buffer

def read : reader info := do
  b ← reader.read_chars 4,
  when (b ≠ magic) (throw "Not an elf file."),
  cl_val ← reader.read_uint8,
  cl ←
    match cl_val.val with
    | 1 := pure ELF32
    | 2 := pure ELF64
    | _ := throw "Invalid elf data."
    end,
  dt_val ← reader.read_uint8,
  dt ←
    match dt_val.val with
    | 1 := pure ELFDATA2LSB
    | 2 := pure ELFDATA2MSB
    | _ := throw "Invalid elf data."
    end,
  elf_version ← reader.read_uint8,
  when (elf_version ≠ 1) (throw "Mismatched elf version."),
  osabi ← reader.read_uint8,
  osabi_ver ← reader.read_uint8,
  pure { elf_class := cl
       , elf_data := dt
       , osabi := ⟨osabi⟩
       , abi_version := osabi_ver
       }

end info

-- A reader for elf files
@[reducible]
def file_reader := reader_t info buffer.reader

namespace file_reader

protected
def from_handle {α:Type} (i:info) (h:io.handle) (n:ℕ) (r:file_reader α) : io α := do
  b ← io.fs.read h n,
  match (r.run i).run.run b with
  | ⟨except.ok r, b'⟩ := do
    pure r
  | ⟨except.error e, b'⟩ := do
    io.fail e
  end

def read_u8  : file_reader uint8  :=
  reader_t.lift $ buffer.reader.read_uint8

protected
def read_chars_lsb (w:ℕ) : file_reader (list char) := do
  i ← read,
  let f (l:list char) : list char :=
        match i.elf_data with
        | ELFDATA2LSB := l
        | ELFDATA2MSB := l.reverse
        end in do
  reader_t.lift $ f <$> buffer.reader.read_chars w

def read_u16 : file_reader uint16 := do
  l ← file_reader.read_chars_lsb 2,
  match l with
  | [x0,x1] :=
    return $ fin.of_nat
      $ nat.shiftl x1.val 8
      + x0.val
  | _ := throw "internal: read_uint16"
  end

def read_u32 : file_reader uint32 := do
  l ← file_reader.read_chars_lsb 4,
  match l with
  | [x0,x1,x2,x3] :=
    return $ fin.of_nat
      $ nat.shiftl x3.val 24
      + nat.shiftl x2.val 16
      + nat.shiftl x1.val 8
      + x0.val
  | _ := throw "internal: read_uint32"
  end

def read_u64 : file_reader uint64 := do
  l ← file_reader.read_chars_lsb 8,
  match l with
  | [x0,x1,x2,x3, x4, x5, x6, x7] :=
    return $ fin.of_nat
      $ nat.shiftl x7.val 56
      + nat.shiftl x6.val 48
      + nat.shiftl x5.val 40
      + nat.shiftl x4.val 32
      + nat.shiftl x3.val 24
      + nat.shiftl x2.val 16
      + nat.shiftl x1.val 8
      + x0.val
  | _ := throw "internal: read_uint64"
  end

end file_reader

class elf_file_data (α:Type) :=
(read {} : file_reader α)

instance uint16_si_elf_file_data : elf_file_data uint16 :=
{ read := file_reader.read_u16 }

/- Elf defines a set of types depending on the class, e.g. Elf32_Word, Elf32_Addr, etc.  
   Some of these are independent of the class, e.g. Elf32_Word = Elf64_Word = uint32.  
-/

-- A 32 or 64-bit word dependent on the class.
def word (c:elf_class) := fin (nat.succ (2^c.bits-1))

namespace word

protected def to_hex_with_leading_zeros : list char → ℕ → ℕ → string
| prev 0 _ := prev.as_string
| prev (nat.succ w) x :=
  let c := (nat.land x 0xf).digit_char in
  to_hex_with_leading_zeros (c::prev) w (nat.shiftr x 4)

protected def to_hex' : list char → ℕ → ℕ → string
| prev 0 _ := prev.as_string
| prev w 0 := prev.as_string
| prev (nat.succ w) x :=
  let c := (nat.land x 0xf).digit_char in
  to_hex' (c::prev) w (nat.shiftr x 4)

-- Print word as decinal
protected def pp_dec : Π{c:elf_class}, word c → string
| ELF32 v := v.val.repr
| ELF64 v := v.val.repr

--- Print word as hex
protected def pp_hex : Π{c:elf_class}, word c → string
| ELF32 v := "0x" ++ word.to_hex' []  8 v.val
| ELF64 v := "0x" ++ word.to_hex' [] 16 v.val

protected def size : elf_class → ℕ := elf_class.bytes

theorem dbl_is_bit0 (x y:ℕ) : bit0 x*y = bit0 (x*y) :=
begin
  simp [bit0, nat.right_distrib],
end

--- `bit1_dec d x` is a utility function that denotes `(d+1)*x-1`
-- It is primarily used
def bit1_dec : ℕ →  ℕ → ℕ
| d x := (d+1)*x-1

theorem bit0_sub_1_congr (x:ℕ)  : bit0 x - 1 = bit1_dec 1 x :=
begin
  simp [bit1_dec, bit1, bit0, nat.add_succ, nat.succ_mul],
end

theorem bit1_dec_bit0 (d x:ℕ) : bit1_dec d (bit0 x) = bit1_dec (bit1 d) x :=
begin
  simp [bit1_dec, bit1, bit0, nat.add_succ, nat.succ_mul,
        nat.left_distrib, nat.right_distrib],
end

theorem bit1_dec_one (d:ℕ) : bit1_dec d 1 = d :=
begin
  simp [bit1_dec],
end

theorem word32_is_uint32 : uint32 = word ELF32 :=
begin
  simp [uint32, word, elf_class.bits, has_pow.pow, nat.pow, dbl_is_bit0, bit0_sub_1_congr
       , bit1_dec_bit0, bit1_dec_one],
end

theorem word64_is_uint64 : uint64 = word ELF64 :=
begin
  simp [uint32, word, elf_class.bits, has_pow.pow, nat.pow, dbl_is_bit0, bit0_sub_1_congr
       , bit1_dec_bit0, bit1_dec_one],
end

instance (c:elf_class) : elf_file_data (word c) :=
{ read := do
  match c with
  | ELF32 := eq.mp word32_is_uint32 <$> file_reader.read_u32
  | ELF64 := eq.mp word64_is_uint64 <$> file_reader.read_u64
  end
}

end word

------------------------------------------------------------------------
-- phdr

inductive phdr_type : Type
  | PT_NULL    : phdr_type
  | PT_LOAD    : phdr_type
  | PT_DYNAMIC : phdr_type
  | PT_INTERP  : phdr_type
  | PT_NOTE    : phdr_type 
  | PT_SHLIB   : phdr_type
  | PT_PHDR    : phdr_type
  | PT_PROC    : uint32 -> phdr_type

namespace phdr_type

def repr (pht : phdr_type) : string :=
  match pht with
  | PT_NULL    := "PT_NULL"
  | PT_LOAD    := "PT_LOAD"  
  | PT_DYNAMIC := "PT_DYNAMIC"
  | PT_INTERP  := "PT_INTERP" 
  | PT_NOTE    := "PT_NOTE"   
  | PT_SHLIB   := "PT_SHLIB"  
  | PT_PHDR    := "PT_PHDR" 
  | PT_PROC n  := "PT_PROC " ++ n.val.repr
  end

instance : has_repr phdr_type := ⟨repr⟩
  
instance : elf_file_data phdr_type :=
{ read := do 
    w <- file_reader.read_u32,
    pure $ match w.val with 
            | 0 := PT_NULL
            | 1 := PT_LOAD    
            | 2 := PT_DYNAMIC 
            | 3 := PT_INTERP  
            | 4 := PT_NOTE    
            | 5 := PT_SHLIB   
            | 6 := PT_PHDR    
            | _ := PT_PROC w
           end
}

end phdr_type

/-- Flags for a program header. -/
inductive phdr_flag
  | PF_X : phdr_flag
  | PF_W : phdr_flag
  | PF_R : phdr_flag
/-  | PF_PROC : word c -> phdr_flag -/

@[reducible]
def phdr_flags := list phdr_flag

namespace phdr_flags

open phdr_flag

instance : elf_file_data phdr_flags :=
{ read := do
  w <- file_reader.read_u32,
  pure $ (if w.val.test_bit 0 then [ PF_X ] else [])
        ++ (if w.val.test_bit 1 then [ PF_W ] else [])
        ++ (if w.val.test_bit 2 then [ PF_R ] else [])
}

def repr1 (f : phdr_flag) : string :=
  match f with
  | PF_X := "PF_X"
  | PF_W := "PF_W"
  | PF_R := "PF_R"
  end

instance : has_repr phdr_flag := ⟨repr1⟩

def repr : phdr_flags -> string := has_repr.repr

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

def size (c:elf_class) : ℕ := 8 + 6 * word.size c

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

def read_phdr : Π(c:elf_class), file_reader (phdr c)
| ELF32 := do
  tp ← elf_file_data.read,
  offset ← elf_file_data.read,
  vaddr  ← elf_file_data.read,
  paddr  ← elf_file_data.read,
  filesz ← elf_file_data.read,
  memsz  ← elf_file_data.read,
  flags ← elf_file_data.read,
  align  ← elf_file_data.read,
  pure { phdr_type := tp
       , flags := flags
       , offset := offset
       , vaddr  := vaddr
       , paddr  := paddr
       , filesz := filesz
       , memsz  := memsz
       , align := align
       }
| ELF64 := do
  tp ← elf_file_data.read,
  flags ← elf_file_data.read,
  offset ← elf_file_data.read,
  vaddr  ← elf_file_data.read,
  paddr  ← elf_file_data.read,
  filesz ← elf_file_data.read,
  memsz  ← elf_file_data.read,
  align  ← elf_file_data.read,
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
(val : uint16)

namespace elf_type
instance : elf_file_data elf_type :=
{ read := elf_type.mk <$> file_reader.read_u16 }
end elf_type

/-- Elf header machine type. -/
structure machine :=
(val : uint16)

namespace machine
instance : elf_file_data machine :=
{ read := machine.mk <$> file_reader.read_u16 }
end machine

/-- Flags for a elf header. -/
structure ehdr_flags :=
(val : uint32)

namespace ehdr_flags

instance : elf_file_data ehdr_flags :=
{ read := ehdr_flags.mk <$> file_reader.read_u32 }

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
(phnum    : uint16)
(shnum    : uint16)
(shstrndx : uint16)

namespace ehdr

-- Number of bytes in the ehdr after the 16 byte info.
protected def size (c:elf_class) : ℕ := 16 + 24 + 3 * c.bytes

protected def elf_class (e:ehdr) := e.info.elf_class

protected def pp (e:ehdr)
  := e.info.pp
  ++ "Type:                              " ++ e.elf_type.val.val.repr ++ "\n"
  ++ "Machine:                           " ++ e.machine.val.val.repr ++ "\n"
  ++ "Entry point address:               " ++ e.entry.pp_hex ++ "\n"
  ++ "Start of program headers:          " ++ e.phoff.val.repr ++ " (bytes into file)\n"
  ++ "Start of section headers:          " ++ e.shoff.val.repr ++ " (bytes into file)\n"
  ++ "Flags:                             " ++ e.flags.val.val.repr ++ "\n"
  ++ "Number of program headers:         " ++ e.phnum.val.repr ++ "\n"
  ++ "Number of section headers:         " ++ e.shnum.val.repr ++ "\n"
  ++ "Section header string table index: " ++ e.shstrndx.val.repr ++ "\n"

end ehdr

-- Read the remainder of the elf header after the first 16 bytes for the info.
def read_ehdr_remainder : file_reader ehdr := do
  i ← read,
  tp ← elf_file_data.read,
  mach ← elf_file_data.read,
  ver ← file_reader.read_u32,
  when (ver ≠ 1) (throw $ "Unexpected version: " ++ ver.val.repr),
  entry ← elf_file_data.read,
  phoff ← elf_file_data.read,
  shoff ← elf_file_data.read,
  flags ← elf_file_data.read,
  _ehsize ← file_reader.read_u16,
  _phentsize ← file_reader.read_u16,
  phnum ← elf_file_data.read,
  _shentsize ← file_reader.read_u16,
  shnum ← elf_file_data.read,
  shstrndx ← elf_file_data.read,
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
def read_ehdr_from_handle (h:io.handle) : io ehdr := do
 i ← buffer.reader.from_handle h 16 info.read,
 let ehdr_size := ehdr.size i.elf_class in do
 file_reader.from_handle i h (ehdr_size - 16) read_ehdr_remainder

-- Return size of phdr table
def phdr_table_size (e:ehdr) : ℕ := phdr.size e.elf_class * e.phnum.val

def read_phdrs_from_handle (e:ehdr) (h:io.handle)  : io (list (phdr e.elf_class)) :=
   file_reader.from_handle (e.info) h (phdr_table_size e) (
      repeat (e.phnum.val) $ read_phdr e.elf_class)

-- Move from current offset to target offset.
def move_to_target (h:io.handle) (cur_off:ℕ) (target_off:ℕ) : io unit :=
  if target_off < cur_off then do
    io.fail "Unexpected phdr offset"
  else do
    _ ← io.fs.read h (target_off - cur_off),
    pure ()

def pp_phdrs {c:elf_class} (phdrs:list (phdr c)) : io unit := do
  forM' (list.zip (list.range phdrs.length) phdrs) (λphdr, do
    let idx := phdr.fst in do
    io.put_str_ln $ "Index:            " ++ idx.repr,
    io.put_str_ln phdr.snd.pp)

@[reducible] def region := char_buffer

def elfmem : Type := data.imap ℕ region

def read_one_elfmem {c : elf_class} (m : elfmem) (ph : phdr c) : file_input elfmem :=
  match ph.phdr_type with
  | phdr_type.PT_LOAD := do
    file_input.seek ph.offset.val,
    fbs <- file_input.read (min ph.filesz.val ph.memsz.val),
    monad_lift (io.put_str_ln ("read_one_elfmem: read " ++ fbs.size.repr ++ " bytes")),
    let val := buffer.append_list fbs (list.repeat (char.of_nat 0) (ph.memsz.val - ph.filesz.val)) 
    in pure $ data.imap.insert ph.vaddr.val ph.memsz.val val m
  | _       := pure m
  end

def read_elfmem {c : elf_class} (path : string) (phdrs : list (phdr c)) : io elfmem  := do
    r <- file_input.run_file_input path $ list.mfoldl read_one_elfmem [] phdrs,
    match r with                  
    | except.error s := io.fail s
    | except.ok r    := return r
    end
/---
Read the elf file from the given path, and print out ehdr and
program headers.
-/
def read_info_from_file (path:string) : io elfmem := do
  bracket (io.mk_file_handle path io.mode.read tt) io.fs.close $ λh, do
  e ← read_ehdr_from_handle h,
  let i := e.info in do
  let ehdr_size := ehdr.size i.elf_class in do
  move_to_target h ehdr_size e.phoff.val,
  phdrs ← read_phdrs_from_handle e h,
  read_elfmem path phdrs
  -- pp_phdrs phdrs

end elf

def get_filename_arg : io (string × string × ℕ × ℕ) := do
  args ← io.cmdline_args,
  match args with
  | [name, decoder, first, last_plus_1 ] := do
      return ( name, decoder, string.to_nat first, string.to_nat last_plus_1 )
  | _ := do
      io.fail "Usage: CMD elf_file decoder first_byte last_byte_plus_1"
  end

def main : io unit := do
  (file, decoder, first, last_plus_1) ← get_filename_arg,
  mem <- elf.read_info_from_file file,
  match data.imap.lookup first mem with
  | none := io.fail ("Could not find start address: " ++ repr first)
  | (some (buf_start, buf)) :=
    if last_plus_1 - buf_start > buffer.size buf then
      io.fail ("Last byte outside buffer: " ++ repr last_plus_1)
    else do
      buf' <- return (buffer.take (buffer.drop buf (first - buf_start)) (last_plus_1 - first)),
      res  <- decodex86.decode decoder buf',
      match res with
      | (sum.inl e) := io.fail ("Decode error: " ++ e)
      | (sum.inr r) := io.put_str_ln (repr r)
      end
  end
