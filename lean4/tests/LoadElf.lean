import Main.Elf
import ReoptVCG.ReoptVCG


namespace Test
namespace LoadElf

open elf

def loadElfTest (filePath : String) : IO String := do
(hdr, phdrs, elfMem) ← ReoptVCG.loadElf filePath;
pure "pass"


/-
$ readelf -h test_add_diet_lld.exe
ELF Header:
  Magic:   7f 45 4c 46 02 01 01 00 00 00 00 00 00 00 00 00 
  Class:                             ELF64
  Data:                              2's complement, little endian
  Version:                           1 (current)
  OS/ABI:                            UNIX - System V
  ABI Version:                       0
  Type:                              EXEC (Executable file)
  Machine:                           Advanced Micro Devices X86-64
  Version:                           0x1
  Entry point address:               0x201367
  Start of program headers:          64 (bytes into file)
  Start of section headers:          4248 (bytes into file)
  Flags:                             0x0
  Size of this header:               64 (bytes)
  Size of program headers:           56 (bytes)
  Number of program headers:         6
  Size of section headers:           64 (bytes)
  Number of section headers:         17
  Section header string table index: 15
-/
def loadAndCheckAddElfHdr : IO String := do
(hdr, phdrs, elfMem) ← ReoptVCG.loadElf "../test-programs/test_add_diet_lld.exe";
unless (hdr.elf_data.repr == "ELFDATA2LSB") $
  IO.println $ "Incorrect elf_data: " ++ hdr.elf_data.repr;
unless (hdr.osabi.val.toNat == 0) $
  IO.println $ "Incorrect osabi: " ++ hdr.osabi.val.toNat.repr;
unless (hdr.abi_version.toNat == 0) $
  IO.println $ "Incorrect abi_version: " ++ hdr.abi_version.toNat.repr;
unless (hdr.elf_type.val.toNat == 2) $
  IO.println $ "Incorrect elf_type: " ++ hdr.elf_type.val.toNat.repr;
unless (hdr.machine.val.toNat == 62) $
  IO.println $ "Incorrect machine: " ++ hdr.machine.val.toNat.repr;
unless (hdr.entry.toNat == 0x201367) $
  IO.println $ "Incorrect entry point address: " ++ repr hdr.entry.toNat;
unless (hdr.phoff.toNat == 64) $
  IO.println $ "Incorrect program header table offset: " ++ hdr.phoff.toNat.repr;
unless (hdr.shoff.toNat == 4248) $
  IO.println $ "Incorrect section header table offset: " ++ hdr.shoff.toNat.repr;
unless (hdr.flags.toNat == 0) $
  IO.println $ "Incorrect elf header flags: " ++ hdr.flags.toNat.repr;
unless (hdr.phnum.toNat == 6) $
  IO.println $ "Incorrect number of program headers: " ++ hdr.phnum.toNat.repr;
unless (hdr.shnum.toNat == 17) $
  IO.println $ "Incorrect number of section headers: " ++ hdr.shnum.toNat.repr;
unless (hdr.shstrndx.toNat == 15) $
  IO.println $ "Incorrect section header string table index: " ++ hdr.shstrndx.toNat.repr;
pure "done"


def test : IO UInt32 := do
loadElfTest "../test-programs/test_add_diet_lld.exe" >>= IO.println;
loadElfTest "../test-programs/test_fib_diet_lld.exe" >>= IO.println;
loadAndCheckAddElfHdr >>= IO.println;
pure 0


end LoadElf
end Test


