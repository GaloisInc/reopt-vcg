/- This file ties together the evaluator,  elf support, and the decoder -/

-- import system.io
import Galois.Init.Io
import Main.Elf
import MCInst.Basic

open x86
 

def get_text_segment (e : elf.ehdr) (phdrs : List (elf.phdr e.elf_class)) : Option (elf.phdr e.elf_class) :=
    phdrs.find (fun p => p.flags.has_X)

def throwS { a : Type} (e : String) : IO a := throw (IO.userError e)

partial def decode_loop (d : mcinst.decoder) : Nat -> IO Unit
  | ip => do let inst := mcinst.decode d ip;
             IO.print (repr ip ++ ": ");    
             match inst with 
             | (Sum.inl b) => throw ("Unknown byte")
             | (Sum.inr (i, n)) => do
               IO.println (repr i);
               decode_loop  (ip + n)

def doit (elffile : String) : IO Unit := do
  ((Sigma.mk ehdr phdrs), init_mem) <- elf.read_info_from_file elffile;
  text_phdr <- (match get_text_segment ehdr phdrs with
                | none     => throw "No executable segment"
                | (some p) => pure p);
  text_bytes <- (match init_mem.lookup_buffer (bitvec.of_nat 64 text_phdr.vaddr.toNat) with
                | none        => throw "No text region"
                | some (_, b) => pure b);
  let entry := ehdr.entry.toNat;
  let d := mcinst.mk_decoder text_bytes text_phdr.vaddr.toNat;
  decode_loop d ehdr.entry.toNat
    
def main (xs : List String) : IO UInt32 :=
  match xs with 
  | [f] => do doit f; pure 0
  | _   => throw "Expected a file"

-- set_option profiler true
-- #eval doit ("../testfiles/two", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1544)
-- #eval doit ("../testfiles/mixed_mem", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1536)

-- #eval doit ("../../sample-binaries/tiny/test-conditional.x86_64-exe", "../llvm-tablegen-support/llvm-tablegen-support", 4194704, 4194711)

