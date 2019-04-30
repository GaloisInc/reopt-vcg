/- This file ties together the evaluator,  elf support, and the decoder -/

import system.io
import .machine_memory
import .elf
import .translate
import decodex86

open x86

def get_filename_arg : io (string × string) := do
  args ← io.cmdline_args,
  match args with
  | [decoder, name ] := do
      return ( decoder, name )
  | _ := do
      io.fail "Usage: CMD decoder elf_file"
  end

-- def evaluate_one (s : machine_state) : (ℕ × sum unknown_byte instruction) -> except string machine_state
--   | (n, sum.inl err)  := throw "Got an unknown byte"
--   | (n, sum.inr inst) := eval_instruction {s with ip := s.ip + bitvec.of_nat _ n} inst

def get_text_segment (e : elf.ehdr) (phdrs : list (elf.phdr e.elf_class)) : option (elf.phdr e.elf_class) :=
    phdrs.find (λp, p.flags.has_X)

def decode_loop (d : decodex86.decoder) : ℕ -> machine_state -> io unit
  | nat.zero  _     := io.fail "Out of fuel"
  | (nat.succ n) s  := do
  io.put_str_ln s.print_regs,
  inst <- decodex86.decode d s.ip.to_nat,
  match inst with 
  | (sum.inl err) := io.fail ("Decode error:  " ++ err)
  | (sum.inr (sum.inl b)) := io.fail ("Unknown byte")
  | (sum.inr (sum.inr i)) := 
    match eval_instruction {s with ip := s.ip + bitvec.of_nat _ i.nbytes} i with
    | (except.error e) := io.fail ("Eval failed: "  ++ e)
    | (except.ok s')    := decode_loop n s'
    end
  end
                
def doit : (string × string) -> io unit 
  | (decoder, elffile) := do
    ((sigma.mk ehdr phdrs), init_mem) <- elf.read_info_from_file elffile,
    text_phdr <- match get_text_segment ehdr phdrs with
                 | none     := io.fail "No executable segment"
                 | (some p) := return p
                 end,
    d <- decodex86.mk_decoder decoder elffile text_phdr.vaddr.val text_phdr.offset.val text_phdr.filesz.val,
    let init_state := { machine_state.empty with ip := bitvec.of_nat _ ehdr.entry.val, mem := memory.from_init init_mem }  in
    let fuel : ℕ := 100000 in decode_loop d fuel init_state
  
def main : io unit := 
  get_filename_arg >>= doit

-- set_option profiler true
-- #eval doit ("../testfiles/two", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1544)
-- #eval doit ("../testfiles/mixed_mem", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1536)

-- #eval doit ("../../sample-binaries/tiny/test-conditional.x86_64-exe", "../llvm-tablegen-support/llvm-tablegen-support", 4194704, 4194711)

