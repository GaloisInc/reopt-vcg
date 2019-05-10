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

namespace sysv_abi

namespace x86_64

-- c.f. https://www.uclibc.org/docs/psABI-x86_64.pdf
-- Basically:
-- - rFLAGS are all 0 (ff)
-- - (%rsp) has argc
-- - 8(%rsp) has an an argc-long array of 64 bit words
-- - (8 + 8 * argc)(%rsp) is 0
-- - followed by a 0 terminated array of envps
-- - followed by auxiliary vectors (16 bytes each), terminated by an essentially 0 entry.
-- - At some higher address the strings
-- Also:
-- - %rsp should be 16 byte aligned
--
-- For now we just pick a reasonably rsp, initialise s.t. argc == 0

def initialise { ost : Type } (st : system_state ost) : system_state ost :=
    let rsp_idx := 4 in -- FIXME
    let stack_top := bitvec.of_nat 64 (2 ^ 47) in
    let words     := [ 0 /- argc -/, 0 /- argv term. -/, 0 /- envp term -/, 0, 0 /- auxv term (2 words) -/ ] in
    let f (acc : (bitvec 64 × machine_state)) (v : ℕ) : bitvec 64 × machine_state :=         
        (acc.fst + bitvec.of_nat _ 8, acc.snd.store_word acc.fst (bitvec.of_nat (8 * 8) v)) in
    let s'        := list.foldl f (stack_top, st.machine_state) words in
    { st with machine_state := machine_state.update_gpreg rsp_idx (λ_, stack_top) s'.snd }

end x86_64

end sysv_abi

namespace linux
namespace x86_64
open mc_semantics

def rax_idx : fin 16 := 0

def os_state := unit
def os_state.empty := ()

def simple_syscall (f : system_state os_state -> machine_word) : system_m os_state unit :=
  modify (λs, { s with machine_state := s.machine_state.update_gpreg rax_idx (λ_, f s) })

def sys_getuid : system_m os_state unit := 
  let res     := bitvec.of_nat 64 4242
  in simple_syscall (λ_, res)

-- FIXME: maybe use the euid of the current (lean) process?  We could
-- also forward these to the underlying (Linux) kernel
def sys_geteuid : system_m os_state unit := 
  let res     := bitvec.of_nat 64 4242
  in simple_syscall (λ_, res)

def sys_getgid : system_m os_state unit := 
  let res     := bitvec.of_nat 64 4242
  in simple_syscall (λ_, res)

-- FIXME: maybe use the euid of the current (lean) process?  We could
-- also forward these to the underlying (Linux) kernel
def sys_getegid : system_m os_state unit := 
  let res     := bitvec.of_nat 64 4242
  in simple_syscall (λ_, res)

def syscalls : rbmap ℕ (system_m os_state unit) := 
  rbmap.from_list [ (0x66, sys_geteuid)
                  , (0x6b, sys_geteuid)
                  , (0x68, sys_getgid)
                  , (0x6c, sys_getegid)
                  ]

def syscall_handler : system_m os_state unit := do
  s <- get,
  let syscall_no := (s.machine_state.get_gpreg rax_idx).to_nat 
  in match syscalls.find syscall_no with
     | none := throw ("Unknown syscall: " ++ repr syscall_no)
     | (some m) := m
     end

end x86_64
end linux


-- def lift_eval {α : Type *} |  evaluator α) : io a

def dump_state (s : system_state linux.x86_64.os_state) : io unit := do
  let line := s.machine_state.ip.pp_hex ++ ": " ++ s.machine_state.print_regs ++ " " ++ s.machine_state.print_set_flags
  in io.put_str_ln line

def decode_loop (d : decodex86.decoder) : ℕ -> system_state linux.x86_64.os_state -> io unit
  | nat.zero  _     := io.fail "Out of fuel"
  | (nat.succ n) s  := do
  dump_state s,
  inst <- decodex86.decode d s.machine_state.ip.to_nat,
  match inst with 
  | (sum.inl err) := io.fail ("Decode error:  " ++ err)
  | (sum.inr (sum.inl b)) := io.fail ("Unknown byte")
  | (sum.inr (sum.inr i)) := 
    match eval_instruction { s with machine_state := { s.machine_state with ip := s.machine_state.ip + bitvec.of_nat _ i.nbytes} } linux.x86_64.syscall_handler i with
    | (except.error e) := io.fail ("Eval failed: (" ++ repr i ++ ") "  ++ e)
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
    let init_state := 
        system_state.mk { machine_state.empty with ip := bitvec.of_nat _ ehdr.entry.val, mem := memory.from_init init_mem } 
                        linux.x86_64.os_state.empty
    in
    let init_state_abi := sysv_abi.x86_64.initialise init_state in
    let fuel : ℕ := 100000 in decode_loop d fuel init_state_abi
  
def main : io unit := 
  get_filename_arg >>= doit

-- set_option profiler true
-- #eval doit ("../testfiles/two", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1544)
-- #eval doit ("../testfiles/mixed_mem", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1536)

-- #eval doit ("../../sample-binaries/tiny/test-conditional.x86_64-exe", "../llvm-tablegen-support/llvm-tablegen-support", 4194704, 4194711)

