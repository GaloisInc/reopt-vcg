/- This file ties together the evaluator,  elf support, and the decoder -/

-- import system.io
import galois.init.io
import x86_semantics.machine_memory
import .elf
import .translate
import decodex86

open x86
 
-- def evaluate_one (s : machine_state) : (Nat × sum unknown_byte instruction) -> except String machine_state
--   | (n, sum.inl err)  => throw "Got an unknown byte"
--   | (n, sum.inr inst) := eval_instruction {s with ip => s.ip + bitvec.of_nat _ n} inst

def get_text_segment (e : elf.ehdr) (phdrs : List (elf.phdr e.elf_class)) : Option (elf.phdr e.elf_class) :=
    phdrs.find (fun p => p.flags.has_X)

def throwS { a : Type} (e : String) : IO a := throw (IO.userError e)

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
    let rsp_idx : Fin 16 := 4; -- FIXME
    let stack_top := bitvec.of_nat 64 (2 ^ 47);
    let words     := [ 0 /- argc -/, 0 /- argv term. -/, 0 /- envp term -/, 0, 0 /- auxv term (2 words) -/ ];
    let f (acc : (bitvec 64 × machine_state)) (v : Nat) : bitvec 64 × machine_state :=         
        (acc.fst + bitvec.of_nat _ 8, acc.snd.store_word acc.fst (bitvec.of_nat (8 * 8) v));
    let s'        := List.foldl f (stack_top, st.machine_state) words;
    { st with machine_state := machine_state.update_gpreg rsp_idx (fun _ => stack_top) s'.snd }

end x86_64

end sysv_abi

namespace linux
namespace x86_64
open mc_semantics

def rax_idx : Fin 16 := 0

def os_state := Unit
def os_state.empty := ()

def simple_syscall (f : system_state os_state -> machine_word) : system_m os_state Unit :=
  modify (fun s => { s with machine_state := s.machine_state.update_gpreg rax_idx (fun _ => f s) })

def sys_getuid : system_m os_state Unit := 
  let res     := bitvec.of_nat 64 4242;
  simple_syscall (fun _ => res)

-- FIXME: maybe use the euid of the current (lean) process?  We could
-- also forward these to the underlying (Linux) kernel
def sys_geteuid : system_m os_state Unit := 
  let res     := bitvec.of_nat 64 4242;
  simple_syscall (fun _ => res)

def sys_getgid : system_m os_state Unit := 
  let res     := bitvec.of_nat 64 4242;
  simple_syscall (fun _ => res)

-- FIXME: maybe use the euid of the current (lean) process?  We could
-- also forward these to the underlying (Linux) kernel
def sys_getegid : system_m os_state Unit := 
  let res     := bitvec.of_nat 64 4242;
  simple_syscall (fun _ => res)

def syscalls : RBMap Nat (system_m os_state Unit) (fun x y => decide (x < y)) := 
  RBMap.fromList [ (0x66, sys_geteuid)
                  , (0x6b, sys_geteuid)
                  , (0x68, sys_getgid)
                  , (0x6c, sys_getegid)
                  ] (fun x y => decide (x < y))

def syscall_handler : system_m os_state Unit := do
  s <- get;
  let syscall_no := (s.machine_state.get_gpreg rax_idx).to_nat;
  match syscalls.find syscall_no with
     | none     => throw ("Unknown syscall: " ++ repr syscall_no)
     | (some m) => m

end x86_64
end linux


-- def lift_eval {α : Type *} |  evaluator α) : io a

def dump_state (s : system_state linux.x86_64.os_state) : IO Unit := do
  let line := s.machine_state.ip.pp_hex ++ ": " ++ s.machine_state.print_regs ++ " " ++ s.machine_state.print_set_flags;
  IO.println line

def decode_loop (d : decodex86.decoder) : Nat -> system_state linux.x86_64.os_state -> IO Unit
  | Nat.zero,    _   => throw "Out of fuel"
  | (Nat.succ n), s  => do
  dump_state s;
  let inst := decodex86.decode d s.machine_state.ip.to_nat;
  match inst with 
  | (Sum.inl b) => throw ("Unknown byte")
  | (Sum.inr i) => 
    (match eval_instruction { machine_state := { ip := s.machine_state.ip + bitvec.of_nat _ i.nbytes, .. s.machine_state}, ..s } linux.x86_64.syscall_handler i with
    | (Except.error e) => throwS ("Eval failed: (" ++ repr i ++ ") "  ++ e)
    | (Except.ok s')   => decode_loop n s')

def doit (elffile : String) : IO Unit := do
  ((Sigma.mk ehdr phdrs), init_mem) <- elf.read_info_from_file elffile;
  text_phdr <- (match get_text_segment ehdr phdrs with
                | none     => throw "No executable segment"
                | (some p) => pure p);
  text_bytes <- (match init_mem.lookup_buffer (bitvec.of_nat 64 text_phdr.vaddr.toNat) with
                | none        => throw "No text region"
                | some (_, b) => pure b);
  let entry := ehdr.entry.toNat;
  IO.println ("Entry is " ++ repr entry ++ " imm:" ++ repr (18446744073709551616 : Nat) 
                          ++ " exp:"    ++ repr (2 ^ 64)
                          ++ " mul:"  ++ repr (9223372036854775808 * 2) );
  let d := decodex86.mk_decoder text_bytes text_phdr.vaddr.toNat;
  let init_state := 
      system_state.mk { machine_state.empty with 
                      ip := bitvec.of_nat _ ehdr.entry.toNat
                      , mem := memory.from_init init_mem } 
                      linux.x86_64.os_state.empty;
    let init_state_abi := sysv_abi.x86_64.initialise init_state;
    let fuel : Nat := 100000; decode_loop d fuel init_state_abi
  
def main (xs : List String) : IO UInt32 :=
  match xs with 
  | [f] => do doit f; pure 0
  | _   => throw "Expected a file"

-- set_option profiler true
-- #eval doit ("../testfiles/two", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1544)
-- #eval doit ("../testfiles/mixed_mem", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1536)

-- #eval doit ("../../sample-binaries/tiny/test-conditional.x86_64-exe", "../llvm-tablegen-support/llvm-tablegen-support", 4194704, 4194711)

