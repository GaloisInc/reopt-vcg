/- This file ties together the evaluator,  elf support, and the decoder -/

-- import system.io
import Galois.Init.Io
import X86Semantics.MachineMemory
import Main.Elf
import Main.Translate
import X86Semantics.ConcreteBackend
import DecodeX86.DecodeX86


open x86
 
-- def evaluate_one (s : machine_state) : (Nat × sum unknown_byte instruction) -> except String machine_state
--   | (n, sum.inl err)  => throw "Got an unknown byte"
--   | (n, sum.inr inst) := eval_instruction {s with ip => s.ip + bitvec.of_nat _ n} inst

def get_text_segment {c} (e : elf.ehdr c) (phdrs : List (elf.phdr c)) : Option (elf.phdr c) :=
    phdrs.find? (fun p => p.flags.has_X)

def throwS {a : Type} {m : Type -> Type} [MonadLiftT IO m] (e : String) : m a := 
  monadLift (throw (IO.userError e) : IO a)

-- def lift_eval {α : Type *} |  evaluator α) : io a

-- def dump_state (s : system_state linux.x86_64.os_state) : IO Unit := do
--   let line := s.ip.pp_hex ++ ": " ++ s.print_regs ++ " " ++ s.print_set_flags;
--   IO.println line

def decode_loop (d : decodex86.decoder) 
  : forall (fuel : Nat) (os : linux.x86_64.os_state) (s : machine_state), IO Unit
  | Nat.zero, _, _      => throwS "Out of fuel"
  | Nat.succ n, os, s => do -- dump_state s;
     let inst := decodex86.decode d s.ip.to_nat;
     match inst with 
     | (Sum.inl b) => throwS "Unknown byte"
     | (Sum.inr i) => do
       -- IO.println (repr i);
       let s'  := {s with ip := s.ip + bitvec.of_nat _ i.nbytes };
       let os' := {os with current_ip := s.ip};
       r <- (eval_instruction concreteBackend i).run os' s';
       match r with
       | Except.ok ((_, s''), os'') => decode_loop n os'' s''
       | Except.error e => do
         _ <- os'.trace.reverse.mapM (fun (e : (machine_word × linux.x86_64.trace_event)) => 
                                           IO.println (e.fst.pp_hex ++ " " ++ repr e.snd));
         throwS ("Eval failed: (" ++ repr i ++ ") at " ++  s.ip.pp_hex ++ " "  ++ e)

def doit (elffile : String) : IO Unit := do
  (⟨c, (ehdr, phdrs)⟩, init_mem) <- elf.read_info_from_file elffile;
  text_phdr <- (match get_text_segment ehdr phdrs with
                | none     => throwS "No executable segment"
                | (some p) => pure p);
  text_bytes <- (match init_mem.lookup_buffer (bitvec.of_nat 64 text_phdr.vaddr.toNat) with
                | none        => throwS "No text region"
                | some (_, b) => pure b);
  let entry := ehdr.entry.toNat;
  IO.println ("Entry is " ++ repr entry);
  let d := decodex86.mk_decoder text_bytes text_phdr.vaddr.toNat;
  let init_state :=  { machine_state.empty with 
                       ip := bitvec.of_nat _ ehdr.entry.toNat
                     , mem := memory.from_init init_mem };
  let init_state_abi := sysv_abi.x86_64.initialise init_state;
  let fuel : Nat := 100000; 
  decode_loop d fuel linux.x86_64.os_state.empty init_state_abi

-- set_option profiler true
-- #eval doit ("../testfiles/two", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1544)
-- #eval doit ("../testfiles/mixed_mem", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1536)

-- #eval doit ("../../sample-binaries/tiny/test-conditional.x86_64-exe", "../llvm-tablegen-support/llvm-tablegen-support", 4194704, 4194711)

