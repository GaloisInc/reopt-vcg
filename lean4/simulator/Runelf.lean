/- This file ties together the evaluator,  elf support, and the decoder -/

-- import system.io
import Galois.Init.Io
import X86Semantics.MachineMemory
import Main.Elf
import Main.Translate
import DecodeX86.DecodeX86

open x86
 
-- def evaluate_one (s : machine_state) : (Nat × sum unknown_byte instruction) -> except String machine_state
--   | (n, sum.inl err)  => throw "Got an unknown byte"
--   | (n, sum.inr inst) := eval_instruction {s with ip => s.ip + bitvec.of_nat _ n} inst

def get_text_segment (e : elf.ehdr) (phdrs : List (elf.phdr e.elf_class)) : Option (elf.phdr e.elf_class) :=
    phdrs.find? (fun p => p.flags.has_X)


def throwS {a : Type} {m : Type -> Type} [MonadIO m] (e : String) : m a := 
  monadLift (throw (IO.userError e) : IO a)

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

def initialise (st : machine_state) : machine_state :=
    let rsp_idx : Fin 16 := 4; -- FIXME
    let stack_top := bitvec.of_nat 64 (2 ^ 47);
    let words     := [ 0 /- argc -/, 0 /- argv term. -/, 0 /- envp term -/, 0, 0 /- auxv term (2 words) -/ ];
    let f (acc : (bitvec 64 × machine_state)) (v : Nat) : bitvec 64 × machine_state :=         
        (acc.fst + bitvec.of_nat _ 8, acc.snd.store_word acc.fst (bitvec.of_nat (8 * 8) v));
    let s'        := List.foldl f (stack_top, st) words;
    machine_state.update_gpreg rsp_idx (fun _ => stack_top) s'.snd

end x86_64

end sysv_abi

namespace linux
namespace x86_64
open mc_semantics


inductive trace_event 
  | syscall : Nat -> List machine_word -> trace_event
  | read    : machine_word -> ∀(n:Nat), bitvec n -> trace_event
  | write   : machine_word -> ∀(n:Nat), bitvec n -> trace_event

def trace_event.repr : trace_event -> String 
  | trace_event.syscall n args => 
    let pfx := "syscall " ++ repr n ++ " " ++ repr args.length;
    List.foldl (fun (s : String) (w : machine_word) => s ++ " " ++ w.pp_hex) pfx args
  | trace_event.read addr n b  => "read " ++ addr.pp_hex ++ " " ++ repr n ++ " " ++ b.pp_hex
  | trace_event.write addr n b => "write " ++ addr.pp_hex ++ " " ++ repr n ++ " " ++ b.pp_hex

instance trace_event_repr : HasRepr trace_event := ⟨trace_event.repr⟩

structure os_state :=
  (current_ip : machine_word)
  (trace : List (machine_word × trace_event))

def os_state.empty : os_state := os_state.mk 0 []

-- Stacking like this makes it easier to derive MonadState
def base_system_m := (StateT os_state (ExceptT String IO))
def system_m := StateT machine_state base_system_m

instance : Monad base_system_m :=
  inferInstanceAs (Monad (StateT os_state (ExceptT String IO)))

instance : MonadState os_state base_system_m :=
  inferInstanceAs (MonadState os_state (StateT os_state (ExceptT String IO)))

instance : MonadExcept String base_system_m :=
  inferInstanceAs (MonadExcept String (StateT os_state (ExceptT String IO)))

instance  : MonadIO base_system_m :=
  inferInstanceAs (MonadIO (StateT os_state (ExceptT String IO)))

instance system_m.Monad : Monad system_m :=
  inferInstanceAs (Monad (StateT machine_state base_system_m))

instance system_m.MonadState : MonadState machine_state system_m :=
  inferInstanceAs (MonadState machine_state (StateT machine_state base_system_m))

instance system_m.MonadExcept : MonadExcept String system_m :=
  inferInstanceAs (MonadExcept String (StateT machine_state base_system_m))

instance : HasMonadLiftT base_system_m system_m :=
  inferInstanceAs (HasMonadLiftT base_system_m (StateT machine_state base_system_m))

instance system_m.MonadIO : MonadIO system_m :=
  inferInstanceAs (MonadIO (StateT machine_state base_system_m))

def system_m.run {a : Type} (m : system_m a) (s : machine_state) : IO (Except String a) := 
  ((m.run' s).run' os_state.empty).run

def emit_trace_event (e : trace_event) : system_m Unit :=
  monadLift (modify (fun (s : os_state) => { s with trace := (s.current_ip, e) :: s.trace }) : base_system_m Unit)

-- Linux calling conv: %rdi, %rsi, %rdx, %r10, %r8 and %r9, with %rax holding syscall number.

-- FIXME: these should maybe be in common?

def rax_idx : Fin 16 := 0
def rcx_idx : Fin 16 := 1
def rdx_idx : Fin 16 := 2
def rbx_idx : Fin 16 := 3
def rsp_idx : Fin 16 := 4
def rbp_idx : Fin 16 := 5
def rsi_idx : Fin 16 := 6
def rdi_idx : Fin 16 := 7
def r8_idx  : Fin 16 := 8
def r9_idx  : Fin 16 := 9
def r10_idx : Fin 16 := 10
def r11_idx : Fin 16 := 11
def r12_idx : Fin 16 := 12
def r13_idx : Fin 16 := 13
def r14_idx : Fin 16 := 14
def r15_idx : Fin 16 := 15

-- def simple_syscall (f : system_state os_state -> machine_word) : system_m Unit :=
--   modify (fun s => { s with machine_state := s.machine_state.update_gpreg rax_idx (fun _ => f s) })

def emit_syscall_trace (syscall_no : Nat) (args : List machine_word) : system_m Unit :=
    emit_trace_event (trace_event.syscall syscall_no args)

def raw_syscall {a : Type} (f : machine_word -> machine_word -> machine_word -> machine_word -> machine_word -> machine_word -> system_m a)
  : system_m a := do
  s <- get;
  f (s.get_gpreg rdi_idx)
    (s.get_gpreg rsi_idx)
    (s.get_gpreg rdx_idx)
    (s.get_gpreg r10_idx)
    (s.get_gpreg r8_idx)
    (s.get_gpreg r9_idx)

def syscall0 (sys_f : system_m machine_word)
             (syscall_no : Nat) 
             : system_m Unit := do
  res <- raw_syscall (fun _ _ _ _ _ _ => do emit_syscall_trace syscall_no []; sys_f);
  modify (machine_state.update_gpreg rax_idx (fun _ => res))

def syscall1 (sys_f : machine_word -> system_m machine_word) 
             (syscall_no : Nat)
             : system_m Unit := do
  res <- raw_syscall (fun a _ _ _ _ _ => do emit_syscall_trace syscall_no [a]; sys_f a);
  modify (machine_state.update_gpreg rax_idx (fun _ => res))

def syscall3 (sys_f : machine_word -> machine_word -> machine_word -> system_m machine_word) 
             (syscall_no : Nat)
             : system_m Unit := do
  res <- raw_syscall (fun a b c _ _ _ => do emit_syscall_trace syscall_no [a, b, c]; sys_f a b c);
  modify (machine_state.update_gpreg rax_idx (fun _ => res))

def syscall6 (sys_f : machine_word -> machine_word -> machine_word -> machine_word -> machine_word -> machine_word -> system_m machine_word) 
             (syscall_no : Nat)
             : system_m Unit := do
  res <- raw_syscall (fun a b c d e f => do emit_syscall_trace syscall_no [a, b, c, d, e, f]; sys_f a b c d e f);
  modify (machine_state.update_gpreg rax_idx (fun _ => res))

-- Stub calls
abbrev syscall_t := ∀(syscall_no : Nat), system_m Unit

def sys_getuid : syscall_t :=
  syscall0 (pure (bitvec.of_nat 64 4242))

-- FIXME: maybe use the euid of the current (lean) process?  We could
-- also forward these to the underlying (Linux) kernel
def sys_geteuid : syscall_t :=
  syscall0 (pure (bitvec.of_nat 64 4242))

def sys_getgid : syscall_t :=
  syscall0 (pure (bitvec.of_nat 64 4242))

-- FIXME: maybe use the euid of the current (lean) process?  We could
-- also forward these to the underlying (Linux) kernel
def sys_getegid : syscall_t :=
  syscall0 (pure (bitvec.of_nat 64 4242))

def sys_exit : syscall_t :=
  syscall1 (fun _ => throw "Exit system call")

def sys_write : syscall_t :=
  syscall3 (fun filedes buf nbytes => do
               s <- get;
               let m_bytes := s.mem.read_bytes buf nbytes.to_nat;
               match m_bytes with
               | none      => throw ("sys_write: unable to read " ++ nbytes.to_nat.repr ++ " bytes at " ++ buf.pp_hex)
               | (some bs) => if filedes = 1 
                              then do let str := String.mk (bs.map (fun (b : byte) => Char.ofNat b.toNat));
                                      IO.print str;
                                      pure nbytes -- always succeed
                              else throw ("sys_write: unable to write to filedes " ++ filedes.to_nat.repr)
           )

def syscalls : RBMap Nat syscall_t (fun x y => decide (x < y)) := 
  RBMap.fromList [  (0x01, sys_write)
                  , (0x3c, sys_exit)
                  , (0x66, sys_geteuid)
                  , (0x6b, sys_geteuid)
                  , (0x68, sys_getgid)
                  , (0x6c, sys_getegid)
                  ] (fun x y => decide (x < y))

def syscall_handler : system_m Unit := do
  s <- get;
  let syscall_no := (s.get_gpreg rax_idx).to_nat;
  match syscalls.find? syscall_no with
     | none     => throw ("Unknown syscall: " ++ repr syscall_no)
     | (some m) => m syscall_no

instance : SystemM system_m :=
  SystemM.mk syscall_handler 
             (fun addr n b => emit_trace_event (trace_event.read addr n b))
             (fun addr n b => emit_trace_event (trace_event.write addr n b))

end x86_64
end linux


-- def lift_eval {α : Type *} |  evaluator α) : io a

-- def dump_state (s : system_state linux.x86_64.os_state) : IO Unit := do
--   let line := s.ip.pp_hex ++ ": " ++ s.print_regs ++ " " ++ s.print_set_flags;
--   IO.println line

def decode_loop (d : decodex86.decoder) : Nat -> linux.x86_64.system_m Unit
  | Nat.zero      => throwS "Out of fuel"
  | (Nat.succ n)  => do
  -- dump_state s;
  s <- get;
  let inst := decodex86.decode d s.ip.to_nat;
  match inst with 
  | (Sum.inl b) => throwS "Unknown byte"
  | (Sum.inr i) => do
    -- IO.println (repr i);
    modify (fun (s : machine_state) => { s with ip := s.ip + bitvec.of_nat _ i.nbytes });
    monadLift (modify (fun (s' : linux.x86_64.os_state) => {s' with current_ip := s.ip}) : 
               linux.x86_64.base_system_m Unit);
    catch (eval_instruction linux.x86_64.system_m i)
          (fun e => do s' <- monadLift (get : linux.x86_64.base_system_m linux.x86_64.os_state);
                       _ <- s'.trace.reverse.mapM (fun (e : (machine_word × linux.x86_64.trace_event)) => 
                                                  IO.println (e.fst.pp_hex ++ " " ++ repr e.snd));
                       throwS ("Eval failed: (" ++ repr i ++ ") at " ++  s.ip.pp_hex ++ " "  ++ e));
    decode_loop n

def doit (elffile : String) : IO Unit := do
  ((Sigma.mk ehdr phdrs), init_mem) <- elf.read_info_from_file elffile;
  text_phdr <- (match get_text_segment ehdr phdrs with
                | none     => throwS "No executable segment"
                | (some p) => pure p);
  text_bytes <- (match init_mem.lookup_buffer (bitvec.of_nat 64 text_phdr.vaddr.toNat) with
                | none        => throwS "No text region"
                | some (_, b) => pure b);
  let entry := ehdr.entry.toNat;
  IO.println ("Entry is " ++ repr entry ++ " imm:" ++ repr (18446744073709551616 : Nat) 
                          ++ " exp:"    ++ repr (2 ^ 64)
                          ++ " mul:"  ++ repr (9223372036854775808 * 2) );
  let d := decodex86.mk_decoder text_bytes text_phdr.vaddr.toNat;
  let init_state :=  { machine_state.empty with 
                       ip := bitvec.of_nat _ ehdr.entry.toNat
                     , mem := memory.from_init init_mem };
  let init_state_abi := sysv_abi.x86_64.initialise init_state;
  let fuel : Nat := 100000; 
  r <- (decode_loop d fuel).run init_state_abi;
  match r with 
  | (Except.ok _) => pure ()
  | (Except.error e) => throwS ("Unexpected error: " ++ e)    

-- set_option profiler true
-- #eval doit ("../testfiles/two", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1544)
-- #eval doit ("../testfiles/mixed_mem", "../llvm-tablegen-support/llvm-tablegen-support", 1530, 1536)

-- #eval doit ("../../sample-binaries/tiny/test-conditional.x86_64-exe", "../llvm-tablegen-support/llvm-tablegen-support", 4194704, 4194711)

