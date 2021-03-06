import Init.System.IO
import Galois.Data.Bitvec
import Std.Data.RBMap
import X86Semantics.Common
import X86Semantics.BackendAPI
import X86Semantics.MachineMemory



namespace x86

open mc_semantics
open mc_semantics.type
open Std (RBMap RBMap.fromList)

axiom I_am_really_sorry2 : ∀(P : Prop),  P 

@[reducible]
def machine_word := bitvec 64

@[reducible]
def avx_word := bitvec avx_width

def bitvec.uext {n} (m : Nat) (p: n ≤ m) (x:bitvec n) : bitvec m :=
  bitvec.set_bits 0 0 x (I_am_really_sorry2 _) -- (begin simp, exact p end)
  
def bitvec.sext {n} (m : Nat) (p: n ≤ m) (x:bitvec n) : bitvec m :=
  bitvec.set_bits (if x.msb then (bitvec.zero m).not else 0) 0 x (I_am_really_sorry2 _)-- (begin simp, exact p end)

-- Returns the number of bits that are tt mod 2
def bitvec.parity {n : Nat} (b : bitvec n) : Bool :=
  bitvec.foldl (λx y => not (x == y)) false b

-- example : bitvec.parity (3 : bitvec 4) = false := by refl
-- example : bitvec.parity (7 : bitvec 4) = true := by refl

def bitvec.trunc {n} (m : Nat) (p: m ≤ n) (x:bitvec n) : bitvec m :=
  bitvec.get_bits x 0 m (I_am_really_sorry2 _) --(begin simp, exact p end)

def bit_to_bitvec (n : Nat) (b : Bool) : bitvec n := 
  if b then 1 else 0


structure machine_state : Type :=
  (mem    : memory)
  (gpregs : Array machine_word) -- 16
  (flags  : Array Bool) -- 32
  (avxregs : Array avx_word)
  (ip     : machine_word)


namespace machine_state

-- Constructs an empty machine state, with 0 where we need a value.
def empty : machine_state := 
  { mem    := memory.empty
  , gpregs := mkArray 16 0
  , flags  := mkArray 32 false
  , avxregs := mkArray 16 0
  , ip     := 0
  }

def get_gpreg  (s : machine_state) (idx : Fin 16) : machine_word := 
  -- FIXME
  if h : 16 = s.gpregs.size
  then s.gpregs.get (cast (congrArg Fin h) idx)
  else 0

def update_gpreg (idx : Fin 16) (f : machine_word -> machine_word) (s : machine_state) : machine_state :=
  -- FIXME
  if h : 16 = s.gpregs.size 
  then { s with gpregs := s.gpregs.set (cast (congrArg Fin h) idx) (f (get_gpreg s idx)) }
  else s 

def get_flag  (s : machine_state) (idx : Fin 32) : Bool := 
  if h : 32 = s.flags.size
  then s.flags.get (cast (congrArg Fin h) idx)
  else false

def update_flag (idx : Fin 32) (f : Bool -> Bool) (s : machine_state) : machine_state :=
  if h : 32 = s.flags.size
  then { s with flags := s.flags.set (cast (congrArg Fin h) idx) (f (get_flag s idx)) }
  else s 

def get_avxreg  (s : machine_state) (idx : Fin 16) : avx_word := 
  -- FIXME
  if h : 16 = s.avxregs.size
  then s.avxregs.get (cast (congrArg _ h) idx) else 0

def update_avxreg (idx : Fin 16) (f : avx_word -> avx_word) (s : machine_state) : machine_state :=
  -- FIXME
  if h : 16 = s.avxregs.size 
  then { s with avxregs := s.avxregs.set (cast (congrArg _ h) idx) (f (get_avxreg s idx)) }
  else s 

-- def store_bytes (addr : machine_word) (bs : List (bitvec 8)) (s : machine_state) : machine_state := 
--   { s with mem := s.mem.store_bytes addr bs }

-- def read_bytes (s : machine_state) (addr : machine_word) (n : Nat) : Option (List (bitvec 8)) :=
--   s.mem.read_bytes addr n

-- lemma read_bytes_length {s : machine_state} {addr : machine_word} {n : Nat} {bs : List (bitvec 8)}
--   : read_bytes s addr n = some bs -> bs.length = n := memory.read_bytes_length

def store_word {n : Nat} (s : machine_state) (addr : machine_word) (b : bitvec (8 * n)) : machine_state :=
  {s with mem := s.mem.store_word addr b }

def read_word (s : machine_state) (addr : machine_word) (n : Nat) : bitvec (8 * n) := do
  match s.mem.read_word addr n with     
  | some v => v
  | none   => bitvec.of_nat _ 0 -- FIXME


def print_regs (s : machine_state) : String :=
  let lines := List.zipWith (fun n (r : bitvec 64) => if r = 0 then "" else (n ++ ": " ++ r.pp_hex ++ ", ")) reg.r64_names s.gpregs.toList;
  String.join lines

def print_set_flags (s : machine_state) : String :=
  let lines := List.zipWith (fun n (r : Bool) => if r then n else "") reg.flag_names s.flags.toList;
  "[" ++ String.intercalate ", " (List.filter (fun s => s.length > 0) lines) ++ "]"

end machine_state

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
    let rsp_idx : Fin 16 := Fin.ofNat 4; -- FIXME
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

protected
def trace_event.repr : trace_event -> String 
  | trace_event.syscall n args => 
    let pfx := "syscall " ++ reprStr n ++ " " ++ reprStr args.length;
    List.foldl (fun (s : String) (w : machine_word) => s ++ " " ++ w.pp_hex) pfx args
  | trace_event.read addr n b  => "read " ++ addr.pp_hex ++ " " ++ reprStr n ++ " " ++ b.pp_hex
  | trace_event.write addr n b => "write " ++ addr.pp_hex ++ " " ++ reprStr n ++ " " ++ b.pp_hex

-- FIXME: behave wrt prec
instance trace_event_repr : Repr trace_event := ⟨fun te _n => trace_event.repr te⟩

structure os_state :=
  (current_ip : machine_word)
  (trace : List (machine_word × trace_event))

def os_state.empty : os_state := os_state.mk 0 []

-- Stacking like this makes it easier to derive MonadState
abbrev base_system_m := StateT os_state IO
abbrev system_m := StateT machine_state base_system_m


namespace base_system_m

instance : MonadLiftT IO base_system_m :=
  inferInstanceAs (MonadLiftT IO (StateT os_state IO))

end base_system_m

namespace system_m

instance : MonadLiftT IO system_m :=
  inferInstanceAs (MonadLiftT IO (StateT machine_state base_system_m))

def throwString {α} (err : String) : system_m α := throw $ IO.userError err
def catchString {α} (m : system_m α) (h : String → system_m α) : system_m α := 
  let handler : IO.Error → system_m α := 
    λ e => match e with
           | IO.Error.userError msg => h msg
           | _ => throw e;
  tryCatch m handler

-- FIXME `MonadIO` now requires a `MonadExcept IO.Error` instance,
-- which means we now have two `MonadExcept _` instances for system_m,
-- which can be a pain to deal with.
instance : MonadExcept String system_m :=
  {throw := @system_m.throwString,
   tryCatch := @system_m.catchString }

end system_m

protected
def system_m.run {a : Type} (m : system_m a) (os : os_state) (s : machine_state) 
  : IO (Except String ((a × machine_state) × os_state)) :=
  λ rw => match ((m.run s).run os).run rw with
          | EStateM.Result.ok a rw'    => EStateM.Result.ok (Except.ok a) rw'
          | EStateM.Result.error (IO.Error.userError msg) rw' => EStateM.Result.ok (Except.error msg) rw'
          | EStateM.Result.error e rw' => EStateM.Result.error e rw'


def emit_trace_event (e : trace_event) : system_m Unit :=
  monadLift (modify (fun (s : os_state) => { s with trace := (s.current_ip, e) :: s.trace }) : base_system_m Unit)

-- Linux calling conv: %rdi, %rsi, %rdx, %r10, %r8 and %r9, with %rax holding syscall number.

-- FIXME: these should maybe be in common?

def rax_idx : Fin 16 := Fin.ofNat 0
def rcx_idx : Fin 16 := Fin.ofNat 1
def rdx_idx : Fin 16 := Fin.ofNat 2
def rbx_idx : Fin 16 := Fin.ofNat 3
def rsp_idx : Fin 16 := Fin.ofNat 4
def rbp_idx : Fin 16 := Fin.ofNat 5
def rsi_idx : Fin 16 := Fin.ofNat 6
def rdi_idx : Fin 16 := Fin.ofNat 7
def r8_idx  : Fin 16 := Fin.ofNat 8
def r9_idx  : Fin 16 := Fin.ofNat 9
def r10_idx : Fin 16 := Fin.ofNat 10
def r11_idx : Fin 16 := Fin.ofNat 11
def r12_idx : Fin 16 := Fin.ofNat 12
def r13_idx : Fin 16 := Fin.ofNat 13
def r14_idx : Fin 16 := Fin.ofNat 14
def r15_idx : Fin 16 := Fin.ofNat 15

-- def simple_syscall (f : system_state os_state -> machine_word) : system_m Unit :=
--   modify (fun s => { s with machine_state := s.machine_state.update_gpreg rax_idx (fun _ => f s) })

def emit_syscall_trace (syscall_no : Nat) (args : List machine_word) : system_m Unit :=
    emit_trace_event (trace_event.syscall syscall_no args)

def raw_syscall {a : Type} (f : machine_word -> machine_word -> machine_word -> machine_word -> machine_word -> machine_word -> system_m a)
  : system_m a := do
  let s ← get
  f (s.get_gpreg rdi_idx)
    (s.get_gpreg rsi_idx)
    (s.get_gpreg rdx_idx)
    (s.get_gpreg r10_idx)
    (s.get_gpreg r8_idx)
    (s.get_gpreg r9_idx)

def syscall0 (sys_f : system_m machine_word)
             (syscall_no : Nat) 
             : system_m Unit := do
  let res ← raw_syscall (fun _ _ _ _ _ _ => do emit_syscall_trace syscall_no []; sys_f)
  modify (machine_state.update_gpreg rax_idx (fun _ => res))

def syscall1 (sys_f : machine_word -> system_m machine_word) 
             (syscall_no : Nat)
             : system_m Unit := do
  let res ← raw_syscall (fun a _ _ _ _ _ => do emit_syscall_trace syscall_no [a]; sys_f a)
  modify (machine_state.update_gpreg rax_idx (fun _ => res))

def syscall3 (sys_f : machine_word -> machine_word -> machine_word -> system_m machine_word) 
             (syscall_no : Nat)
             : system_m Unit := do
  let res ← raw_syscall (fun a b c _ _ _ => do emit_syscall_trace syscall_no [a, b, c]; sys_f a b c)
  modify (machine_state.update_gpreg rax_idx (fun _ => res))

def syscall6 (sys_f : machine_word -> machine_word -> machine_word -> machine_word -> machine_word -> machine_word -> system_m machine_word) 
             (syscall_no : Nat)
             : system_m Unit := do
  let res ← raw_syscall (fun a b c d e f => do emit_syscall_trace syscall_no [a, b, c, d, e, f]; sys_f a b c d e f)
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
               let s ←  get
               let m_bytes := s.mem.read_bytes buf nbytes.to_nat
               match m_bytes with
               | none      => throw ("sys_write: unable to read " ++ nbytes.to_nat.repr ++ " bytes at " ++ buf.pp_hex)
               | (some bs) => if filedes = 1 
                              then do let str := String.mk (bs.map (fun (b : byte) => Char.ofNat b.toNat))
                                      IO.print str
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
  let s ← get
  let syscall_no := (s.get_gpreg rax_idx).to_nat
  match syscalls.find? syscall_no with
  | none     => throw ("Unknown syscall: " ++ reprStr syscall_no)
  | (some m) => m syscall_no


def set_reg32 (idx : Fin 16) (x : bitvec 32) : system_m Unit :=
  modify (machine_state.update_gpreg rax_idx (fun _ => bitvec.uresize x 64))

-- FIXME: a hack
def read_cpuid : system_m Unit := do
  -- Copied from the cpuid results from my macbook
  -- Note: CPUID is allowed to return 0s 
  let cpuid_values : RBMap Nat (Nat × Nat × Nat × Nat) (fun x y => decide (x < y)) :=
    RBMap.fromList [ (0, (0xd, 0x756e6547, 0x6c65746e, 0x49656e69))
                    , (1, (0x40661, 0x2100800, 0x7ffafbff, 0xbfebfbff))
                    , (2, (0x76036301, 0xf0b5ff, 0x0, 0xc10000))
                    , (3, (0x0, 0x0, 0x0, 0x0))
                    , (4, (0x1c004121, 0x1c0003f, 0x3f, 0x0))
                    , (5, (0x40, 0x40, 0x3, 0x42120))
                    , (6, (0x77, 0x2, 0x9, 0x0))
                    , (7, (0x0, 0x27ab, 0x0, 0x9c000000))
                    , (8, (0x0, 0x0, 0x0, 0x0))
                    , (9, (0x0, 0x0, 0x0, 0x0))
                    , (10, (0x7300403, 0x0, 0x0, 0x603))
                    , (11, (0x1, 0x2, 0x100, 0x6))
                    , (12, (0x0, 0x0, 0x0, 0x0))
                    , (13, (0x7, 0x340, 0x340, 0x0))
                    , (2147483648, (0x80000008, 0x0, 0x0, 0x0))
                    , (2147483649, (0x0, 0x0, 0x21, 0x2c100800))
                    , (2147483650, (0x65746e49, 0x2952286c, 0x726f4320, 0x4d542865))
                    , (2147483651, (0x37692029, 0x3839342d, 0x20514830, 0x20555043))
                    , (2147483652, (0x2e322040, 0x48473038, 0x7a, 0x0))
                    , (2147483653, (0x0, 0x0, 0x0, 0x0))
                    , (2147483654, (0x0, 0x0, 0x1006040, 0x0))
                    , (2147483655, (0x0, 0x0, 0x0, 0x100))
                    , (2147483656, (0x3027, 0x0, 0x0, 0x0))
                    ] (fun x y => decide (x < y)) -- FIXME: we need to look at rcx sometimes as well
  let cpuid_fn (n : Nat) : (Nat × Nat × Nat × Nat) :=
      match cpuid_values.find? n with
      | none     => (0, 0, 0, 0)
      | (some r) => r
   let s ← get
   let raxv :=  bitvec.uresize (s.get_gpreg rax_idx) 32
   match cpuid_fn raxv.to_nat with 
   | (axv, bxv, cxv, dxv) => do
     set_reg32 rax_idx (bitvec.of_nat 32 axv)
     set_reg32 rbx_idx (bitvec.of_nat 32 bxv)
     set_reg32 rcx_idx (bitvec.of_nat 32 cxv)
     set_reg32 rdx_idx (bitvec.of_nat 32 dxv) 

end x86_64
end linux

section in_linux

open linux.x86_64


def concreteBackend : Backend :=
  { s_bv     := bitvec
  , s_bool   := Bool
  , s_float  := fun (fc : float_class) => bitvec fc.width

  , s_bv_imm := bitvec.of_nat
  , s_bool_imm := fun b => b

  , monad := linux.x86_64.system_m
  , Monad_backend := inferInstance
  , MonadExcept_backend := inferInstance
  
  , store_word := fun n addr v => do 
                  emit_trace_event (trace_event.write addr _ v)
                  modify (fun s => machine_state.store_word s addr v)
  , read_word  := fun addr n => do
                  let v ← (fun s => machine_state.read_word s addr n) <$> get
                  emit_trace_event (trace_event.read addr _ v)
                  pure v
               
  , get_gpreg  := fun i => (fun s => machine_state.get_gpreg s i) <$> get
  , s_cond_set_gpreg := fun c i v => do
    if c then modify (machine_state.update_gpreg i (fun _ => v))
  , get_flag  :=  fun i => (fun s => machine_state.get_flag s i) <$> get
  , s_cond_set_flag := fun c i v => do
    if c then modify (machine_state.update_flag i (fun _ => v))
  , get_avxreg := fun i => (fun s => machine_state.get_avxreg s i) <$> get
  , s_cond_set_avxreg := fun c i v => do
    if c then modify (machine_state.update_avxreg i (fun _ => v))

  , s_mux_bool := fun (b : Bool) (x y : Bool) => if b then x else y
  , s_mux_bv   := fun {n : Nat} (b : Bool) (x y : bitvec n) => if b then x else y
  , s_mux_float := fun {fc : float_class} (b : Bool) (x y : bitvec fc.width) => if b then x else y
  
  , s_not      := not
  , s_or       := or
  , s_and      := and
  , s_xor      := (λx y => not (x == y))
 
  -- - Comparison
  , s_bveq     := fun {n : Nat} x y => decide (x = y)
  , s_bvult    := fun {n : Nat} x y => decide (bitvec.ult x y)
  , s_bvslt    := fun {n : Nat} x y => decide (bitvec.slt x y)
  
  -- - Arithmetic
  , s_bvneg    := @bitvec.neg
  , s_bvnot    := @bitvec.not
   
  , s_bvadd    := @bitvec.add
  , s_bvsub    := @bitvec.sub
  , s_bvmul    := @bitvec.mul
  , s_bvudiv   := fun (n : Nat) (x y : bitvec n) => bitvec.of_nat n 0 -- FIXME
  , s_bvurem   := fun (n : Nat) (x y : bitvec n) => bitvec.of_nat n 0 -- FIXME
  , s_bvextract := fun {w : Nat} (i j : Nat) (x : bitvec w) =>
                       let n := i + 1 - j;
                       if H : w = w - n + n 
                       then bitvec.slice i j (w - n) H x
                       else bitvec.of_nat _ 0 -- FIXME

  -- FIXME: use resize
  , s_sext    := fun (n m : Nat) (x : bitvec n) =>
                 if H : n ≤ m 
                 then bitvec.sext m H x
                 else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

  , s_uext    := fun (n m : Nat) (x : bitvec n) =>
                 if H : n ≤ m 
                 then bitvec.sext m H x
                 else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

  , s_trunc   := fun (n m : Nat) (x : bitvec n) =>
                 if H : m ≤ n
                 then bitvec.trunc m H x
                 else bitvec.of_nat _ 0 -- FIXME
  , s_bvappend := @bitvec.append
  , s_bvgetbits  := fun {n : Nat} (off m : Nat) (x : bitvec n) => 
                    bitvec.get_bits (bitvec.uresize x (off + m)) off m (Nat.leRefl _)

  , s_bvsetbits  := fun {n m : Nat} (off : Nat) (x : bitvec n) (bs : bitvec m) =>
                    if H : off + m ≤ n 
                    then bitvec.set_bits x off bs H
                    else bitvec.of_nat _ 0   -- FIXME
  , s_bvand      := @bitvec.and
  , s_bvor       := @bitvec.or
  , s_bvxor      := @bitvec.xor
  , s_bvshl      := fun (n : Nat) ( x y : bitvec n) => bitvec.shl x (y.to_nat)
  , s_bvmsb      := @bitvec.msb
  -- unsigned
  , s_bvlshr     := fun {n : Nat} ( x y : bitvec n) => bitvec.ushr x (y.to_nat)
  -- signed
  , s_bvsshr     := fun {n : Nat} ( x y : bitvec n) => bitvec.sshr x (y.to_nat)
  , s_parity     := @bitvec.parity
  , s_bit_test   := fun {wr wi : Nat} (x : bitvec wr) (y : bitvec wi) =>
                        bitvec.nth x (y.to_nat)
   
  -- System operations
  , s_os_transition := linux.x86_64.syscall_handler
  , s_get_ip        := (fun (s : machine_state) => s.ip) <$> get
  , s_set_ip        := fun x => modify (fun s => { s with ip := x })
  , s_cond_set_ip   := fun b x => do if b then modify (fun s => { s with ip := x })

  -- FP, all currently stubbed out
  , s_fp_literal := fun (_fc : float_class) (_m : Nat) (_esign : Bool) (_e : Nat) => 
                    panic! "s_fp_literal unimplemented"
  , s_bv_bitcast_to_fp := fun (fc : float_class) _ =>
                       panic! "s_bv_bitcast_to_fp unimplemented"
  
  , s_fp_bitcast_to_bv := fun (_fc : float_class) _ => 
                       panic! "s_fp_bitcast_to_bv unimplemented"

  , s_fp_convert_to_fp := fun (_sfc _dfc : float_class) (_rm : RoundingMode) _ =>
                       panic! "s_fp_convert_to_fp unimplemented"

  , s_fp_convert_to_int := fun (_fc : float_class) (_is32or64 : Bool) (_rm : RoundingMode) _ =>
                       panic! "s_fp_convert_to_int unimplemented"

  , s_int_convert_to_fp := fun (_fc : float_class) (_is32or64 : Bool) _ =>
                       panic! "s_int_convert_to_fp unimplemented"

  , s_fp_add  := fun (_fc : float_class) _ _ => panic! "s_fp_add unimplemented"

  , s_fp_sub  := fun (_fc : float_class) _ _ => panic! "s_fp_add unimplemented"
  , s_fp_mul  := fun (_fc : float_class) _ _ => panic! "s_fp_sub unimplemented"
  , s_fp_div  := fun (_fc : float_class) _ _ => panic! "s_fp_div unimplemented"
  , s_fp_sqrt := fun (_fc : float_class) _   => panic! "s_fp_sqrt unimplemented"

  , s_fp_le := fun (_fc : float_class) _ _ => panic! "s_fp_le unimplemented"
  , s_fp_lt := fun (_fc : float_class) _ _ => panic! "s_fp_lt unimplemented"

  , s_fp_max     := fun (_fc : float_class) _ _ => panic! "s_fp_max unimplemented"
  , s_fp_min     := fun (_fc : float_class) _ _ => panic! "s_fp_min unimplemented"
  , s_fp_ordered := fun (_fc : float_class) _ _ => panic! "s_fp_ordered unimplemented"

  , s_read_cpuid    := linux.x86_64.read_cpuid

  } 

end in_linux

end x86
