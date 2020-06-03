
import SMTLIB.Syntax

import X86Semantics.Common
import X86Semantics.BackendAPI


namespace x86

namespace symbolic

axiom I_am_really_sorry3 : ∀(P : Prop),  P 

open mc_semantics
open mc_semantics.type
open SMTLIB (sort term smtM)

def bitvec (n : Nat) := term (SMTLIB.sort.bitvec n)
def memaddr := bitvec 64
def byte    := bitvec 8

namespace bitvec

def cong {n m : Nat} (pf : n = m) (x : bitvec n) : bitvec m :=
  @Eq.recOn _ _ (fun x _ => bitvec x) _ pf x

-- probably doesn't do what you want if not (w dvd n).  MSB as the first byte to follow Galois.Data.Bitvec
def split_list {n:Nat} (x : bitvec n) (w : Nat) : List (bitvec w) :=
  let idxs := (Nat.upto0_lt (n / w)).reverse;
  let ex1 : Nat -> bitvec w := fun ix =>
    (let b := ix * w; 
     let pf : (b + w - 1) + 1 - b = w := I_am_really_sorry3 _;
     let v : bitvec ((b + w - 1) + 1 - b) := SMTLIB.extract (b + w - 1) b x;
     bitvec.cong pf v);
  List.map ex1 idxs

protected
def concat_list_aux {n : Nat} : forall (m : Nat) (acc : bitvec m) (xs : List (bitvec n)), bitvec (m + n * xs.length) 
  | m, acc, [] => acc
  | m, acc, (x :: xs) => 
    let pf : (m + n + n * List.length xs) = (m + n * List.length (x :: xs)) := I_am_really_sorry3 _;
    bitvec.cong pf (concat_list_aux (m + n) (SMTLIB.concat acc x) xs)
  
def concat_list {n : Nat} : forall (xs : List (bitvec n)), bitvec (n * xs.length) 
  | []        => SMTLIB.bvimm 0 0 -- FIXME: shouldn't happen, or raise an error
  | (x :: xs) => let pf : (n + n * List.length xs) = (n * List.length (x :: xs)) := I_am_really_sorry3 _; 
                 bitvec.cong pf (bitvec.concat_list_aux n x xs)

-- Breaks if m == 0
def trunc {n : Nat} (m : Nat) (pf : m <= n) (x : bitvec n) : bitvec m :=
  if m = 0 
  then SMTLIB.bvimm _ 0 -- FIXME: will probably cause issues
  else (let pf' : (m - 1) + 1 - 0 = m := I_am_really_sorry3 _; 
        bitvec.cong pf' (SMTLIB.extract (m - 1) 0 x))

end bitvec

def memory_t := SMTLIB.sort.array (SMTLIB.sort.bitvec 64) (SMTLIB.sort.bitvec 8)
def memory := term memory_t

-- We use these to abstract over the actual implementation of read/store
structure StdLib :=
  (read_byte  : memaddr -> memory  -> byte)
  (store_byte : memaddr -> byte -> memory -> memory)

namespace memory

def store_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (bs : List byte) : memory := 
    (List.foldl (fun (v : memory × memaddr) b => (stdlib.store_byte v.snd b v.fst, SMTLIB.bvadd v.snd (SMTLIB.bvimm 64 1))) (m, addr) bs).fst

def read_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (n : Nat) : List byte :=
    List.map (fun i => stdlib.read_byte (SMTLIB.bvadd addr (SMTLIB.bvimm 64 i)) m) (Nat.upto0_lt n)

-- theorem read_bytes_length: forall {m} {stdlib} {addr} {n}, List.length (read_bytes m stdkub addr n) = n 
--   := I_am_really_sorry3 _; 

def store_word {n : Nat} (m : memory) (stdlib : StdLib) (addr : memaddr) (b : bitvec (8 * n)) : memory := 
  m.store_bytes stdlib addr (b.split_list 8).reverse 

def read_word (m : memory) (stdlib : StdLib) (addr : memaddr) (n : Nat) : bitvec (8 * n) :=
  let bs := m.read_bytes stdlib addr n;
  let w  : bitvec (8 * bs.length) := bitvec.concat_list bs;
  let pf : 8 * bs.length = 8 * n := I_am_really_sorry3 _;
  bitvec.cong pf w

end memory

def machine_word := bitvec 64
def s_bool       := term SMTLIB.sort.smt_bool

structure machine_state : Type :=
  (mem    : memory)
  (gpregs : Array machine_word) -- 16
  (flags  : Array s_bool) -- 32
  (ip     : machine_word)

namespace machine_state

-- Constructs an empty machine state, with 0 where we need a value.
-- def empty : machine_state := 
--   { mem    := memory.empty
--   , gpregs := mkArray 16 0
--   , flags  := mkArray 32 false
--   , ip     := 0
--   }

def get_gpreg  (s : machine_state) (idx : Fin 16) : machine_word := 
  -- FIXME
  if h : 16 = s.gpregs.size
  then Array.get s.gpregs (Eq.recOn h idx) else SMTLIB.bvimm _ 0

def update_gpreg (idx : Fin 16) (f : machine_word -> machine_word) (s : machine_state) : machine_state :=
  -- FIXME
  if h : 16 = s.gpregs.size 
  then { s with gpregs := Array.set s.gpregs (Eq.recOn h idx) (f (get_gpreg s idx)) }
  else s 

def get_flag  (s : machine_state) (idx : Fin 32) : s_bool := 
  if h : 32 = s.flags.size
  then Array.get s.flags (Eq.recOn h idx) else SMTLIB.false

def update_flag (idx : Fin 32) (f : s_bool -> s_bool) (s : machine_state) : machine_state :=
  if h : 32 = s.flags.size
  then { s with flags := Array.set s.flags (Eq.recOn h idx) (f (get_flag s idx)) }
  else s 

def store_word {n : Nat} (s : machine_state) (stdlib : StdLib) (addr : machine_word) (b : bitvec (8 * n)) : machine_state :=
  {s with mem := s.mem.store_word stdlib addr b }

def read_word (s : machine_state) (stdlib : StdLib) (addr : machine_word) (n : Nat) : bitvec (8 * n) :=
  s.mem.read_word stdlib addr n 

-- def print_regs (s : machine_state) : String :=
--   let lines := List.zipWith (fun n (r : bitvec 64) => if r = 0 then "" else (n ++ ": " ++ r.pp_hex ++ ", ")) reg.r64_names s.gpregs.toList;
--   String.join lines

-- def print_set_flags (s : machine_state) : String :=
--   let lines := List.zipWith (fun n (r : Bool) => if r then n else "") reg.flag_names s.flags.toList;
--   "[" ++ String.intercalate ", " (List.filter (fun s => s.length > 0) lines) ++ "]"

end machine_state
  
-- FIXME
inductive trace_event 
  | syscall : Nat -> List machine_word -> trace_event
  | read    : machine_word -> ∀(n:Nat), bitvec n -> trace_event
  | write   : machine_word -> ∀(n:Nat), bitvec n -> trace_event

-- def trace_event.repr : trace_event -> String 
--   | trace_event.syscall n args => 
--     let pfx := "syscall " ++ repr n ++ " " ++ repr args.length;
--     List.foldl (fun (s : String) (w : machine_word) => s ++ " " ++ w.pp_hex) pfx args
--   | trace_event.read addr n b  => "read " ++ addr.pp_hex ++ " " ++ repr n ++ " " ++ b.pp_hex
--   | trace_event.write addr n b => "write " ++ addr.pp_hex ++ " " ++ repr n ++ " " ++ b.pp_hex

-- instance trace_event_repr : HasRepr trace_event := ⟨trace_event.repr⟩

structure os_state :=
  (current_ip : machine_word)
  (trace : List (machine_word × trace_event))

def os_state.empty : os_state := os_state.mk (SMTLIB.bvimm _ 0) []

-- Stacking like this makes it easier to derive MonadState
def base_system_m := (StateT os_state (ExceptT String smtM))
def system_m := StateT machine_state base_system_m

instance : Monad base_system_m :=
  inferInstanceAs (Monad (StateT os_state (ExceptT String smtM)))

instance : MonadState os_state base_system_m :=
  inferInstanceAs (MonadState os_state (StateT os_state (ExceptT String smtM)))

instance : MonadExcept String base_system_m :=
  inferInstanceAs (MonadExcept String (StateT os_state (ExceptT String smtM)))

instance system_m.Monad : Monad system_m :=
  inferInstanceAs (Monad (StateT machine_state base_system_m))

instance system_m.MonadState : MonadState machine_state system_m :=
  inferInstanceAs (MonadState machine_state (StateT machine_state base_system_m))

instance system_m.MonadExcept : MonadExcept String system_m :=
  inferInstanceAs (MonadExcept String (StateT machine_state base_system_m))

instance : HasMonadLiftT base_system_m system_m :=
  inferInstanceAs (HasMonadLiftT base_system_m (StateT machine_state base_system_m))

def system_m.run {a : Type} (m : system_m a) (os : os_state) (s : machine_state) 
  : smtM (Except String ((a × machine_state) × os_state)) := do
  ((m.run s).run os).run

-- def system_m.run' {a : Type} (m : system_m a) (s : machine_state) : IO (Except String a) := 
--   do x <- m.run os_state.empty s;
--      pure 

def emit_trace_event (e : trace_event) : system_m Unit :=
  monadLift (modify (fun (s : os_state) => { s with trace := (s.current_ip, e) :: s.trace }) : base_system_m Unit)

-- FIXME: maybe factor out common stuff from concreteBackend
def symbolicBackend (stdlib : StdLib) : Backend :=
  { s_bv     := bitvec
  , s_bool   := s_bool

  , s_bv_imm   := SMTLIB.bvimm
  , s_bool_imm := fun b => if b then SMTLIB.true else SMTLIB.false

  , monad := system_m
  -- , Monad_backend := 
  -- , MonadExcept_backend := 
  
  , store_word := fun n addr v => do 
                  -- FIXME: might want to name the new state
                  emit_trace_event (trace_event.write addr _ v);
                  modify (fun s => machine_state.store_word s stdlib addr v)
  , read_word  := fun addr n => do
                  v <- (fun s => machine_state.read_word s stdlib addr n) <$> get;
                  emit_trace_event (trace_event.read addr _ v);
                  pure v
               
  , get_gpreg  := fun i => (fun s => machine_state.get_gpreg s i) <$> get
  , set_gpreg := fun i v => modify (machine_state.update_gpreg i (fun _ => v))
  , get_flag  :=  fun i => (fun s => machine_state.get_flag s i) <$> get
  , set_flag := fun i v => modify (machine_state.update_flag i (fun _ => v))
  
  , s_mux_bool := fun (b : s_bool) (x y : s_bool) => SMTLIB.smt_ite b x y
  , s_mux_bv   := fun {n : Nat} (b : s_bool) (x y : bitvec n) => SMTLIB.smt_ite b x y
  , s_mux_m    := fun (b : s_bool) x y => x -- FIXME!!!
  
  , s_not      := SMTLIB.not
  , s_or       := SMTLIB.or
  , s_and      := SMTLIB.and
  , s_xor      := SMTLIB.xor
 
  -- - Comparison
  , s_bveq     := fun {n : Nat} (x y : bitvec n) => SMTLIB.eq x y
  , s_bvult    := @SMTLIB.bvult
  , s_bvslt    := @SMTLIB.bvslt
  
  -- - Arithmetic
  , s_bvneg    := @SMTLIB.bvneg
  , s_bvnot    := @SMTLIB.bvnot
   
  , s_bvadd    := @SMTLIB.bvadd
  , s_bvsub    := @SMTLIB.bvsub
  , s_bvmul    := @SMTLIB.bvmul
  , s_bvudiv   := @SMTLIB.bvudiv 
  , s_bvurem   := @SMTLIB.bvurem
  , s_bvextract := fun (w i j : Nat) (x : bitvec w) => SMTLIB.extract i j x

  -- FIXME: use resize
  , s_sext    := fun (n m : Nat) (x : bitvec n) =>
                 if H : n ≤ m 
                 then (let pf : n + (m - n) = m := I_am_really_sorry3 _; 
                       bitvec.cong pf (SMTLIB.sign_extend (m - n) x))
                 else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

  , s_uext    := fun (n m : Nat) (x : bitvec n) =>
                 if H : n ≤ m 
                 then (let pf : n + (m - n) = m := I_am_really_sorry3 _; 
                       bitvec.cong pf (SMTLIB.zero_extend (m - n) x))
                 else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

  , s_trunc   := fun (n m : Nat) (x : bitvec n) =>
                 if H : m ≤ n
                 then bitvec.trunc m H x
                 else SMTLIB.bvimm _ 0 -- FIXME
  , s_bvappend := @SMTLIB.concat
  , s_bvgetbits  := fun {n : Nat} (off m : Nat) (x : bitvec n) => 
                    if m = 0
                    then SMTLIB.bvimm m 0
                    else (let pf : (off + m - 1) + 1 - off = m := I_am_really_sorry3 _;
                          bitvec.cong pf (SMTLIB.extract (off + m - 1) off x))

  , s_bvsetbits  := fun {n m : Nat} (off : Nat) (x : bitvec n) (bs : bitvec m) =>
                    SMTLIB.bvimm _ 0   -- FIXME
  , s_bvand      := @SMTLIB.bvand
  , s_bvor       := @SMTLIB.bvor
  , s_bvxor      := @SMTLIB.bvxor
  , s_bvshl      := @SMTLIB.bvshl
  , s_bvmsb      := fun (n : Nat) (x : bitvec n) => 
                    SMTLIB.eq (SMTLIB.extract (n - 1) (n - 1) x) (SMTLIB.bvimm _ 1)
  -- unsigned
  , s_bvlshr     := @SMTLIB.bvlshr
  -- signed
  , s_bvsshr     := @SMTLIB.bvashr
  , s_parity     := fun (n : Nat) (x : bitvec n) => SMTLIB.false -- FIXME
  , s_bit_test   := fun {wr wi : Nat} (x : bitvec wr) (y : bitvec wi) => SMTLIB.false -- FIXME
   
  -- System operations
  , s_os_transition := pure ()
  , s_get_ip        := (fun (s : machine_state) => s.ip) <$> get
  , s_set_ip        := fun x => modify (fun s => { s with ip := x })
  , s_read_cpuid    := pure ()

  } 

end symbolic
end x86
