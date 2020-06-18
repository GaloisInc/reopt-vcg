
import SMTLIB.Syntax

import X86Semantics.Common
import X86Semantics.BackendAPI


namespace x86

namespace symbolic

axiom I_am_really_sorry3 : ∀(P : Prop),  P 

open mc_semantics
open mc_semantics.type
open SMT (sort term smtM command)

abbrev bitvec (n : Nat) := term (SMT.sort.bitvec n)
def s_bool              := term SMT.sort.smt_bool

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
     let v : bitvec ((b + w - 1) + 1 - b) := SMT.extract (b + w - 1) b x;
     bitvec.cong pf v);
  List.map ex1 idxs

protected
def concat_list_aux {n : Nat} : forall (m : Nat) (acc : bitvec m) (xs : List (bitvec n)), bitvec (m + n * xs.length) 
  | m, acc, [] => acc
  | m, acc, (x :: xs) => 
    let pf : (m + n + n * List.length xs) = (m + n * List.length (x :: xs)) := I_am_really_sorry3 _;
    bitvec.cong pf (concat_list_aux (m + n) (SMT.concat acc x) xs)
  
def concat_list {n : Nat} : forall (xs : List (bitvec n)), bitvec (n * xs.length) 
  | []        => SMT.bvimm 0 0 -- FIXME: shouldn't happen, or raise an error
  | (x :: xs) => let pf : (n + n * List.length xs) = (n * List.length (x :: xs)) := I_am_really_sorry3 _; 
                 bitvec.cong pf (bitvec.concat_list_aux n x xs)

-- Breaks if m == 0
def trunc {n : Nat} (m : Nat) (pf : m <= n) (x : bitvec n) : bitvec m :=
  if m = 0 
  then SMT.bvimm _ 0 -- FIXME: will probably cause issues
  else (let pf' : (m - 1) + 1 - 0 = m := I_am_really_sorry3 _; 
        bitvec.cong pf' (SMT.extract (m - 1) 0 x))

def uresize (n m : Nat) (x : bitvec n) : bitvec m :=
  if H : n ≤ m 
  then (let pf : n + (m - n) = m := I_am_really_sorry3 _; 
       bitvec.cong pf (SMT.zero_extend (m - n) x))
  else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

def sresize (n m : Nat) (x : bitvec n) : bitvec m :=
  if H : n ≤ m 
  then (let pf : n + (m - n) = m := I_am_really_sorry3 _; 
       bitvec.cong pf (SMT.sign_extend (m - n) x))
  else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

-- There may be a more efficient way of doing this (e.g. slicing and concat)
def set_bits {n} (x:bitvec n) (i:Nat) {m} (y:bitvec m) (p:i+m ≤ n) : bitvec n :=
  let premask := SMT.bvshl (uresize _ n (SMT.repeat m (SMT.bvimm 1 1)))
                              (SMT.bvimm _ i);
  let mask    := SMT.bvnot premask;
  let bits := SMT.bvshl (uresize _ n y) (SMT.bvimm _ i);
  SMT.bvor (SMT.bvand x mask) bits

def to_bool (b : bitvec 1) : s_bool := SMT.eq b (SMT.bvimm _ 1)

end bitvec

abbrev memory_t := SMT.sort.array (SMT.sort.bitvec 64) (SMT.sort.bitvec 8)
def memory := term memory_t

-- We use these to abstract over the actual implementation of read/store
structure StdLib :=
  (read_byte  : memaddr -> memory  -> byte)
  (store_byte : memaddr -> byte -> memory -> memory)

namespace StdLib

def make : smtM StdLib := do
  rb <- SMT.define_fun "read_byte" [SMT.sort.bitvec 64, memory_t] (SMT.sort.bitvec 8)
        (fun addr mem => SMT.select _ _ mem addr);
  sb <- SMT.define_fun "write_byte" [SMT.sort.bitvec 64, SMT.sort.bitvec 8, memory_t] memory_t
        (fun addr b mem => SMT.store _ _ mem addr b);
  pure { read_byte := rb, store_byte := sb }

end StdLib

namespace memory

def store_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (bs : List byte) : memory := 
    (List.foldl (fun (v : memory × memaddr) b => (stdlib.store_byte v.snd b v.fst, SMT.bvadd v.snd (SMT.bvimm 64 1))) (m, addr) bs).fst

def read_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (n : Nat) : List byte :=
    List.map (fun i => stdlib.read_byte (SMT.bvadd addr (SMT.bvimm 64 i)) m) (Nat.upto0_lt n)

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
  then Array.get s.gpregs (Eq.recOn h idx) else SMT.bvimm _ 0

def update_gpreg (idx : Fin 16) (f : machine_word -> machine_word) (s : machine_state) : machine_state :=
  -- FIXME
  if h : 16 = s.gpregs.size 
  then { s with gpregs := Array.set s.gpregs (Eq.recOn h idx) (f (get_gpreg s idx)) }
  else s 

def get_flag  (s : machine_state) (idx : Fin 32) : s_bool := 
  if h : 32 = s.flags.size
  then Array.get s.flags (Eq.recOn h idx) else SMT.false

def update_flag (idx : Fin 32) (f : s_bool -> s_bool) (s : machine_state) : machine_state :=
  if h : 32 = s.flags.size
  then { s with flags := Array.set s.flags (Eq.recOn h idx) (f (get_flag s idx)) }
  else s 

def store_word {n : Nat} (s : machine_state) (stdlib : StdLib) (addr : machine_word) (b : bitvec (8 * n)) : machine_state :=
  {s with mem := s.mem.store_word stdlib addr b }

def read_word (s : machine_state) (stdlib : StdLib) (addr : machine_word) (n : Nat) : bitvec (8 * n) :=
  s.mem.read_word stdlib addr n 

def print_regs (s : machine_state) : String :=
  let lines := List.zipWith (fun n (r : bitvec 64) => (n ++ ": " ++ toString (toSExpr r) ++ ", ")) reg.r64_names s.gpregs.toList;
  String.join lines

-- def print_set_flags (s : machine_state) : String :=
--   let lines := List.zipWith (fun n (r : Bool) => if r then n else "") reg.flag_names s.flags.toList;
--   "[" ++ String.intercalate ", " (List.filter (fun s => s.length > 0) lines) ++ "]"


-- Constructs a new machine state where all the elements are fresh constants
-- FIXME: could use sz = ns.length
protected 
def declare_const_aux {s : sort} (ns : List String) (sz : Nat) : smtM (Array (term s)) := do
  let base := mkArray sz 0;
  let f    := fun n (_ : Nat) => SMT.declare_fun (List.getD n ns "el") [] s;
  Array.mapIdxM f base

def declare_const : smtM machine_state := do
  mem   <- SMT.declare_fun "memory" [] memory_t;
  gprs  <- machine_state.declare_const_aux reg.r64_names 16;
  flags <- machine_state.declare_const_aux reg.flag_names 32;
  ip    <- SMT.declare_fun "ip" [] (SMT.sort.bitvec 64);
  pure { mem := mem, gpregs := gprs, flags := flags, ip := ip }

end machine_state

inductive Event
  | Command : SMT.command -> Event
  | Warning : String -> Event
  | Read  : memaddr -> Nat -> Event
  | Write : memaddr -> forall (n : Nat), bitvec n -> Event

namespace Event

protected
def repr : Event -> String
  | Command c   => toString (toSExpr c)
  | Warning w   => "Warning: "  ++ w
  | Read _ _    => "Read"
  | Write _ _ _ => "Write"

instance : HasRepr Event := ⟨Event.repr⟩

end Event

  --   -- ^ We added a warning about an issue in the VCG
  -- | MCOnlyStackReadEvent : memaddr -> Nat -> Event -- SMT.Term !(MemRepr tp) !Var
  --   -- ^ `MCOnlyReadEvent a w v` indicates that we read `w` bytes
  --   -- from `a`, and assign the value returned to `v`.  This only
  --   -- appears in the binary code.
  -- | forall tp . JointStackReadEvent !SMT.Term !(MemRepr tp) !Var !Ann.LocalIdent
  --   -- ^ `JointReadEvent a w v llvmAlloca` indicates that we read `w` bytes from `a`,
  --   -- and assign the value returned to `v`.  This appears in the both the binary
  --   -- and LLVM.  The alloca name refers to the LLVM allocation this is part of,
  --   -- and otherwise this is a binary only read.
  -- | forall tp . NonStackReadEvent !SMT.Term !(MemRepr tp) !Var
  --   -- ^ `NonStackReadEvent a w v` indicates that we read `w` bytes
  --   -- from `a`, and assign the value returned to `v`.  The address `a` should not
  --   -- be in the stack.
  -- | forall tp . MCOnlyStackWriteEvent !SMT.Term !(MemRepr tp) !SMT.Term
  --   -- ^ `MCOnlyStackWriteEvent a tp v` indicates that we write the `w` byte value `v`  to `a`.
  --   --
  --   -- This has side effects, so we record the event.
  -- | forall tp . JointStackWriteEvent !SMT.Term !(MemRepr tp) !SMT.Term !Ann.LocalIdent
  --   -- ^ `JointStackWriteEvent a w v` indicates that we write the `w` byte value `v`  to `a`.
  --   -- The write affects the alloca pointed to by Allocaname.
  --   --
  --   -- This has side effects, so we record the event.
  -- | forall tp . NonStackWriteEvent !SMT.Term !(MemRepr tp) !SMT.Term
  --   -- ^ `NonStackWriteEvent a w v` indicates that we write the `w` byte value `v`  to `a`.  The
  --   -- address `a` should not be in the stack.
  --   --
  --   -- This has side effects, so we record the event.
  -- | forall ids . FetchAndExecuteEvent !EvalContext !(RegState (ArchReg X86_64) (Value X86_64 ids))
  --   -- ^ A fetch and execute

-- def trace_event.repr : trace_event -> String 
--   | trace_event.syscall n args => 
--     let pfx := "syscall " ++ repr n ++ " " ++ repr args.length;
--     List.foldl (fun (s : String) (w : machine_word) => s ++ " " ++ w.pp_hex) pfx args
--   | trace_event.read addr n b  => "read " ++ addr.pp_hex ++ " " ++ repr n ++ " " ++ b.pp_hex
--   | trace_event.write addr n b => "write " ++ addr.pp_hex ++ " " ++ repr n ++ " " ++ b.pp_hex

-- instance trace_event_repr : HasRepr trace_event := ⟨trace_event.repr⟩

structure os_state :=
  (current_ip : machine_word)
  (nextFresh  : Nat)
  (trace : List Event)

def os_state.empty : os_state := os_state.mk (SMT.bvimm _ 0) 0 []

-- Stacking like this makes it easier to derive MonadState
def base_system_m := (StateT os_state (ExceptT String Id))
def system_m := StateT machine_state base_system_m

instance : Monad base_system_m :=
  inferInstanceAs (Monad (StateT os_state (ExceptT String Id)))

instance : MonadState os_state base_system_m :=
  inferInstanceAs (MonadState os_state (StateT os_state (ExceptT String Id)))

instance : MonadExcept String base_system_m :=
  inferInstanceAs (MonadExcept String (StateT os_state (ExceptT String Id)))

instance system_m.Monad : Monad system_m :=
  inferInstanceAs (Monad (StateT machine_state base_system_m))

instance system_m.MonadState : MonadState machine_state system_m :=
  inferInstanceAs (MonadState machine_state (StateT machine_state base_system_m))

instance system_m.MonadExcept : MonadExcept String system_m :=
  inferInstanceAs (MonadExcept String (StateT machine_state base_system_m))

instance : HasMonadLiftT base_system_m system_m :=
  inferInstanceAs (HasMonadLiftT base_system_m (StateT machine_state base_system_m))


namespace system_m

def run {a : Type} (m : system_m a) (os : os_state) (s : machine_state) 
  : (Except String ((a × machine_state) × os_state)) := do
  ((m.run s).run os).run

def runsmtM {a : Type} (m : smtM a) : system_m a := do
  let run' := fun (s : os_state) => 
                  (let r := SMT.runsmtM s.nextFresh m;
                  (r.fst, {s with trace := (List.map Event.Command r.snd.snd.reverse) ++ s.trace
                          , nextFresh   := r.snd.fst}));
  monadLift (modifyGet run' : base_system_m a)

def name_term {s : sort} (name : Option String) (tm : term s) : system_m (term s) :=
  runsmtM (SMT.name_term (name.getD "tmp") tm)

end system_m

-- def system_m.run' {a : Type} (m : system_m a) (s : machine_state) : IO (Except String a) := 
--   do x <- m.run os_state.empty s;
--      pure 

def emit_event (e : Event) : system_m Unit :=
  monadLift (modify (fun (s : os_state) => { s with trace := e :: s.trace }) : base_system_m Unit)

-- FIXME: maybe factor out common stuff from concreteBackend
def symbolicBackend (stdlib : StdLib) : Backend :=
  { s_bv     := bitvec
  , s_bool   := s_bool

  , s_bv_imm   := SMT.bvimm
  , s_bool_imm := fun b => if b then SMT.true else SMT.false

  , monad := system_m
  -- , Monad_backend := 
  -- , MonadExcept_backend := 
  
  , store_word := fun n addr v => do 
                  -- FIXME: might want to name the new state
                  -- emit_trace_event (trace_event.write addr _ v);
                  addr' <- system_m.name_term (some "addr") addr;
                  modify (fun s => machine_state.store_word s stdlib addr' v)
  , read_word  := fun addr n => do
                  addr' <- system_m.name_term (some "addr") addr;
                  v <- (fun s => machine_state.read_word s stdlib addr' n) <$> get;
                  -- emit_trace_event (trace_event.read addr _ v);
                  pure v
               
  , get_gpreg  := fun i => (fun s => machine_state.get_gpreg s i) <$> get
  , set_gpreg := fun i v => do s <- system_m.name_term (reg.r64_names.get? i.val) v;
                               modify (machine_state.update_gpreg i (fun _ => s))
  , get_flag  :=  fun i => (fun s => machine_state.get_flag s i) <$> get
  , set_flag := fun i v => modify (machine_state.update_flag i (fun _ => v))
  
  , s_mux_bool := fun (b : s_bool) (x y : s_bool) => SMT.smt_ite b x y
  , s_mux_bv   := fun {n : Nat} (b : s_bool) (x y : bitvec n) => SMT.smt_ite b x y
  , s_mux_m    := fun (b : s_bool) x y => throw "s_mux_m" -- FIXME!!!
  
  , s_not      := SMT.not
  , s_or       := SMT.or
  , s_and      := SMT.and
  , s_xor      := SMT.xor
 
  -- - Comparison
  , s_bveq     := fun {n : Nat} (x y : bitvec n) => SMT.eq x y
  , s_bvult    := @SMT.bvult
  , s_bvslt    := @SMT.bvslt
  
  -- - Arithmetic
  , s_bvneg    := @SMT.bvneg
  , s_bvnot    := @SMT.bvnot
   
  , s_bvadd    := @SMT.bvadd
  , s_bvsub    := @SMT.bvsub
  , s_bvmul    := @SMT.bvmul
  , s_bvudiv   := @SMT.bvudiv 
  , s_bvurem   := @SMT.bvurem
  , s_bvextract := fun (w i j : Nat) (x : bitvec w) => SMT.extract i j x

  , s_sext    := bitvec.sresize
  , s_uext    := bitvec.uresize

  , s_trunc   := fun (n m : Nat) (x : bitvec n) =>
                 if H : m ≤ n
                 then bitvec.trunc m H x
                 else SMT.bvimm _ 0 -- FIXME
  , s_bvappend := @SMT.concat
  , s_bvgetbits  := fun {n : Nat} (off m : Nat) (x : bitvec n) => 
                    if m = 0
                    then SMT.bvimm m 0
                    else (let pf : (off + m - 1) + 1 - off = m := I_am_really_sorry3 _;
                          bitvec.cong pf (SMT.extract (off + m - 1) off x))

  , s_bvsetbits  := fun {n m : Nat} (off : Nat) (x : bitvec n) (bs : bitvec m) =>
                    if H : off + m <= n 
                    then bitvec.set_bits x off bs H
                    else SMT.bvimm _ 0   -- FIXME  
  , s_bvand      := @SMT.bvand
  , s_bvor       := @SMT.bvor
  , s_bvxor      := @SMT.bvxor
  , s_bvshl      := @SMT.bvshl
  , s_bvmsb      := fun (n : Nat) (x : bitvec n) => 
                    SMT.eq (SMT.extract (n - 1) (n - 1) x) (SMT.bvimm _ 1)
  -- unsigned
  , s_bvlshr     := @SMT.bvlshr
  -- signed
  , s_bvsshr     := @SMT.bvashr
  , s_parity     := fun (n : Nat) (x : bitvec n) => 
                    bitvec.to_bool (List.foldl SMT.bvxor (SMT.bvimm 1 0) (bitvec.split_list x 1))

  , s_bit_test   := fun {wr wi : Nat} (x : bitvec wr) (y : bitvec wi) => 
                    let ix := bitvec.uresize _ wr y;
                    let ixbit := SMT.bvshl (SMT.bvimm _ 1) ix;
                    SMT.not (SMT.eq (SMT.bvand x ixbit) (SMT.bvimm _ 0))
   
  -- System operations
  , s_os_transition := pure ()
  , s_get_ip        := (fun (s : machine_state) => s.ip) <$> get
  , s_set_ip        := fun x => modify (fun s => { s with ip := x })
  , s_cond_set_ip   := fun b x => modify (fun s => { s with ip := SMT.smt_ite b x s.ip })
  , s_read_cpuid    := pure ()

  } 

end symbolic
end x86
