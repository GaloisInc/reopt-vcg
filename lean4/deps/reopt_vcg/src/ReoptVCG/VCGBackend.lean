
import SMTLIB.Syntax

import X86Semantics.Common
import X86Semantics.BackendAPI

import DecodeX86.DecodeX86
import ReoptVCG.Translate -- FIXME: this should be moved elsewhere

import ReoptVCG.Annotations

namespace x86

namespace vcg

axiom I_am_really_sorry4 : ∀(P : Prop),  P 

open mc_semantics
open mc_semantics.type
open SMT (sort term smtM command IdGen)

open ReoptVCG (MemoryAnn)

abbrev bitvec (n : Nat) := term (SMT.sort.bitvec n)
def s_bool              := term SMT.sort.smt_bool

abbrev memaddr := bitvec 64
def byte    := bitvec 8

def machine_word := bitvec 64

structure RegState : Type :=
  (gpregs : Array machine_word) -- 16
  (flags  : Array s_bool) -- 32
  (ip     : machine_word)

namespace RegState

def get_gpreg  (s : RegState) (idx : Fin 16) : machine_word := 
  -- FIXME
  if h : 16 = s.gpregs.size
  then Array.get s.gpregs (Eq.recOn h idx) else SMT.bvimm _ 0

def update_gpreg (idx : Fin 16) (f : machine_word -> machine_word) (s : RegState) : RegState :=
  -- FIXME
  if h : 16 = s.gpregs.size 
  then { s with gpregs := Array.set s.gpregs (Eq.recOn h idx) (f (get_gpreg s idx)) }
  else s 

def get_flag  (s : RegState) (idx : Fin 32) : s_bool := 
  if h : 32 = s.flags.size
  then Array.get s.flags (Eq.recOn h idx) else SMT.false

def update_flag (idx : Fin 32) (f : s_bool -> s_bool) (s : RegState) : RegState :=
  if h : 32 = s.flags.size
  then { s with flags := Array.set s.flags (Eq.recOn h idx) (f (get_flag s idx)) }
  else s 

def get_reg64  (s : RegState) (r : concrete_reg (bv gpreg_type.reg64.width)) : machine_word :=
  match gpreg_type.reg64.width, r with
  | _, concrete_reg.gpreg idx tp => s.get_gpreg idx

def update_reg64  (r : concrete_reg (bv gpreg_type.reg64.width)) 
                  (f : machine_word -> machine_word) (s : RegState) : RegState :=
  match gpreg_type.reg64.width, r with
  | _, concrete_reg.gpreg idx tp => update_gpreg idx f s

def print_regs (s : RegState) : String :=
  let lines := List.zipWith (fun n (r : bitvec 64) => (n ++ ": " ++ toString (toSExpr r) ++ ", ")) reg.r64_names s.gpregs.toList;
  String.join lines

-- Constructs a new machine state where all the elements are fresh constants
-- FIXME: could use sz = ns.length
protected 
def declare_const_aux {s : sort} (pfx : String) (ns : List String) (sz : Nat) : smtM (Array (term s)) := do
  let base := mkArray sz 0;
  let f    := fun n (_ : Nat) => SMT.declare_fun (pfx ++ List.getD n ns "el") [] s;
  Array.mapIdxM f base

-- We normally havea concrete rip
def declare_const (pfx : String) (ip : Nat) : smtM RegState := do
  gprs  <- RegState.declare_const_aux pfx reg.r64_names 16;
  flags <- RegState.declare_const_aux pfx reg.flag_names 32;
  pure { gpregs := gprs, flags := flags, ip := SMT.bvimm _ ip }

end RegState

-- This mirrors the Haskell prototype as far as possible, hence the slightly verbose names.
inductive Event
  | Command : SMT.command -> Event
  | Warning : String -> Event
    -- ^ We added a warning about an issue in the VCG
  | MCOnlyStackReadEvent : memaddr -> forall (n : Nat), bitvec n -> Event
    -- ^ `MCOnlyReadEvent a w v` indicates that we read `w` bytes
    -- from `a`, and assign the value returned to `v`.  This only
    -- appears in the binary code.
  | JointStackReadEvent : memaddr -> forall (n : Nat), bitvec n -> ReoptVCG.LocalIdent -> Event
    -- ^ `JointReadEvent a w v llvmAlloca` indicates that we read `w` bytes from `a`,
    -- and assign the value returned to `v`.  This appears in the both the binary
    -- and LLVM.  The alloca name refers to the LLVM allocation this is part of,
    -- and otherwise this is a binary only read.
  | NonStackReadEvent : memaddr -> forall (n : Nat), bitvec n -> Event
    -- ^ `NonStackReadEvent a w v` indicates that we read `w` bytes
    -- from `a`, and assign the value returned to `v`.  The address `a` should not
    -- be in the stack.
  | MCOnlyStackWriteEvent : memaddr -> forall (n : Nat), bitvec n -> Event
    -- ^ `MCOnlyStackWriteEvent a tp v` indicates that we write the `w` byte value `v`  to `a`.
    --
    -- This has side effects, so we record the event.
  | JointStackWriteEvent : memaddr -> forall (n : Nat), bitvec n -> ReoptVCG.LocalIdent -> Event 
    -- ^ `JointStackWriteEvent a w v` indicates that we write the `w` byte value `v`  to `a`.
    -- The write affects the alloca pointed to by Allocaname.
    --
    -- This has side effects, so we record the event.
  | NonStackWriteEvent : memaddr -> forall (n : Nat), bitvec n -> Event
    -- ^ `NonStackWriteEvent a w v` indicates that we write the `w` byte value `v`  to `a`.  The
    -- address `a` should not be in the stack.
    --
    -- This has side effects, so we record the event.
  | FetchAndExecuteEvent : RegState -> Event
    -- ^ A fetch and execute

namespace Event

protected
def repr : Event -> String
| Command c => "Command " ++ toString (toSExpr c)
| Warning s => "Warning " ++ s
| MCOnlyStackReadEvent addr n b => "MCOnlyStackReadEvent " ++ toString (toSExpr addr)
| JointStackReadEvent addr n b i => "JointStackReadEvent " ++ toString (toSExpr addr)
| NonStackReadEvent _ _ _ => "NonStackReadEvent"
| MCOnlyStackWriteEvent _ _ _ => "MCOnlyStackWriteEvent"
| JointStackWriteEvent _ _ _ _ => "JointStackWriteEvent"
| NonStackWriteEvent _ _ _ => "NonStackWriteEvent"
| FetchAndExecuteEvent _   => "FetchAndExecuteEvent"

instance : HasRepr Event := ⟨Event.repr⟩

end Event

namespace bitvec

def cong {n m : Nat} (pf : n = m) (x : bitvec n) : bitvec m :=
  @Eq.recOn _ _ (fun x _ => bitvec x) _ pf x

-- probably doesn't do what you want if not (w dvd n).  MSB as the first byte to follow Galois.Data.Bitvec
def split_list {n:Nat} (x : bitvec n) (w : Nat) : List (bitvec w) :=
  let idxs := (Nat.upto0_lt (n / w)).reverse;
  let ex1 : Nat -> bitvec w := fun ix =>
    (let b := ix * w; 
     let pf : (b + w - 1) + 1 - b = w := sorryAx _;
     let v : bitvec ((b + w - 1) + 1 - b) := SMT.extract (b + w - 1) b x;
     bitvec.cong pf v);
  List.map ex1 idxs

protected
def concat_list_aux {n : Nat} : forall (m : Nat) (acc : bitvec m) (xs : List (bitvec n)), bitvec (m + n * xs.length) 
  | m, acc, [] => acc
  | m, acc, (x :: xs) => 
    let pf : (m + n + n * List.length xs) = (m + n * List.length (x :: xs)) := I_am_really_sorry4 _;
    bitvec.cong pf (concat_list_aux (m + n) (SMT.concat acc x) xs)
  
def concat_list {n : Nat} : forall (xs : List (bitvec n)), bitvec (n * xs.length) 
  | []        => SMT.bvimm 0 0 -- FIXME: shouldn't happen, or raise an error
  | (x :: xs) => let pf : (n + n * List.length xs) = (n * List.length (x :: xs)) := I_am_really_sorry4 _; 
                 bitvec.cong pf (bitvec.concat_list_aux n x xs)

-- Breaks if m == 0
def trunc {n : Nat} (m : Nat) (pf : m <= n) (x : bitvec n) : bitvec m :=
  if m = 0 
  then SMT.bvimm _ 0 -- FIXME: will probably cause issues
  else (let pf' : (m - 1) + 1 - 0 = m := sorryAx _; 
        bitvec.cong pf' (SMT.extract (m - 1) 0 x))

def uresize (n m : Nat) (x : bitvec n) : bitvec m :=
  if H : n ≤ m 
  then (let pf : n + (m - n) = m := sorryAx _; 
       bitvec.cong pf (SMT.zero_extend (m - n) x))
  else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

def sresize (n m : Nat) (x : bitvec n) : bitvec m :=
  if H : n ≤ m 
  then (let pf : n + (m - n) = m := sorryAx _; 
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

-- abbrev memory_t := SMT.sort.array (SMT.sort.bitvec 64) (SMT.sort.bitvec 8)
-- def memory := term memory_t

-- -- We use these to abstract over the actual implementation of read/store
-- structure StdLib :=
--   (read_byte  : memaddr -> memory  -> byte)
--   (store_byte : memaddr -> byte -> memory -> memory)

-- namespace StdLib

-- def make : smtM StdLib := do
--   rb <- SMT.define_fun "read_byte" [SMT.sort.bitvec 64, memory_t] (SMT.sort.bitvec 8)
--         (fun addr mem => SMT.select _ _ mem addr);
--   sb <- SMT.define_fun "write_byte" [SMT.sort.bitvec 64, SMT.sort.bitvec 8, memory_t] memory_t
--         (fun addr b mem => SMT.store _ _ mem addr b);
--   pure { read_byte := rb, store_byte := sb }

-- end StdLib

-- namespace memory

-- def store_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (bs : List byte) : memory := 
--     (List.foldl (fun (v : memory × memaddr) b => (stdlib.store_byte v.snd b v.fst, SMT.bvadd v.snd (SMT.bvimm 64 1))) (m, addr) bs).fst

-- def read_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (n : Nat) : List byte :=
--     List.map (fun i => stdlib.read_byte (SMT.bvadd addr (SMT.bvimm 64 i)) m) (Nat.upto0_lt n)

-- -- theorem read_bytes_length: forall {m} {stdlib} {addr} {n}, List.length (read_bytes m stdkub addr n) = n 
-- --   := I_am_really_sorry4 _; 

-- def store_word {n : Nat} (m : memory) (stdlib : StdLib) (addr : memaddr) (b : bitvec (8 * n)) : memory := 
--   m.store_bytes stdlib addr (b.split_list 8).reverse 

-- def read_word (m : memory) (stdlib : StdLib) (addr : memaddr) (n : Nat) : bitvec (8 * n) :=
--   let bs := m.read_bytes stdlib addr n;
--   let w  : bitvec (8 * bs.length) := bitvec.concat_list bs;
--   let pf : 8 * bs.length = 8 * n := I_am_really_sorry4 _;
--   bitvec.cong pf w

-- end memory

namespace Internal

structure vcg_state :=
  (eventInfo  : Option MemoryAnn)
  (idGen  : IdGen)
  (revEvents : List Event)

-- def vcg_state.empty : vcg_state := vcg_state.mk 0 []

-- Stacking like this makes it easier to derive MonadState
def base_system_m := (StateT vcg_state (ExceptT String Id))
def system_m := StateT RegState base_system_m

instance : Monad base_system_m :=
  inferInstanceAs (Monad (StateT vcg_state (ExceptT String Id)))

instance : MonadState vcg_state base_system_m :=
  inferInstanceAs (MonadState vcg_state (StateT vcg_state (ExceptT String Id)))

instance : MonadExcept String base_system_m :=
  inferInstanceAs (MonadExcept String (StateT vcg_state (ExceptT String Id)))

instance system_m.Monad : Monad system_m :=
  inferInstanceAs (Monad (StateT RegState base_system_m))

instance system_m.MonadState : MonadState RegState system_m :=
  inferInstanceAs (MonadState RegState (StateT RegState base_system_m))

instance system_m.MonadExcept : MonadExcept String system_m :=
  inferInstanceAs (MonadExcept String (StateT RegState base_system_m))

instance : HasMonadLiftT base_system_m system_m :=
  inferInstanceAs (HasMonadLiftT base_system_m (StateT RegState base_system_m))

namespace system_m

def run {a : Type} (m : system_m a) (os : vcg_state) (s : RegState) 
  : (Except String ((a × RegState) × vcg_state)) := do
  ((m.run s).run os).run

def runsmtM {a : Type} (m : smtM a) : system_m a := do
  let run' := fun (s : vcg_state) => 
                  (let r := SMT.runsmtM s.idGen m;
                  (r.fst, {s with revEvents := (List.map Event.Command r.snd.snd.reverse) ++ s.revEvents
                          , idGen := r.snd.fst}));
  monadLift (modifyGet run' : base_system_m a)

def name_term {s : sort} (name : Option String) (tm : term s) : system_m (term s) :=
  runsmtM (SMT.name_term (name.getD "tmp") tm)

def emit_event (e : Event) : system_m Unit :=
  monadLift (modify (fun (s : vcg_state) => { s with revEvents := e :: s.revEvents }) : base_system_m Unit)

def getEventInfo : system_m MemoryAnn := do
  s <- monadLift (get : base_system_m vcg_state);
  match s.eventInfo with
  | none => throw "Missing event info"
  | some v => pure v

-- c.f. stmt2SMT
def store_word (n : Nat) (addr : memaddr) (v : bitvec n) : system_m Unit := do
  -- addr can be a complicated expression, name to avoid term explosion
  addr' <- name_term (some "addr") addr;
  memEventInfo <- getEventInfo;
  match memEventInfo with
  | ReoptVCG.MemoryAnn.binaryOnlyAccess       => emit_event (Event.MCOnlyStackWriteEvent addr' n v)
  | ReoptVCG.MemoryAnn.jointStackAccess aname => emit_event (Event.JointStackWriteEvent addr' n v aname)
  | ReoptVCG.MemoryAnn.heapAccess             => emit_event (Event.NonStackWriteEvent addr' n v)

-- c.f. assignRhs2SMT
def read_word (n : Nat) (addr : memaddr) : system_m (bitvec n) := do
  addr' <- name_term (some "addr") addr;
  resv  <- runsmtM (SMT.declare_fun "readv" [] (SMT.sort.bitvec n));
  memEventInfo <- getEventInfo;
  match memEventInfo with
  | ReoptVCG.MemoryAnn.binaryOnlyAccess       => emit_event (Event.MCOnlyStackReadEvent addr' n resv)
  | ReoptVCG.MemoryAnn.jointStackAccess aname => emit_event (Event.JointStackReadEvent addr' n resv aname)
  | ReoptVCG.MemoryAnn.heapAccess             => emit_event (Event.NonStackReadEvent addr' n resv);
  pure resv

end system_m

-- FIXME: maybe factor out common stuff from concreteBackend
-- FIXME!!: this is a pretty close copy of symbolic.backend
def backend : Backend :=
  { s_bv     := bitvec
  , s_bool   := s_bool

  , s_bv_imm   := SMT.bvimm
  , s_bool_imm := fun b => if b then SMT.true else SMT.false

  , monad := system_m
  -- , Monad_backend := 
  -- , MonadExcept_backend := 
  
  , store_word := fun n addr bv => system_m.store_word (8 * n) addr bv
  , read_word  := fun addr n => system_m.read_word (8 * n) addr 
               
  , get_gpreg  := fun i => (fun s => RegState.get_gpreg s i) <$> get
  , set_gpreg := fun i v => do s <- system_m.name_term (reg.r64_names.get? i.val) v;
                               modify (RegState.update_gpreg i (fun _ => s))
  , get_flag  :=  fun i => (fun s => RegState.get_flag s i) <$> get
  , set_flag := fun i v => modify (RegState.update_flag i (fun _ => v))
  
  , s_mux_bool := fun (b : s_bool) (x y : s_bool) => SMT.smt_ite b x y
  , s_mux_bv   := fun {n : Nat} (b : s_bool) (x y : bitvec n) => SMT.smt_ite b x y
  , s_mux_m    := fun (b : s_bool) x y => throw "backend.s_mux_m"
  
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
                    else (let pf : (off + m - 1) + 1 - off = m := I_am_really_sorry4 _;
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
  , s_get_ip        := (fun (s : RegState) => s.ip) <$> get
  , s_set_ip        := fun x => modify (fun s => { s with ip := x })
  -- FIXME: could just use mux_bv and get_ip
  , s_cond_set_ip   := fun b x => modify (fun s => { s with ip := SMT.smt_ite b x s.ip })
  , s_read_cpuid    := pure ()
  } 

end Internal

open Internal

def instructionEvents ( evtMap : Std.RBMap Nat MemoryAnn (fun x y => decide (x < y)) )
                      -- ^ Map from addresses to annotations of events on that address.
                      ( s : RegState )
                      -- ^ Initial values for registers
                      ( idGen : IdGen)
                      -- ^ Used to generate unique/fresh identifiers for SMT terms.
                      ( ip : Nat )
                      ( d : decodex86.decoder )  
                      -- ^ Location to explore
                      : Except String (List Event × IdGen × Nat) :=
  let inst := decodex86.decode d ip;
  match inst with 
  | (Sum.inl b) => throw "Unknown byte"
  | (Sum.inr i) => do
       -- set ip of next instruction, used for getting ip-relative addrs.
       let nextIP := ip + i.nbytes;
       let s'  := { s with ip := SMT.bvimm _ nextIP };
       let evt := evtMap.find? ip;
       let r := (eval_instruction backend i).run            
                { idGen := idGen, eventInfo := evt, revEvents := [] }
                s';
       match r with
       | Except.ok ((_, s''), os'') =>
             let fAndE := Event.FetchAndExecuteEvent s'';
             Except.ok (List.reverse (fAndE :: os''.revEvents), os''.idGen, i.nbytes)
       | Except.error err => Except.error (err ++ " " ++ repr i)

end vcg
end x86
