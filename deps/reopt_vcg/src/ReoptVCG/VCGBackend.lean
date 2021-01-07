

-- import SMTLIB.Syntax
-- import SMTLIB.IdGen

import SmtLib.Smt


import X86Semantics.Common
import X86Semantics.BackendAPI

import DecodeX86.DecodeX86
import ReoptVCG.Types
import ReoptVCG.Translate -- FIXME: this should be moved elsewhere

import ReoptVCG.Annotations

namespace x86

namespace vcg

axiom I_am_really_sorry4 : ∀(P : Prop),  P 

open mc_semantics
open mc_semantics.type
open Smt (SmtSort SmtSort.bool SmtSort.bitvec SmtSort.array Term SmtM Command IdGen)

open ReoptVCG (MemoryAnn)

abbrev bitvec (n : Nat) := Term (SmtSort.bitvec n)
def s_bool              := Term SmtSort.bool

abbrev memaddr := bitvec 64
def byte    := bitvec 8

def machine_word := bitvec 64
def avx_word := bitvec 256


/- The statement that either [low1,high1) preceeds and does not overlap
    [low2,high2) or vice versa. -/
def isDisjoint (low1 high1 low2 high2 : bitvec 64) : s_bool :=
Smt.or (Smt.bvule high1 low2) (Smt.bvule high2 low1)


namespace RegState

def get_gpreg  (s : RegState) (idx : Fin 16) : machine_word := 
  -- FIXME
  if h : 16 = s.gpregs.size
  then s.gpregs.get (cast (congrArg Fin h) idx)
  else Smt.bvimm _ 0

def update_gpreg (idx : Fin 16) (f : machine_word -> machine_word) (s : RegState) : RegState :=
  -- FIXME
  if h : 16 = s.gpregs.size 
  then { s with gpregs := s.gpregs.set (cast (congrArg Fin h) idx) (f (get_gpreg s idx)) }
  else s 

def get_flag  (s : RegState) (idx : Fin 32) : s_bool := 
  if h : 32 = s.flags.size
  then s.flags.get (cast (congrArg Fin h) idx)
  else Smt.false

def update_flag (idx : Fin 32) (f : s_bool -> s_bool) (s : RegState) : RegState :=
  if h : 32 = s.flags.size
  then { s with flags := s.flags.set (cast (congrArg Fin h) idx) (f (get_flag s idx)) }
  else s 

-- def get_reg64' : forall (n : Nat) (s : RegState) (r : concrete_reg (bv n)), n = 64 ->machine_word
--   | _, s, concrete_reg.gpreg idx tp => λ_ => s.get_gpreg idx
--   | _, _, _ => λ_ => Smt.bvimm _ 0

--   -- | _, pf, s, concrete_reg.avxreg _ avxreg_type.ymm =>
--   --   let pf' : ¬ (Eq 256 64) := Nat.neOfBeqEqFalse rfl; absurd pf pf'
--   -- | _, pf, s, concrete_reg.avxreg _ avxreg_type.xmm =>
--   --   let pf' : ¬ (Eq 128 64) := Nat.neOfBeqEqFalse rfl; absurd pf pf'

def get_reg64' (n : Nat) (pf : n = 64) (s : RegState) (r : concrete_reg (bv n)) : machine_word :=
  match n, r, pf with
  | _, concrete_reg.gpreg idx tp, _ => s.get_gpreg idx
  | _, concrete_reg.avxreg _ avxreg_type.ymm, pf => 
    let pf' : ¬ (Eq 256 64) := Nat.neOfBeqEqFalse rfl; absurd pf pf'
  | _, concrete_reg.avxreg _ avxreg_type.xmm, pf => 
    let pf' : ¬ (Eq 128 64) := Nat.neOfBeqEqFalse rfl; absurd pf pf'

def update_reg64' (n : Nat) (pf : n = 64) (r : concrete_reg (bv n)) 
                  (f : machine_word -> machine_word) (s : RegState) : RegState :=
  match n, r, pf with
  | _, concrete_reg.gpreg idx tp, _ => update_gpreg idx f s
  | _, concrete_reg.avxreg _ avxreg_type.ymm, pf => 
    let pf' : ¬ (Eq 256 64) := Nat.neOfBeqEqFalse rfl; absurd pf pf'
  | _, concrete_reg.avxreg _ avxreg_type.xmm, pf => 
    let pf' : ¬ (Eq 128 64) := Nat.neOfBeqEqFalse rfl; absurd pf pf'

def get_flag'  (s : RegState) (r : concrete_reg bit) : s_bool :=
  match r with
  | concrete_reg.flagreg idx => get_flag s idx

def update_flag'  (r : concrete_reg bit)
                  (f : s_bool -> s_bool) (s : RegState) : RegState :=
  match r with
  | concrete_reg.flagreg idx => update_flag idx f s

def get_reg64 (s : RegState) (r : concrete_reg (bv gpreg_type.reg64.width)) : machine_word :=
  get_reg64' _ rfl s r

def update_reg64  (r : concrete_reg (bv gpreg_type.reg64.width)) 
                  (f : machine_word -> machine_word) (s : RegState) : RegState :=
    update_reg64' _ rfl r f s

def get_avxreg  (s : RegState) (idx : Fin 16) : avx_word := 
  -- FIXME
  if h : 16 = s.avxregs.size
  then Array.get s.avxregs (cast (congrArg _ h) idx) else  Smt.bvimm _ 0

def update_avxreg (idx : Fin 16) (f : avx_word -> avx_word) (s : RegState) : RegState :=
  -- FIXME
  if h : 16 = s.avxregs.size 
  then { s with avxregs := Array.set s.avxregs (cast (congrArg _ h) idx) (f (get_avxreg s idx)) }
  else s 

def print_regs (s : RegState) : String :=
  let lines := List.zipWith (fun n (r : bitvec 64) => (n ++ ": " ++ toString (toSExpr r) ++ ", ")) reg.r64_names s.gpregs.toList;
  String.join lines

-- Constructs a new machine state where all the elements are fresh constants
-- FIXME: could use sz = ns.length
protected 
def declare_const_aux {s : SmtSort} (pfx : String) (ns : List String) (sz : Nat) : SmtM (Array (Term s)) := do
  let mut terms : Array (Term s) := Array.mkEmpty sz
  for n in [:sz] do
    let fn ← Smt.declareFun (pfx ++ List.getD n ns "el") [] s
    terms := terms.push fn
  pure terms

-- We normally havea concrete rip
def declare_const (pfx : String) (ip : Nat) : SmtM RegState := do
  let gprs  <- RegState.declare_const_aux pfx reg.r64_names 16;
  let flags <- RegState.declare_const_aux pfx reg.flag_names 32;
  let avxregs <- RegState.declare_const_aux pfx (List.map (fun i => "xmm" ++ reprStr i) (Nat.upto0_lt 16)) 16;
  pure { gpregs := gprs, flags := flags, avxregs := avxregs, ip := Smt.bvimm _ ip }

end RegState


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

-- FIXME: behave wrt prec
instance : Repr Event := ⟨fun e _n => Event.repr e⟩

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
     let v : bitvec ((b + w - 1) + 1 - b) := Smt.extract (b + w - 1) b x;
     bitvec.cong pf v);
  List.map ex1 idxs


def concat_list_aux {n : Nat} : forall (m : Nat) (acc : bitvec m) (xs : List (bitvec n)), bitvec (m + n * xs.length) 
  | m, acc, [] => acc
  | m, acc, (x :: xs) => 
    let pf : (m + n + n * List.length xs) = (m + n * List.length (x :: xs)) := I_am_really_sorry4 _;
    bitvec.cong pf (concat_list_aux (m + n) (Smt.concat acc x) xs)
  
def concat_list {n : Nat} : forall (xs : List (bitvec n)), bitvec (n * xs.length) 
  | []        => Smt.bvimm 0 0 -- FIXME: shouldn't happen, or raise an error
  | (x :: xs) => let pf : (n + n * List.length xs) = (n * List.length (x :: xs)) := I_am_really_sorry4 _; 
                 bitvec.cong pf (bitvec.concat_list_aux n x xs)

-- Breaks if m == 0
def trunc {n : Nat} (m : Nat) (pf : m <= n) (x : bitvec n) : bitvec m :=
  if m = 0 
  then Smt.bvimm _ 0 -- FIXME: will probably cause issues
  else (let pf' : (m - 1) + 1 - 0 = m := sorryAx _; 
        bitvec.cong pf' (Smt.extract (m - 1) 0 x))

def uresize (n m : Nat) (x : bitvec n) : bitvec m :=
  if H : n ≤ m 
  then (let pf : n + (m - n) = m := sorryAx _; 
       bitvec.cong pf (Smt.zeroExtend (m - n) x))
  else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

def sresize (n m : Nat) (x : bitvec n) : bitvec m :=
  if H : n ≤ m 
  then (let pf : n + (m - n) = m := sorryAx _; 
       bitvec.cong pf (Smt.signExtend (m - n) x))
  else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

-- There may be a more efficient way of doing this (e.g. slicing and concat)
def set_bits {n} (x:bitvec n) (i:Nat) {m} (y:bitvec m) (p:i+m ≤ n) : bitvec n :=
  let premask := Smt.bvshl (uresize _ n (Smt.repeat m (Smt.bvimm 1 1)))
                              (Smt.bvimm _ i);
  let mask    := Smt.bvnot premask;
  let bits := Smt.bvshl (uresize _ n y) (Smt.bvimm _ i);
  Smt.bvor (Smt.bvand x mask) bits

def to_bool (b : bitvec 1) : s_bool := Smt.eq b (Smt.bvimm _ 1)

end bitvec

-- abbrev memory_t := SmtSort.array (SmtSort.bitvec 64) (SmtSort.bitvec 8)
-- def memory := Term memory_t

-- -- We use these to abstract over the actual implementation of read/store
-- structure StdLib :=
--   (read_byte  : memaddr -> memory  -> byte)
--   (store_byte : memaddr -> byte -> memory -> memory)

-- namespace StdLib

-- def make : SmtM StdLib := do
--   rb <- Smt.define_fun "read_byte" [SmtSort.bitvec 64, memory_t] (SmtSort.bitvec 8)
--         (fun addr mem => Smt.select _ _ mem addr);
--   sb <- Smt.define_fun "write_byte" [SmtSort.bitvec 64, SmtSort.bitvec 8, memory_t] memory_t
--         (fun addr b mem => Smt.store _ _ mem addr b);
--   pure { read_byte := rb, store_byte := sb }

-- end StdLib

-- namespace memory

-- def store_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (bs : List byte) : memory := 
--     (List.foldl (fun (v : memory × memaddr) b => (stdlib.store_byte v.snd b v.fst, Smt.bvadd v.snd (Smt.bvimm 64 1))) (m, addr) bs).fst

-- def read_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (n : Nat) : List byte :=
--     List.map (fun i => stdlib.read_byte (Smt.bvadd addr (Smt.bvimm 64 i)) m) (Nat.upto0_lt n)

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

def vcg_state.empty : vcg_state := vcg_state.mk none Smt.IdGen.empty []

-- Stacking like this makes it easier to derive MonadState
def base_system_m := (StateT vcg_state (ExceptT String Id))
def system_m := StateT RegState base_system_m

instance : Monad base_system_m :=
  inferInstanceAs (Monad (StateT vcg_state (ExceptT String Id)))

instance : MonadState vcg_state base_system_m :=
  inferInstanceAs (MonadState vcg_state (StateT vcg_state (ExceptT String Id)))

instance : MonadExcept String base_system_m :=
  inferInstanceAs (MonadExcept String (StateT vcg_state (ExceptT String Id)))

instance system_m.monad : Monad system_m :=
  inferInstanceAs (Monad (StateT RegState base_system_m))

instance system_m.monadState : MonadState RegState system_m :=
  inferInstanceAs (MonadState RegState (StateT RegState base_system_m))

instance system_m.monadExcept : MonadExcept String system_m :=
  inferInstanceAs (MonadExcept String (StateT RegState (StateT vcg_state (ExceptT String Id))))

instance : MonadLift base_system_m system_m :=
  inferInstanceAs (MonadLift base_system_m (StateT RegState base_system_m))

namespace system_m

protected
def run {a : Type} (m : system_m a) (os : vcg_state) (s : RegState) 
  : (Except String ((a × RegState) × vcg_state)) := do
  ((m.run s).run os).run

def runSmtM {a : Type} (m : SmtM a) : system_m a := do
  let run' :=
    fun (s : vcg_state) => 
        (let r := Smt.runSmtM s.idGen m;
         (r.fst, {s with revEvents := (List.map Event.Command r.snd.snd.reverse) ++ s.revEvents, idGen := r.snd.fst}));
  monadLift (modifyGet run' : base_system_m a)

def name_term {s : SmtSort} (name : Option String) (tm : Term s) : system_m (Term s) :=
  runSmtM (Smt.nameTerm (name.getD "tmp") tm)

def emit_event (e : Event) : system_m Unit :=
  monadLift (modify (fun (s : vcg_state) => { s with revEvents := e :: s.revEvents }) : base_system_m Unit)

def getEventInfo : system_m MemoryAnn := do
  let s ← monadLift (get : base_system_m vcg_state)
  match s.eventInfo with
  | none => throw "Missing event info"
  | some v => pure v

-- c.f. stmt2SMT
def store_word (n : Nat) (addr : memaddr) (v : bitvec n) : system_m Unit := do
  -- addr can be a complicated expression, name to avoid term explosion
  let addr' ← name_term (some "addr") addr
  let memEventInfo ← getEventInfo
  match memEventInfo with
  | ReoptVCG.MemoryAnn.binaryOnlyAccess       => emit_event (Event.MCOnlyStackWriteEvent addr' n v)
  | ReoptVCG.MemoryAnn.jointStackAccess aname => emit_event (Event.JointStackWriteEvent addr' n v aname)
  | ReoptVCG.MemoryAnn.heapAccess             => emit_event (Event.NonStackWriteEvent addr' n v)

-- c.f. assignRhs2SMT
def read_word (n : Nat) (addr : memaddr) : system_m (bitvec n) := do
  let addr' ← name_term (some "addr") addr
  let resv  ← runSmtM (Smt.declareFun "readv" [] (SmtSort.bitvec n))
  let memEventInfo ← getEventInfo
  match memEventInfo with
  | ReoptVCG.MemoryAnn.binaryOnlyAccess       => emit_event (Event.MCOnlyStackReadEvent addr' n resv)
  | ReoptVCG.MemoryAnn.jointStackAccess aname => emit_event (Event.JointStackReadEvent addr' n resv aname)
  | ReoptVCG.MemoryAnn.heapAccess             => emit_event (Event.NonStackReadEvent addr' n resv)
  pure resv

end system_m

-- FIXME: maybe factor out common stuff from concreteBackend
-- FIXME!!: this is a pretty close copy of symbolic.backend
def backend : Backend :=
  { s_bv     := bitvec
  , s_bool   := s_bool

  , s_bv_imm   := Smt.bvimm
  , s_bool_imm := fun b => if b then Smt.true else Smt.false

  , monad := system_m
  , Monad_backend := inferInstance
  , MonadExcept_backend := inferInstance
  
  , store_word := fun n addr bv => system_m.store_word (8 * n) addr bv
  , read_word  := fun addr n => system_m.read_word (8 * n) addr 
               
  , get_gpreg  := fun i => (fun s => RegState.get_gpreg s i) <$> get
  , s_cond_set_gpreg := fun c i v => do 
    let s ← system_m.name_term (reg.r64_names.get? i.val) v
    modify (RegState.update_gpreg i (fun old => Smt.smtIte c s old))
  , get_flag  :=  fun i => (fun s => RegState.get_flag s i) <$> get
  , s_cond_set_flag := fun c i v =>
    modify (RegState.update_flag i (fun old => Smt.smtIte c v old))

  , get_avxreg  := fun i => (fun s => RegState.get_avxreg s i) <$> get
  , s_cond_set_avxreg := fun c i v => do
    let s <- system_m.name_term (some ("xmm" ++ reprStr i)) v;
    modify (RegState.update_avxreg i (fun old => Smt.smtIte c s old))
  
  , s_mux_bool := fun (b : s_bool) (x y : s_bool) => Smt.smtIte b x y
  , s_mux_bv   := fun {n : Nat} (b : s_bool) (x y : bitvec n) => Smt.smtIte b x y
  
  , s_not      := Smt.not
  , s_or       := Smt.or
  , s_and      := Smt.and
  , s_xor      := Smt.xor
 
  -- - Comparison
  , s_bveq     := fun {n : Nat} (x y : bitvec n) => Smt.eq x y
  , s_bvult    := @Smt.bvult
  , s_bvslt    := @Smt.bvslt
  
  -- - Arithmetic
  , s_bvneg    := @Smt.bvneg
  , s_bvnot    := @Smt.bvnot
   
  , s_bvadd    := @Smt.bvadd
  , s_bvsub    := @Smt.bvsub
  , s_bvmul    := @Smt.bvmul
  , s_bvudiv   := @Smt.bvudiv 
  , s_bvurem   := @Smt.bvurem
  , s_bvextract := fun {w : Nat} (i j : Nat) (x : bitvec w) => Smt.extract i j x

  , s_sext    := bitvec.sresize
  , s_uext    := bitvec.uresize

  , s_trunc   := fun (n m : Nat) (x : bitvec n) =>
                 if H : m ≤ n
                 then bitvec.trunc m H x
                 else Smt.bvimm _ 0 -- FIXME
  , s_bvappend := @Smt.concat
  , s_bvgetbits  := fun {n : Nat} (off m : Nat) (x : bitvec n) => 
                    if m = 0
                    then Smt.bvimm m 0
                    else (let pf : (off + m - 1) + 1 - off = m := I_am_really_sorry4 _;
                          bitvec.cong pf (Smt.extract (off + m - 1) off x))

  , s_bvsetbits  := fun {n m : Nat} (off : Nat) (x : bitvec n) (bs : bitvec m) =>
                    if H : off + m <= n 
                    then bitvec.set_bits x off bs H
                    else Smt.bvimm _ 0   -- FIXME  
  , s_bvand      := @Smt.bvand
  , s_bvor       := @Smt.bvor
  , s_bvxor      := @Smt.bvxor
  , s_bvshl      := @Smt.bvshl
  , s_bvmsb      := fun (n : Nat) (x : bitvec n) => 
                    Smt.eq (Smt.extract (n - 1) (n - 1) x) (Smt.bvimm _ 1)
  -- unsigned
  , s_bvlshr     := @Smt.bvlshr
  -- signed
  , s_bvsshr     := @Smt.bvashr
  , s_parity     := fun {n : Nat} (x : bitvec n) => 
                    bitvec.to_bool (List.foldl Smt.bvxor (Smt.bvimm 1 0) (bitvec.split_list x 1))

  , s_bit_test   := fun {wr wi : Nat} (x : bitvec wr) (y : bitvec wi) => 
                    let ix := bitvec.uresize _ wr y;
                    let ixbit := Smt.bvshl (Smt.bvimm _ 1) ix;
                    Smt.not (Smt.eq (Smt.bvand x ixbit) (Smt.bvimm _ 0))
   
  -- System operations
  , s_os_transition := pure ()
  , s_get_ip        := (fun (s : RegState) => s.ip) <$> get
  , s_set_ip        := fun x => modify (fun s => { s with ip := x })
  -- FIXME: could just use mux_bv and get_ip
  , s_cond_set_ip   := fun b x => modify (fun s => { s with ip := Smt.smtIte b x s.ip })
  , s_read_cpuid    := pure ()
  } 

end Internal

open Internal

structure Semantics :=
  (instruction : Type)
  (instruction_size : instruction -> Nat)
  (decode      : Nat -> Sum String instruction)
  (eval        : forall (backend : Backend), instruction -> backend.monad Unit)

-- We can't stick the above in Context as it is in Type 1

def instructionEvents 
  ( sem    : Semantics )
  ( evtMap : Std.RBMap Nat MemoryAnn (fun x y => decide (x < y)) )
  -- ^ Map from addresses to annotations of events on that address.
  ( s : RegState )
  -- ^ Initial values for registers
  ( idGen : IdGen)
  -- ^ Used to generate unique/fresh identifiers for SMT terms.
  ( ip : Nat )
  -- ^ Location to explore
  : Except String (List Event × IdGen × Nat) :=
  let inst := sem.decode ip;
  match inst with 
  | (Sum.inl _) => throw "Unknown byte"
  | (Sum.inr i) => do
       -- set ip of next instruction, used for getting ip-relative addrs.
       let nextIP := ip + sem.instruction_size i;
       let s'  := { s with ip := Smt.bvimm _ nextIP };
       let evt := evtMap.find? ip;
       let r := (sem.eval backend i).run
                { idGen := idGen, eventInfo := evt, revEvents := [] }
                s';
       match r with
       | Except.ok ((_, s''), os'') =>
             let fAndE := Event.FetchAndExecuteEvent s'';
             Except.ok (List.reverse (fAndE :: os''.revEvents), os''.idGen, sem.instruction_size i)
       | Except.error err => Except.error err -- (err ++ " " ++ repr i)

end vcg
end x86
