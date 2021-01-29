
import SmtLib.Smt

import X86Semantics.Common
import X86Semantics.BackendAPI


namespace x86

namespace symbolic

axiom I_am_really_sorry3 : ∀(P : Prop),  P 

open mc_semantics
open mc_semantics.type
open Smt (SmtSort SmtSort.bitvec SmtSort.bool SmtSort.array Term SmtM Command IdGen IdGen.empty)

abbrev bitvec (n : Nat) := Term (SmtSort.bitvec n)
def s_bool              := Term SmtSort.bool
abbrev s_float (fc : float_class) := bitvec fc.width

instance {n : Nat} : Inhabited (bitvec n) := ⟨Smt.bvimm _ 0⟩
instance : Inhabited s_bool := ⟨Smt.false⟩

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
     let v : bitvec ((b + w - 1) + 1 - b) := Smt.extract (b + w - 1) b x;
     bitvec.cong pf v);
  List.map ex1 idxs

protected
def concat_list_aux {n : Nat} : forall (m : Nat) (acc : bitvec m) (xs : List (bitvec n)), bitvec (m + n * xs.length) 
  | m, acc, [] => acc
  | m, acc, (x :: xs) => 
    let pf : (m + n + n * List.length xs) = (m + n * List.length (x :: xs)) := I_am_really_sorry3 _;
    bitvec.cong pf (bitvec.concat_list_aux (m + n) (Smt.concat acc x) xs)
  
def concat_list {n : Nat} : forall (xs : List (bitvec n)), bitvec (n * xs.length) 
  | []        => Smt.bvimm 0 0 -- FIXME: shouldn't happen, or raise an error
  | (x :: xs) => let pf : (n + n * List.length xs) = (n * List.length (x :: xs)) := I_am_really_sorry3 _; 
                 bitvec.cong pf (bitvec.concat_list_aux n x xs)

-- Breaks if m == 0
def trunc {n : Nat} (m : Nat) (pf : m <= n) (x : bitvec n) : bitvec m :=
  if m = 0 
  then Smt.bvimm _ 0 -- FIXME: will probably cause issues
  else (let pf' : (m - 1) + 1 - 0 = m := I_am_really_sorry3 _; 
        bitvec.cong pf' (Smt.extract (m - 1) 0 x))

def uresize (n m : Nat) (x : bitvec n) : bitvec m :=
  if H : n ≤ m 
  then (let pf : n + (m - n) = m := I_am_really_sorry3 _; 
       bitvec.cong pf (Smt.zeroExtend (m - n) x))
  else bitvec.trunc m (Nat.leOfLt (Nat.gtOfNotLe H)) x

def sresize (n m : Nat) (x : bitvec n) : bitvec m :=
  if H : n ≤ m 
  then (let pf : n + (m - n) = m := I_am_really_sorry3 _; 
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

abbrev memory_t := SmtSort.array (SmtSort.bitvec 64) (SmtSort.bitvec 8)
def memory := Term memory_t

-- We use these to abstract over the actual implementation of read/store
structure StdLib :=
  (read_byte  : memaddr -> memory  -> byte)
  (store_byte : memaddr -> byte -> memory -> memory)

namespace StdLib

def make : SmtM StdLib := do
  let rb ← Smt.defineFun "read_byte" [SmtSort.bitvec 64, memory_t] (SmtSort.bitvec 8)
        (fun addr mem => Smt.select _ _ mem addr);
  let sb ←  Smt.defineFun "write_byte" [SmtSort.bitvec 64, SmtSort.bitvec 8, memory_t] memory_t
        (fun addr b mem => Smt.store _ _ mem addr b);
  pure { read_byte := rb, store_byte := sb }

end StdLib

namespace memory

def store_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (bs : List byte) : memory := 
    (List.foldl (fun (v : memory × memaddr) b => (stdlib.store_byte v.snd b v.fst, Smt.bvadd v.snd (Smt.bvimm 64 1))) (m, addr) bs).fst

def read_bytes (m : memory) (stdlib : StdLib) (addr : memaddr) (n : Nat) : List byte :=
    List.map (fun i => stdlib.read_byte (Smt.bvadd addr (Smt.bvimm 64 i)) m) (Nat.upto0_lt n)

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
def avx_word := bitvec 256

structure machine_state : Type :=
  (mem    : memory)
  (gpregs : Array machine_word) -- 16
  (flags  : Array s_bool) -- 32
  (avxregs : Array avx_word)
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
  then
    Array.get s.gpregs (cast (congrArg Fin h) idx)
  else
    Smt.bvimm _ 0

def update_gpreg (idx : Fin 16) (f : machine_word -> machine_word) (s : machine_state) : machine_state :=
  -- FIXME
  if h : 16 = s.gpregs.size 
  then { s with gpregs := Array.set s.gpregs (cast (congrArg Fin h) idx) (f (get_gpreg s idx)) }
  else s 

def get_flag  (s : machine_state) (idx : Fin 32) : s_bool := 
  if h : 32 = s.flags.size
  then Array.get s.flags (cast (congrArg Fin h) idx)
  else Smt.false

def update_flag (idx : Fin 32) (f : s_bool -> s_bool) (s : machine_state) : machine_state :=
  if h : 32 = s.flags.size
  then { s with flags := Array.set s.flags (cast (congrArg Fin h) idx) (f (get_flag s idx)) }
  else s 

def get_avxreg  (s : machine_state) (idx : Fin 16) : avx_word := 
  -- FIXME
  if h : 16 = s.avxregs.size
  then s.avxregs.get (cast (congrArg _ h) idx) else  Smt.bvimm _ 0

def update_avxreg (idx : Fin 16) (f : avx_word -> avx_word) (s : machine_state) : machine_state :=
  -- FIXME
  if h : 16 = s.avxregs.size 
  then { s with avxregs := s.avxregs.set (cast (congrArg _ h) idx) (f (get_avxreg s idx)) }
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
def declare_const_aux {s : SmtSort} (ns : List String) (sz : Nat) : SmtM (Array (Term s)) := do
  let mut a : (Array (Term s)) := Array.mkEmpty sz
  for n in [:sz] do
    let fn ← Smt.declareFun (List.getD n ns "el") [] s
    a := a.push fn
  pure a


def declare_const : SmtM machine_state := do
  let mem   ← Smt.declareFun "memory" [] memory_t
  let gprs  ← machine_state.declare_const_aux reg.r64_names 16
  let flags ← machine_state.declare_const_aux reg.flag_names 32
  let avxregs ← machine_state.declare_const_aux (List.map (fun i => "xmm" ++ reprStr i) (Nat.upto0_lt 16)) 16
  let ip    ← Smt.declareFun "ip" [] (SmtSort.bitvec 64)
  pure { mem := mem, gpregs := gprs, flags := flags, avxregs := avxregs, ip := ip }

end machine_state

inductive Event
  | Command : Smt.Command -> Event
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

-- FIXME: behave wrt prec
instance : Repr Event := ⟨fun e _n => Event.repr e⟩

end Event

  --   -- ^ We added a warning about an issue in the VCG
  -- | MCOnlyStackReadEvent : memaddr -> Nat -> Event -- Smt.Term !(MemRepr tp) !Var
  --   -- ^ `MCOnlyReadEvent a w v` indicates that we read `w` bytes
  --   -- from `a`, and assign the value returned to `v`.  This only
  --   -- appears in the binary code.
  -- | forall tp . JointStackReadEvent !Smt.Term !(MemRepr tp) !Var !Ann.LocalIdent
  --   -- ^ `JointReadEvent a w v llvmAlloca` indicates that we read `w` bytes from `a`,
  --   -- and assign the value returned to `v`.  This appears in the both the binary
  --   -- and LLVM.  The alloca name refers to the LLVM allocation this is part of,
  --   -- and otherwise this is a binary only read.
  -- | forall tp . NonStackReadEvent !Smt.Term !(MemRepr tp) !Var
  --   -- ^ `NonStackReadEvent a w v` indicates that we read `w` bytes
  --   -- from `a`, and assign the value returned to `v`.  The address `a` should not
  --   -- be in the stack.
  -- | forall tp . MCOnlyStackWriteEvent !Smt.Term !(MemRepr tp) !Smt.Term
  --   -- ^ `MCOnlyStackWriteEvent a tp v` indicates that we write the `w` byte value `v`  to `a`.
  --   --
  --   -- This has side effects, so we record the event.
  -- | forall tp . JointStackWriteEvent !Smt.Term !(MemRepr tp) !Smt.Term !Ann.LocalIdent
  --   -- ^ `JointStackWriteEvent a w v` indicates that we write the `w` byte value `v`  to `a`.
  --   -- The write affects the alloca pointed to by Allocaname.
  --   --
  --   -- This has side effects, so we record the event.
  -- | forall tp . NonStackWriteEvent !Smt.Term !(MemRepr tp) !Smt.Term
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
  (idGen  : IdGen)
  (trace : List Event)

def os_state.empty : os_state := os_state.mk (Smt.bvimm _ 0) IdGen.empty []

-- Stacking like this makes it easier to derive MonadState
def base_system_m := (StateT os_state (ExceptT String Id))
def system_m := StateT machine_state base_system_m

instance : Monad base_system_m :=
  inferInstanceAs (Monad (StateT os_state (ExceptT String Id)))

instance : MonadState os_state base_system_m :=
  inferInstanceAs (MonadState os_state (StateT os_state (ExceptT String Id)))

instance : MonadExcept String base_system_m :=
  inferInstanceAs (MonadExcept String (StateT os_state (ExceptT String Id)))

instance system_mMonad : Monad system_m :=
  inferInstanceAs (Monad (StateT machine_state base_system_m))

instance system_mMonadState : MonadState machine_state system_m :=
  inferInstanceAs (MonadState machine_state (StateT machine_state base_system_m))

instance system_mMonadExcept : MonadExcept String system_m :=
  inferInstanceAs (MonadExcept String (StateT machine_state (StateT os_state (ExceptT String Id))))

instance : MonadLift base_system_m system_m :=
  inferInstanceAs (MonadLift base_system_m (StateT machine_state base_system_m))


namespace system_m

protected
def run {a : Type} (m : system_m a) (os : os_state) (s : machine_state) 
  : (Except String ((a × machine_state) × os_state)) := do
  ((m.run s).run os).run

def runSmtM {a : Type} (m : SmtM a) : system_m a := do
  let run' := fun (s : os_state) => 
                  (let r := Smt.runSmtM s.idGen m;
                  (r.fst, {s with trace := (List.map Event.Command r.snd.snd.reverse) ++ s.trace
                                , idGen   := r.snd.fst}));
  monadLift (modifyGet run' : base_system_m a)

def name_term {s : SmtSort} (name : Option String) (tm : Term s) : system_m (Term s) :=
  runSmtM (Smt.nameTerm (name.getD "tmp") tm)

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
  , s_float  := s_float

  , s_bv_imm   := Smt.bvimm
  , s_bool_imm := fun b => if b then Smt.true else Smt.false

  , monad := system_m
  , Monad_backend := inferInstance
  , MonadExcept_backend := inferInstance
  
  , store_word := fun n addr v => do 
                  -- FIXME: might want to name the new state
                  -- emit_trace_event (trace_event.write addr _ v);
                  let addr' ← system_m.name_term (some "addr") addr
                  modify (fun s => machine_state.store_word s stdlib addr' v)
  , read_word  := fun addr n => do
                  let addr' ← system_m.name_term (some "addr") addr
                  let v ← (fun s => machine_state.read_word s stdlib addr' n) <$> get
                  -- emit_trace_event (trace_event.read addr _ v);
                  pure v
               
  , get_gpreg  := fun i => (fun s => machine_state.get_gpreg s i) <$> get
  , s_cond_set_gpreg := fun c i v => do 
    let s ← system_m.name_term (reg.r64_names.get? i.val) v
    modify (machine_state.update_gpreg i (fun old => Smt.smtIte c s old))
  , get_flag  :=  fun i => (fun s => machine_state.get_flag s i) <$> get
  , s_cond_set_flag := fun c i v => 
    modify (machine_state.update_flag i (fun old => Smt.smtIte c v old))
  , get_avxreg  := fun i => (fun s => machine_state.get_avxreg s i) <$> get
  , s_cond_set_avxreg := fun c i v => do
    let s <- system_m.name_term (some ("xmm" ++ reprStr i)) v;
    modify (machine_state.update_avxreg i (fun old => Smt.smtIte c s old))
  
  , s_mux_bool := fun (b : s_bool) (x y : s_bool) => Smt.smtIte b x y
  , s_mux_bv   := fun {n : Nat} (b : s_bool) (x y : bitvec n) => Smt.smtIte b x y
  , s_mux_float := fun {fc : float_class} (b : s_bool) (x y : s_float fc) => Smt.smtIte b x y
  
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
                    else (let pf : (off + m - 1) + 1 - off = m := I_am_really_sorry3 _;
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
  , s_get_ip        := (fun (s : machine_state) => s.ip) <$> get
  , s_set_ip        := fun x => modify (fun s => { s with ip := x })
  , s_cond_set_ip   := fun b x => modify (fun s => { s with ip := Smt.smtIte b x s.ip })

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


  , s_read_cpuid    := pure ()

  } 

end symbolic
end x86
