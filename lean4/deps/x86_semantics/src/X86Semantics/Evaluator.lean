-- Evaluates actions in an environment.
import Galois.Data.Bitvec
import X86Semantics.Common
import X86Semantics.MachineMemory

-- import .sexpr

axiom I_am_really_sorry : ∀(P : Prop),  P 

-- FIXME: move
def annotate {ε} {m} [Monad m] [MonadExcept ε m]
  {a} (f : ε -> ε) (c : m a) : m a := catch c (fun e => throw (f e))

def annotate' {m} [Monad m] [MonadExcept String m]
  {a} (e : String) (c : m a) : m a := annotate (fun s => e ++ ": " ++ s) c

namespace mc_semantics

namespace type 

def assert_types {m} [Monad m] [MonadExcept String m] (t1 t2 : type) : m Unit :=
  if t1 = t2
  then pure () 
  else throw $ "Type mismatch: "-- ++ t1.pp ++ " and " ++ t2.pp ++ " in " ++ repr nenv

def assert_bv {m} [Monad m] [MonadExcept String m] (tp : type) : m Nat :=
  match tp with
  | (bv n) => pure n
  | _      => throw "Not a bitvecor"


end type
end mc_semantics

namespace x86

open mc_semantics
open mc_semantics.type

@[reducible]
def machine_word := bitvec 64

namespace reg

axiom inject_ax0 : 8 + gpreg_type.width' gpreg_type.reg8h ≤ 64
axiom inject_ax1 : ∀(rtp : gpreg_type), 0 + gpreg_type.width' rtp ≤ 64

def inject : ∀(rtp : gpreg_type), bitvec rtp.width' -> machine_word -> machine_word
  | gpreg_type.reg32, b, _   => bitvec.append (bitvec.zero 32) b
  | gpreg_type.reg8h, b, old => old.set_bits 8 b inject_ax0
  | rtp,              b, old => old.set_bits 0 b (inject_ax1 rtp) -- (begin cases rtp; simp end)

def project : ∀(rtp : gpreg_type), machine_word -> bitvec rtp.width'
  | gpreg_type.reg8h, b => b.get_bits 8 8 inject_ax0 -- (begin simp [gpreg_type.width'], exact dec_trivial end)
  | rtp,              b => b.get_bits 0 rtp.width' (inject_ax1 rtp) -- (begin cases rtp; simp end)

end reg

structure machine_state : Type :=
  (mem    : memory)
  (gpregs : Array machine_word) -- 16
  (flags  : Array Bool) -- 32
  (ip     : machine_word)

namespace machine_state

-- Constructs an empty machine state, with 0 where we need a value.
def empty : machine_state := 
  { mem    := memory.empty
  , gpregs := mkArray 16 0
  , flags  := mkArray 32 false
  , ip     := 0
  }

def get_gpreg  (s : machine_state) (idx : Fin 16) : machine_word := 
  -- FIXME
  if h : 16 = s.gpregs.size
  then Array.get s.gpregs (Eq.recOn h idx) else 0



def update_gpreg (idx : Fin 16) (f : machine_word -> machine_word) (s : machine_state) : machine_state :=
  -- FIXME
  if h : 16 = s.gpregs.size 
  then { s with gpregs := Array.set s.gpregs (Eq.recOn h idx) (f (get_gpreg s idx)) }
  else s 

def get_flag  (s : machine_state) (idx : Fin 32) : Bool := 
  if h : 32 = s.flags.size
  then Array.get s.flags (Eq.recOn h idx) else false

def update_flag (idx : Fin 32) (f : Bool -> Bool) (s : machine_state) : machine_state :=
  if h : 32 = s.flags.size
  then { s with flags := Array.set s.flags (Eq.recOn h idx) (f (get_flag s idx)) }
  else s 

-- def store_bytes (addr : machine_word) (bs : List (bitvec 8)) (s : machine_state) : machine_state := 
--   { s with mem := s.mem.store_bytes addr bs }

-- def read_bytes (s : machine_state) (addr : machine_word) (n : Nat) : Option (List (bitvec 8)) :=
--   s.mem.read_bytes addr n

-- lemma read_bytes_length {s : machine_state} {addr : machine_word} {n : Nat} {bs : List (bitvec 8)}
--   : read_bytes s addr n = some bs -> bs.length = n := memory.read_bytes_length

def store_word {n : Nat} (s : machine_state) (addr : machine_word) (b : bitvec (8 * n)) : machine_state := 
  { s with mem := s.mem.store_word addr b }

def read_word (s : machine_state) (addr : machine_word) (n : Nat) : Option (bitvec (8 * n)) :=
  s.mem.read_word addr n

def print_regs (s : machine_state) : String :=
  let lines := List.zipWith (fun n (r : bitvec 64) => if r = 0 then "" else (n ++ ": " ++ r.pp_hex ++ ", ")) reg.r64_names s.gpregs.toList;
  String.join lines

def print_set_flags (s : machine_state) : String :=
  let lines := List.zipWith (fun n (r : Bool) => if r then n else "") reg.flag_names s.flags.toList;
  "[" ++ String.intercalate ", " (List.filter (fun s => s.length > 0) lines) ++ "]"

end machine_state

inductive arg_lval
  | reg {} {tp : type}  : concrete_reg tp -> arg_lval 
  | memloc (width : Nat) (addr : machine_word) : arg_lval 

namespace arg_lval

def repr : arg_lval -> String
  | (reg r)             => r.repr
  | (memloc width addr) => HasRepr.repr addr ++ "@" ++ HasRepr.repr width

instance arg_lval_repr : HasRepr arg_lval := ⟨repr⟩

end arg_lval

-- This also needs to be a StateMonad machine_state (it owns that)
class SystemM (m : Type -> Type) extends Monad m, MonadState machine_state m, MonadExcept String m :=
  (os_transition    {} : m Unit )
  (emit_read_event  {} : machine_word -> ∀(n : Nat), bitvec n -> m Unit)
  (emit_write_event {}  : machine_word -> ∀(n : Nat), bitvec n -> m Unit)

section with_nat_env

variables (system_m : Type -> Type) [SystemM system_m]

@[reducible]
def value : type -> Type
  | (bv e) => bitvec e
  | bit    => Bool
  | float  => Unit -- FIXME
  | double => Unit -- FIXME
  | x86_80 => Unit -- FIXME  
  | (vec w tp) => Array /- (eval_nat_expr w) -/ (value tp) -- FIXME
  | (pair tp tp') => value tp × value tp'
  | (fn arg res) => (value arg) -> (value res)

-- namespace value

-- def value.repr : ∀{tp : type}, value tp -> String
--   | (bv e) b                => has_repr.repr b
--   | (fn _ _ ) _             => "<function>"
--   | _ _                     => "Unsupported type"


-- instance value_repr {tp : type} : has_repr (value tp) := ⟨value.repr⟩

-- end value

-- Corresponding to the binder type, more or less.
inductive arg_value 
  -- natv is here for completeness --- the presumption is that a
  -- one_of param is only used in types, but in case it is not, we
  -- include a binding in the environment,
  | natv             : Nat        -> arg_value 
  -- covers reg, addr, and lhs bindings
  | lval             : arg_lval -> arg_value
  | rval {tp : type} : value tp -> arg_value

-- namespace arg_value

-- def repr : arg_value -> String 
--   | (lval l) => l.repr
--   | (rval v)  => v.repr

-- instance arg_value_repr : has_repr arg_value := ⟨repr⟩

-- end arg_value

@[reducible]
def environment := List arg_value

-- machine state is stored in the underlying monad
structure evaluator_state : Type :=
  (environment   : environment) -- read only, but reading can fail
  (locals        : RBMap Nat (Sigma value) (fun (n n' : Nat) => decide (n < n')))

-- namespace evaluator_state

def evaluator_state.init : evaluator_state := 
  { environment   := []
  , locals        := {}
  }

-- end evaluator_state

-- Monad for evaluating with failure.  This nesting might be useful to get the ip where things break?
@[reducible]
def evaluator := StateT evaluator_state (ExceptT String system_m)

-- FIXME: this is repeated from the stdlib, not sure why it needs to be
instance (ε): MonadExcept ε (Except ε) := 
  { throw := fun α e => Except.error e, catch := fun α m f => match m with | (Except.error e) => f e | _ => m }

instance (ε) [Inhabited ε] : Alternative (Except ε) := 
  { failure := fun α => Except.error (arbitrary ε)
  , orelse  := fun α => MonadExcept.orelse }

instance MonadExcept_ExceptT (ε) (m)  [Monad m]: MonadExcept ε (ExceptT ε m) := 
  { throw := fun α e => ExceptT.mk (pure (Except.error e))
  , catch := fun α m f => ExceptT.mk (do
          v <- m.run;
          match v with | (Except.error e) => (f e).run | _ => ExceptT.mk (pure v) )}

instance Alternative_ExceptT (ε) (m) [Inhabited ε] [Monad m] : Alternative (ExceptT ε m) := 
  { failure := fun α => throw (arbitrary ε)
  , orelse  := fun α => MonadExcept.orelse }


-- theorem value.type_eval_is_id: ∀{tp : type}, value nenv (eval_type nenv tp) = value nenv tp :=
--   I_am_really_sorry _
-- lemma value.type_eval_is_id: ∀{tp : type}, value (eval_type tp) = value tp :=
-- begin  
--   intros,
--   induction tp,
--   case bv { refl },
--   case fn { simp [value, eval_type, type.eval_default], rw [ tp_ih_arg, tp_ih_res ] },
--   repeat { refl }
-- end

def value.eval_cong {tp tp' : type} (pf : tp = tp') (v : value nenv tp) 
  : value nenv tp' := Eq.recOn pf v


-- begin
--   rw <- value.type_eval_is_id,
--   rw <- value.type_eval_is_id at v,
--   exact (eq.rec v pf)   
-- end

-- This allows us to resolve arith in nat_exprs
def value.type_check {m} [Monad m] [MonadExcept String m] (tp : type) (v : value nenv tp) (tp' : type)
  : m (value nenv tp') :=
  if H : eval_type nenv tp = eval_type nenv tp'
  then pure (value.eval_cong nenv H v)
  else throw "type_check: arg type mismatch"

-- end value
-- def system_m.map_machine_state (f : machine_state → machine_state) : system_m system_config.os_state Unit :=
--   modify (fun (s : system_state system_config.os_state) => { s with machine_state := f s.machine_state })

section SystemM
open SystemM

-- system_m stuff
def SystemM.read_memory_at (addr : machine_word) (n : Nat) : system_m (bitvec n) := do
    s <- get;
    match s.read_word addr (n / 8) with
    | none     => throw "read_memory_at: no bytes at addr" 
    | (some w) => 
      if H : 8 * (n / 8) = n
      then do let res := bitvec.cong H w;
              emit_read_event addr n res;
              pure res
      else throw "read_memory_at: width not a multiple of 8"

def SystemM.write_memory_at : ∀{tp : type} (addr : machine_word) (bytes : value nenv tp)
  , system_m Unit
  | (bv e), addr, bytes =>
    let width := eval_nat_expr nenv e;
    (if H : width = 8 * (width / 8)
        then do modify (fun (s : machine_state) => s.store_word addr (bitvec.cong H bytes));
                emit_write_event addr width bytes
        else throw "write_memory_at: width not a multiple of 8")
  | _, _, _ => throw "write_memory_at not a bv"

end SystemM
-- namespace evaluator
def evaluator.run {a : Type} (m : evaluator system_m nenv a) 
                             (s : evaluator_state nenv) : system_m (Except String (a × evaluator_state nenv)) :=
  (m.run s).run

def evaluator.run' {a : Type} (m : evaluator system_m nenv a) (e : environment nenv) : system_m a :=
  do r <- evaluator.run system_m nenv m { evaluator_state . environment := e, locals := {} };
     match r with
     | Except.ok v    => pure v.fst
     | Except.error e => throw e

-- def evaluator.run' {a : Type} (m : evaluator system_m nenv a) (e : environment nenv) : system_m a :=
--     adaptState' (fun (s : system_state system_config.os_state) => 
--                      { evaluator_state . 
--                        system_state  := s
--                      , environment   := e
--                      , locals        := {}
--                      })
--                 (fun (s : evaluator_state nenv) => s.system_state)
--                 m

def evaluator.run_system_m {a : Type} (m : system_m a) : evaluator system_m nenv a :=
    monadLift m
    -- adaptState (fun (s : evaluator_state nenv) => (s.system_state, s))
    --          (fun s s' => { s' with system_state := s })
    --          m

def evaluator.map_machine_state (f : machine_state → machine_state) : evaluator system_m nenv Unit :=
    monadLift (modify f : system_m Unit)

def evaluator.with_machine_state {a : Type} (f : machine_state → a) : evaluator system_m nenv a :=
    monadLift (f <$> (get : system_m machine_state))

def evaluator.read_memory_at (addr : machine_word) (n : Nat) : evaluator system_m nenv (bitvec n) := do
  evaluator.run_system_m system_m nenv (SystemM.read_memory_at system_m addr n)

def evaluator.write_memory_at {tp : type} (addr : machine_word) (bytes : value nenv tp) :
  evaluator system_m nenv Unit :=
  evaluator.run_system_m system_m nenv (SystemM.write_memory_at system_m nenv addr bytes)

def evaluator.arg_at_idx (idx : Nat) : evaluator system_m nenv (arg_value nenv) :=
  do s <- get;
     match s.environment.get? idx with
       | (some a) => pure a
       | none     => throw "evaluator.arg_at_idx: no arg at idx"

-- We should factor out the type check, although it might depend on
-- the functor (value in this case) if we generalise equality
def evaluator.local_at_idx (idx : Nat) (tp : type) : evaluator system_m nenv (value nenv tp) :=
  do s <- get;
     (match s.locals.find? idx with
     | (some (Sigma.mk tp' v)) => value.type_check nenv _ v tp
     | none                    => throw "local_at_idx: no arg at idx")

theorem width_width' : ∀(rtp : gpreg_type), eval_nat_expr nenv rtp.width = rtp.width' :=
  I_am_really_sorry _

def concrete_reg.set : ∀{tp : type}, concrete_reg tp -> value nenv tp -> evaluator system_m nenv Unit
  | ._, (concrete_reg.gpreg idx rtp), b => 
    let b' : bitvec rtp.width' := Eq.rec b (width_width' nenv rtp);
    evaluator.map_machine_state system_m nenv (machine_state.update_gpreg idx (reg.inject rtp b'))
  | ._, (concrete_reg.flagreg idx),   b => 
    evaluator.map_machine_state system_m nenv (machine_state.update_flag idx (fun _ => b))
  
def concrete_reg.from_state : ∀{tp : type}, concrete_reg tp -> machine_state 
  -> value nenv tp
  | _, (concrete_reg.gpreg idx rtp), s => 
    let v := reg.project rtp (s.get_gpreg idx);
    let v' : bitvec (eval_nat_expr nenv rtp.width) 
        := Eq.rec v (width_width' nenv rtp).symm;
    v'
  | _, (concrete_reg.flagreg idx),   s => s.get_flag idx

def concrete_reg.read {tp : type} (r : concrete_reg tp) : evaluator system_m nenv (value nenv tp) := 
    evaluator.with_machine_state system_m nenv (concrete_reg.from_state nenv r)

-- namespace arg_lval 

def arg_lval.to_value' : arg_lval -> ∀(tp : type), system_m (value nenv tp)
  | (@arg_lval.reg tp r), tp' => do
    s <- get;
    value.type_check nenv tp (concrete_reg.from_state nenv r s) tp'
  | (arg_lval.memloc width addr), tp' => do
    w <- SystemM.read_memory_at system_m addr width;
    value.type_check nenv (bv width) w tp'

def arg_lval.to_value : arg_lval -> ∀(tp : type), evaluator system_m nenv (value nenv tp)
  | (@arg_lval.reg tp r), tp' => do v <- concrete_reg.read system_m nenv r;
                                   value.type_check nenv tp v tp'
  | (arg_lval.memloc width addr), tp' => do
    v <- evaluator.read_memory_at system_m nenv addr width;
    value.type_check nenv (bv width) v tp'

def arg_lval.set_value : arg_lval -> ∀{tp : type}, value nenv tp 
  -> evaluator system_m nenv  Unit
  | (@arg_lval.reg tp r), tp', v => do v' <- value.type_check nenv _ v tp;
                                       concrete_reg.set system_m nenv r v'
  | (arg_lval.memloc _width addr), tp, v => do
    evaluator.write_memory_at system_m nenv addr v

-- def read_memory_at (av : arg_value) (n : Nat) : evaluator trace_event (bitvec (8 * n)) :=
--   match av with 
--   | (@arg_value.bv 64 addr) => 
--   | _                      => throw "addr.read: not a 64-bit bitvecor"
--   end

-- Can fail if types mismatch
def arg_value.to_value : arg_value nenv -> ∀(tp : type), evaluator system_m nenv (value nenv tp)
  | (arg_value.natv _ _),  _ => throw "arg_value.to_value: saw a natv"
  | (arg_value.lval _ l), tp => arg_lval.to_value system_m nenv l tp
  | (arg_value.rval v), tp => value.type_check nenv _ v tp

def arg_value.set_value : arg_value nenv -> ∀{tp : type}, value nenv tp -> evaluator system_m nenv Unit
  | (arg_value.lval _ l), tp, v => arg_lval.set_value system_m nenv l v
  | _, _, _ => throw "arg_value.set_value: not an lvalue"

def addr.read : ∀{tp : type}, addr tp -> evaluator system_m nenv (value nenv tp)
  | tp, (addr.arg idx) => do 
      av <- evaluator.arg_at_idx system_m nenv idx;
      arg_value.to_value system_m nenv av tp -- FIXME: we should really check if this is a memloc first.
      -- w  <- av.read_memory_at n,
      -- return (value.bv w)

def addr.set : ∀{tp : type}, addr tp -> value nenv tp -> evaluator system_m nenv Unit
  | tp, (addr.arg idx), v => do 
      av <- evaluator.arg_at_idx system_m nenv idx; -- FIXME: we should really check if this is a memloc first.
      arg_value.set_value system_m nenv av v

-- This is the least-worst option.  The other alternative is to have a
-- value constructor for functions, which we only need here.
inductive hlist.{u,v} {α : Type u} (f : α -> Type v): List α -> Type (max u v)
  | hnil  : hlist []
  | hcons {xs : List α} (x : α) : f x -> hlist xs -> hlist (x :: xs)

-- namespace nat_expr

-- def eval' (ne : nat_expr) : evaluator trace_event Nat := do
--   s <- get,
--   match nat_expr.eval s.environment ne with
--   | none => throw "nat_expr.eval': couldn't eval"
--   | (some n) => return n
--   end
-- end nat_expr

-- def prim_binop (e : nat_expr) (p : ∀{n : Nat}, bitvec n -> bitvec n -> bitvec n) :=
--   evaluator.with_nat_expr_as_nat' (fun i => value (bv i .→ bv i .→ bv i)) e (fun n => return (@p n))

-- lemma eval_add_eq {x y} : eval_nat_expr (x + y) =  (eval_nat_expr x + eval_nat_expr y) :=
-- begin
--   simp [eval_nat_expr, nat_expr.eval_add_eq, has_seq.seq], 
-- end

  -- by { cases x; cases y; simp [
  --                              has_add.add, has_seq.seq, nat_expr.do_add
  --                             , nat_expr.eval] }

-- FIXME: move
-- Might be easier to define in terms of to_int/from_int etc.
def bitvec.uext {n} (m : Nat) (p: n ≤ m) (x:bitvec n) : bitvec m :=
  bitvec.set_bits 0 0 x (I_am_really_sorry _) -- (begin simp, exact p end)
  
def bitvec.sext {n} (m : Nat) (p: n ≤ m) (x:bitvec n) : bitvec m :=
  bitvec.set_bits (if x.msb then (bitvec.zero m).not else 0) 0 x (I_am_really_sorry _)-- (begin simp, exact p end)

def bitvec.trunc {n} (m : Nat) (p: m ≤ n) (x:bitvec n) : bitvec m :=
  bitvec.get_bits x 0 m (I_am_really_sorry _) --(begin simp, exact p end)

def bit_to_bitvec (n : Nat) (b : Bool) : bitvec n := 
  if b then 1 else 0

-- lemma eval_default_2 {e} : nat_expr.eval_default e 2 = 2 := rfl

-- lemma nat_expr_eval_2 : eval_nat_expr 2 = 2 := rfl

def type.has_eq : type -> Prop
  | (bv _)     => True
  | bit        => True
  | float      => True 
  | double     => True 
  | x86_80     => True
  | (vec _ tp) => type.has_eq tp 
  | (pair tp tp') => type.has_eq tp ∧ type.has_eq tp'
  | (fn _ _)   => False -- could probably come up with something, but nothing efficient

@[reducible]
def type.has_eq_dec : ∀(tp : type), Decidable (type.has_eq tp) 
  | (bv _)     => isTrue True.intro
  | bit        => isTrue True.intro  
  | float      => isTrue True.intro  
  | double     => isTrue True.intro  
  | x86_80     => isTrue True.intro  
  | (vec _ tp) => type.has_eq_dec tp
  | (pair tp tp') => @And.Decidable _ _ (type.has_eq_dec tp) (type.has_eq_dec tp')
  | (fn _ _)   => isFalse notFalse

instance decidable_pred_type_has_eq: DecidablePred type.has_eq := type.has_eq_dec

-- set_option trace.eqn_compiler true
-- set_option trace.debug.eqn_compiler true

-- def tester1 : ∀{tp : type}, value nenv tp -> value nenv tp -> Bool
--   | (bv _)     => fun v1 v2 => v1 = v2
--   | _ => fun _ _ => true

-- def tester2 : ∀{tp : type}, value nenv tp -> value nenv tp -> Bool
--   | (bv _)     => fun v1 v2 => v1 - v2 = 0
--   | _ => fun _ _ => true

-- #print tester2._main

def value.partial_eq : ∀{tp : type}, type.has_eq tp -> value nenv tp -> value nenv tp -> Bool
  | (bv _), _, v1, v2      => (v1 - v2 = 0) -- FIXME: bug in the eqn compiler?
  | bit,    _, v1, v2      => (v1 = v2)
  | float,  _, v1, v2      => (v1 = v2)
  | double, _, v1, v2     => (v1 = v2)
  | x86_80, _, v1, v2     => (v1 = v2)
  | (vec _ tp), pf, v1, v2 => 
     let pf' : type.has_eq tp := pf;
        (List.zip (Array.toList v1) (Array.toList v2)).all (fun (v : (value nenv tp × value nenv tp)) => value.partial_eq pf' v.fst v.snd)
  | (pair tp tp'), pf, v1, v2 => false -- FIXME
    -- and (value.partial_eq pf.left v1.fst v2.fst) (value.partial_eq pf.right v1.snd v2.snd)

-- Returns the number of bits that are tt mod 2
def bitvec.parity {n : Nat} (b : bitvec n) : Bool :=
  bitvec.foldl xor false b

-- example : bitvec.parity (3 : bitvec 4) = false := by refl
-- example : bitvec.parity (7 : bitvec 4) = true := by refl

def prim.eval : ∀{tp : type}, prim tp -> evaluator system_m nenv (value nenv tp)
  -- `(eq tp)` returns `true` if two values are equal.
  | ._, (prim.eq tp) => 
    if pf : type.has_eq tp 
    then pure (value.partial_eq nenv pf)
    else throw "prim.eval.eq: eq at unsupported type"
  -- `(neq tp)` returns `true` if two values are not equal.
  | ._, (prim.neq tp) => 
    if pf : type.has_eq tp 
    then pure (fun v1 v2 => not (value.partial_eq nenv pf v1 v2))
    else throw "prim.eval.neq: neq at unsupported type"
  -- `(mux tp) c t f` evaluates to `t` when `c` is true and `f` otherwise.
  -- This only evaluates `t` when `c` is true, and only evaluates `f` when
  -- `c` is false.
  | ._, (prim.mux tp) => pure (fun b l r => if b then l else r)

  -- `zero` is the zero bit
  | ._, prim.bit_zero => pure false
  -- `one` is the one bit
  | ._, prim.bit_one => pure true

  | ._, prim.bit_or  => pure or
  | ._, prim.bit_and => pure and
  | ._, prim.bit_xor => pure xor

  -- `bvnat` constructs a bit vector from a natural number.
  | ._, (prim.bv_nat w n) => pure (bitvec.of_nat (eval_nat_expr nenv w) (eval_nat_expr nenv n))
  -- `(add i)` returns the sum of two i-bit numbers.
  | ._, (prim.add i)        => pure bitvec.add
  -- `(adc i)` returns the sum of two i-bit numbers and a carry bit.
  | ._, (prim.adc i)         => pure (fun x y b => bitvec.add x (bitvec.add y (bit_to_bitvec _ b)))
  | ._, (prim.uadc_overflows i) => pure (fun x y b => bitvec.ult (x + y + bit_to_bitvec (eval_nat_expr nenv i) b) x)
  | ._, (prim.sadc_overflows i) => pure (fun x y b => bitvec.slt (x + y + bit_to_bitvec (eval_nat_expr nenv i) b) x)
  -- `(bvsub i)` substracts two i-bit bitvectors.
  | ._, (prim.sub i) => pure bitvec.sub
  -- `(ssbb_overflows i)` true if signed sub overflows, the bit
  -- is a borrow bit.
  -- FIXME: is this correct?
  | ._, (prim.ssbb_overflows i) => 
    pure (fun x y b => bitvec.slt x (x - y - bit_to_bitvec (eval_nat_expr nenv i) b))
  -- `(usbb_overflows i)` true if unsigned sub overflows,
  -- the bit is a borrow bit.
  | ._, (prim.usbb_overflows i) => pure (fun x y b => bitvec.ult x (x - y - bit_to_bitvec (eval_nat_expr nenv i) b))

  -- `(neg tp)` Two's Complement negation.
  | ._, (prim.neg i) => pure bitvec.neg

  -- `(mul i)` returns the product of two i-bit numbers.
  | ._, (prim.mul i)            => pure bitvec.mul

  -- `(quotRem i) n d` returns a pair `(q,r)` where `q` is a `floor (n/d)`
  -- and `r` is `n - d * floor (n/d)`.
  -- `n` and `d` are treated as unsigned values.
  -- If `d = 0` or `floor(n/d) >= 2^n`, then this triggers a #DE exception.
  | ._, (prim.quotRem i) => throw "prim.eval.quotRem unimplemented"

  -- `(squotRem i) n d` returns a pair `(q,r)` where `q` is a `trunc (n/d)`
  -- and `r` is `n - d * trunc (n/d)`.  `trunc` always round to zero.
  -- `n` and `d` are treated as signed values.
  -- If `d = 0`, `trunc(n/d) >= 2^(n-1)` or `trunc(n/d) < -2^(n-1), then this
  -- triggers a #DE exception when evaluated.
  | ._, (prim.squotRem i) => throw "prim.eval.squotRem unimplemented"

  | ._, (prim.ule i) => pure (fun x y => bitvec.ule x y)
  | ._, (prim.ult i) => pure (fun x y => bitvec.ult x y)

  -- `(slice w u l)` takes bits `u` through `l` out of a `w`-bit number.
  --  prim (bv w .→ bv (u+1-l))
  --  slice {w: Nat} (u l k:Nat) (H: w = k + (u + 1 - l)) (x: bitvec w) : bitvec (u + 1 - l)
  | tp, (prim.slice w u l) => do
       let n := eval_nat_expr nenv u + 1 - eval_nat_expr nenv l;
       H <- annotate' "slice" (assert (eval_nat_expr nenv w = (eval_nat_expr nenv w - n + n)));
       let f : bitvec (eval_nat_expr nenv w) → bitvec n :=
         (bitvec.slice (eval_nat_expr nenv u) (eval_nat_expr nenv l) (eval_nat_expr nenv w - n) H.default);
       let rewr : value nenv (bv (u + 1 - l)) = value nenv (bv (nat_expr.lit n)) := I_am_really_sorry _ ;
       pure (fun x => Eq.recOn rewr.symm (f x))
       -- pure (begin
       --   have rewr : value nenv (bv (u + 1 - l)) = value nenv (bv (nat_expr.lit n)) :=
       --     begin simp [n, value, nat_expr.eval_default_sub_eq
       --                , nat_expr.eval_default_add_eq
       --                , eval_nat_expr, nat_expr.eval_default], rw add_comm, refl end,
       --   simp [value], rw rewr,
       --   exact (bitvec.slice (eval_nat_expr nenv u) (eval_nat_expr nenv l) (eval_nat_expr nenv w - n) H.default)
       --  end)
  -- `(sext i o)` sign extends an `i`-bit number to a `o`-bit number.
  | ._, (prim.sext i o) => do H <- annotate' "sext" (assert (eval_nat_expr nenv i ≤ eval_nat_expr nenv o));
                             pure (bitvec.sext (eval_nat_expr nenv o) H.default)
  -- `(uext i o)` unsigned extension of an `i`-bit number to a `o`-bit number.
  | ._, (prim.uext i o) => do H <- annotate' "uext" (assert (eval_nat_expr nenv i ≤ eval_nat_expr nenv o));
                             pure (bitvec.uext (eval_nat_expr nenv o) H.default)
  -- `(trunc i o)` truncates an `i`-bit number to a `o`-bit number.
  | ._, (prim.trunc i o) => do H <- annotate' "trunc" (assert (eval_nat_expr nenv o ≤ eval_nat_expr nenv i));
                              pure (bitvec.trunc (eval_nat_expr nenv o) H.default)

  | ._, (prim.cat i) => pure (fun x y => 
       let prf : eval_nat_expr nenv i + eval_nat_expr nenv i = eval_nat_expr nenv (2 * i) := I_am_really_sorry _;
       bitvec.cong prf (bitvec.append x y))
  --(begin simp [eval_nat_expr, nat_expr.eval_default_mul_eq, nat_expr.eval, eval_default_2, two_mul], 
  --end)

  -- | bv_least_nibble (i:Nat) : prim (bv i .→ bv 4)
  | ._, (prim.msb i) => pure bitvec.msb
  | ._, (prim.bv_and i) => pure bitvec.and
  | ._, (prim.bv_or i)  => pure bitvec.or
  | ._, (prim.bv_xor i) => pure bitvec.xor
  | ._, (prim.bv_complement i) => pure bitvec.not
  | ._, (prim.shl i)    => pure (fun x (y : bitvec 8) => bitvec.shl x y.to_nat)
  --- `(shl_carry w) c b i` returns the `i`th bit
  --- in the bitvector [c]++b where `i` is treated as an unsigned
  --- number with `0` as the most-significant bit.
  -- e.g., If `i` is `0`, then this returns `c`.  If `i`
  -- exceeds the number of bits in `[c] ++ b` (i.e., i >= w+1),
  -- the the result is false.
  | ._, (prim.shl_carry w) => pure (fun c b (i : bitvec 8) => 
       match i.to_nat with
       | Nat.zero        => c
       -- FIXME: is this the intended behaviour?
       | (Nat.succ n) => if n < eval_nat_expr nenv w
                         then bitvec.nth b (eval_nat_expr nenv w - n - 1) else false 
       )
   --- `(shr i) x y` shifts the bits in `x` to the right by
   --- `y` bits where `y` is treated as an unsigned integer.
   --- The new bits shifted in from the right are all zero.
   | ._, (prim.shr i) => pure (fun x (y : bitvec 8) => bitvec.ushr x y.to_nat)
   --- `(shr_carry w) b c i` returns the `i`th bit
   --- in the bitvector b++[c] where `i` is treated as an unsigned
   --- number with `0` as the least-significant bit.
   -- e.g., If `i` is `0`, then this returns `c`.  If `i`
   -- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
   -- the the result is false.
  | ._, (prim.shr_carry w) => pure (fun b c (i : bitvec 8) => 
       match i.to_nat with
       | Nat.zero     => c
       | (Nat.succ n) => -- @ite _ (n < eval_nat_expr nenv w) (Nat.decLt _ _) _ (bitvec.nth b n) false
if n < eval_nat_expr nenv w 
then bitvec.nth b n
else false
       )
   --- `(sar i) x y` arithmetically shifts the bits in `x` to
   --- the left by `y` bits where `y` is treated as an unsigned integer.
   --- The new bits shifted in all match the most-significant bit in y.
   | ._, (prim.sar i) => pure (fun x (y : bitvec 8) => bitvec.sshr x y.to_nat)
   --- `(sar_carry w) b c i` returns the `i`th bit
   --- in the bitvector b++[c] where `i` is treated as an unsigned
   --- number with `0` as the least-significant bit.
   -- e.g., If `i` is `0`, then this returns `c`.  If `i`
   -- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
   -- the the result is equal to the most-signfiicant bit.
   | ._, (prim.sar_carry w) => pure (fun b c (i : bitvec 8) => 
       match i.to_nat with
       | Nat.zero     => c
       | (Nat.succ n) =>
         -- @ite _ (n < eval_nat_expr nenv w) (Nat.decLt _ _) _ 
         --      (bitvec.nth b n)
         --      (bitvec.msb b)
       (if n < eval_nat_expr nenv w 
                          then bitvec.nth b n
                          else bitvec.msb b)
         )
   
  | ._, (prim.even_parity i) => pure (fun b => bitvec.parity b = false)
  -- `(bsf i)` returns the index of least-significant bit that is 1.
  | ._, (prim.bsf i)         => throw "prim.eval.bsf unimplemented"
  -- `(bsr i)` returns the index of most-significant bit that is 1.
  | ._, (prim.bsr i)         => throw "prim.eval.bsr unimplemented"
  -- `(bswap i)` reverses the bytes in the bitvector.
  | ._, (prim.bswap i)       => throw "prim.eval.bswap unimplemented"
  -- `(btc w j) base idx` interprets base as bitvector and returns
  -- a bitvector contains the same bits as `base` except the `i`th bit
  -- (where 0 denotes the least-significant bit) is complemented.
  -- The value `i` is `idx` as a unsigned integer modulo `w`.
  | ._, (prim.btc w j)         => throw "prim.eval.btc unimplemented"
  -- `(btr w j) base idx` interprets base as bitvector and returns
  -- a bitvector contains the same bits as `base` except the `i`th bit
  -- (where 0 denotes the least-significant bit) is cleared.
  -- The value `i` is `idx` as a unsigned integer modulo `w`.
  | ._, (prim.btr w j)         => throw "prim.eval.btr unimplemented"
  -- `(bts w j) base idx` interprets base as bitvector and returns
  -- a bitvector contains the same bits as `base` except the `i`th bit
  -- (where 0 denotes the least-significant bit) is set.
  -- The value `i` is `idx` as a unsigned integer modulo `w`.
  | ._, (prim.bts w j)         => throw "prim.eval.bts unimplemented"

  -- `bv_to_x86_80` converts a bitvector to an extended precision number (lossless)
  | ._, (prim.bv_to_x86_80 w)  => throw "prim.eval.bv_to_x86_80 unimplemented"
  -- `float_to_x86_80` converts a float to an extended precision number (lossless)
  | ._, prim.float_to_x86_80   => throw "prim.eval.float_to_x86_80 unimplemented"
  -- `double_to_x86_80` converts a double to an extended precision number (lossless)
  | ._, prim.double_to_x86_80   => throw "prim.eval.double_to_x86_80 unimplemented"
  -- `x87_fadd` adds two extended precision values using the flags in the x87 register.
  | ._, prim.x87_fadd           => throw "prim.eval.dx87_fadd unimplemented"

  -- Return first element of a pair
  | ._, (prim.pair_fst x y) => pure (fun (v : value nenv x × value nenv y) => v.fst)
  -- Return second element of a pair.
  | ._, (prim.pair_snd x y) => pure (fun (v : value nenv x × value nenv y) => v.snd)

def value.make_undef : ∀(tp : type), value nenv tp 
  | (bv e) => bitvec.of_nat (eval_nat_expr nenv e) 0
  | bit    => false
  | float  => ()
  | double => ()
  | x86_80 => ()
  | (vec w tp) => mkArray (eval_nat_expr nenv w) (value.make_undef tp)
  | (pair tp tp') => (value.make_undef tp, value.make_undef tp')
  | (fn arg res) => fun _ => value.make_undef res

def expression.eval : ∀{tp : type}, expression tp -> evaluator system_m nenv (value nenv tp)
  | ._, (expression.primitive p) => prim.eval system_m nenv p
  | ._, (@expression.bit_test wr wi re idxe) => do
    r   <- expression.eval re;
    idx <- expression.eval idxe;
    let idx' := idx.to_nat % eval_nat_expr nenv wr;
    pure (r.nth idx')
  | ._, (expression.mulc m xe) => do
    x <- expression.eval xe;
    pure (bitvec.mul (bitvec.of_nat 64 (eval_nat_expr nenv m)) x)
  | ._, (expression.quotc m xe) => throw "expression.eval.quotc unimplemented"
  | ._, (expression.undef tp)   => pure (value.make_undef nenv tp)
  | ._, (expression.app f a) => (expression.eval f) <*> (expression.eval a)
  | ._, (expression.get_reg r) => concrete_reg.read system_m nenv r
  | ._, (expression.read tp addre) => do
    addr   <- expression.eval addre;
    (match tp with
      | (bv we) => evaluator.read_memory_at system_m nenv  addr (eval_nat_expr nenv we)
      | _ => throw "expression.eval.read Trying to store non-bitvector")

  | ._, (expression.streg idx) => throw "expression.eval.streg unimplemented"
  | ._, (expression.get_local idx tp) => evaluator.local_at_idx system_m nenv idx tp
  -- This is overly general, we might not know that av here is an rval
  | ._, (expression.imm_arg idx tp) => do
    av <- evaluator.arg_at_idx system_m nenv idx;
    (match av with
    | (arg_value.rval v) => value.type_check nenv _ v tp
    | _ => throw "expression.eval.imm_arg Not an rval")

  | ._, (expression.addr_arg idx) => do
    av <- evaluator.arg_at_idx system_m nenv idx;
    (match av with
    | (arg_value.lval _ (arg_lval.memloc _ addr)) => pure addr
    | _ => throw "expression.eval.addr_arg Not an memloc lval")
  -- FIXME: isn't specific to arg_lval
  | ._, (expression.read_arg idx tp) => do
    av <- evaluator.arg_at_idx system_m nenv idx;
    arg_value.to_value system_m nenv av tp

def evaluator.set_ip (new_ip : bitvec 64) : evaluator system_m nenv Unit :=
  evaluator.map_machine_state system_m nenv (fun (s : machine_state) => { s with ip := new_ip })

def lhs.set : ∀{tp : type}, lhs tp -> value nenv tp -> evaluator system_m nenv Unit
  | ._, (lhs.set_reg r), v        => concrete_reg.set system_m nenv  r v
  | ._, (lhs.write_addr ae tp), v => do
    a <- expression.eval system_m nenv ae;
    evaluator.write_memory_at system_m nenv a v
  | ._, (lhs.write_arg idx _tp), v => do
    av <- evaluator.arg_at_idx system_m nenv idx;
    -- fixme: we ignore tp here?
    arg_value.set_value system_m nenv av v
  | ._, (lhs.streg idx), v  => throw "lhs.set: unsupported FP write"

def lhs.read : ∀{tp : type}, lhs tp -> evaluator system_m nenv (value nenv tp)
  | ._, (lhs.set_reg r)        => concrete_reg.read system_m nenv r
  | ._, (lhs.write_addr ae tp) => do
    addr <- expression.eval system_m nenv ae;
   (match tp with
     | (bv we) => evaluator.read_memory_at system_m nenv addr (eval_nat_expr nenv we)
     | _ => throw "lhs.read Trying to store non-bitvector")
  | ._, (lhs.write_arg idx tp) => do
    av <- evaluator.arg_at_idx system_m nenv idx;
    -- fixme: we ignore tp here?
    arg_value.to_value system_m nenv av tp
  | ._, (lhs.streg idx) => throw "lhs.set: unsupported FP write"

def evaluator.push64 (v : value nenv (bv 64)) : evaluator system_m nenv Unit := do
  sp <- lhs.read system_m nenv rsp;
  let sp' := sp - 8; do
    lhs.set system_m nenv rsp sp';
    evaluator.write_memory_at system_m nenv sp' v

def read_cpuid : evaluator system_m nenv Unit :=
  -- Copied from the cpuid results from my macbook
  -- Note: CPUID is allowed to return 0s 
  let cpuid_values : RBMap Nat (bitvec 32 × bitvec 32 × bitvec 32 × bitvec 32) (fun x y => decide (x < y)) :=
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
                    ] (fun x y => decide (x < y)); -- FIXME: we need to look at rcx sometimes as well
    let cpuid_fn (n : Nat) : (bitvec 32 × bitvec 32 × bitvec 32 × bitvec 32) :=
      match cpuid_values.find? n with
      | none     => (0, 0, 0, 0)
      | (some r) => r;
    do 
      raxv <- lhs.read system_m nenv rax;
      match cpuid_fn raxv.to_nat with 
      | (axv, bxv, cxv, dxv) => do 
        lhs.set system_m nenv eax axv;
        lhs.set system_m nenv ebx bxv;
        lhs.set system_m nenv ecx cxv;
        lhs.set system_m nenv edx dxv

def event.eval : event -> evaluator system_m nenv Unit
  | event.syscall => monadLift (SystemM.os_transition : system_m Unit)
    -- adaptState (fun (s : evaluator_state nenv) => (s.system_state, s))
    --            (fun s s' => { s' with system_state := s })
    --            (system_m.os_transition)
  | (event.unsupported msg) => throw ("event.eval: unsupported: " ++ msg)
  | event.pop_x87_register_stack => throw "pop_x87_register_stack"
  | (event.call addr) => do
    new_ip <- expression.eval system_m nenv addr;
    old_ip <- evaluator.with_machine_state system_m nenv (fun s => s.ip);
    evaluator.push64 system_m nenv old_ip;
    evaluator.set_ip system_m nenv new_ip

  | (event.jmp addr) => do
    new_ip <- expression.eval system_m nenv addr;
    evaluator.set_ip system_m nenv new_ip
  | (event.branch c addr) => do
    new_ip <- expression.eval system_m nenv addr;
    b      <- expression.eval system_m nenv c;
    when b (evaluator.set_ip system_m nenv new_ip)
  | event.hlt => throw "halt"
  | (event.xchg addr1 addr2) => throw "xchg"
  | event.cpuid => read_cpuid system_m nenv

-- def lhs.read : ∀{tp : type}, lhs tp -> evaluator trace_event (value tp)
--   | ._ (lhs.reg r)       => reg.read r
--   | ._ (lhs.addr a)      => addr.read a
--   | ._ (lhs.arg idx tp)  => do av <- evaluator.arg_at_idx idx, 
--                                   arg_value.to_value av tp
--   | ._ (lhs.streg idx)   => throw "lhs.read: unsupported FP read"

def action.eval : action -> evaluator system_m nenv Unit
  | (action.set l e) => do v <- expression.eval system_m nenv e;
                           lhs.set system_m nenv l v
  | (action.set_cond l c e) => do
    b <- expression.eval system_m nenv c;
    v <- expression.eval system_m nenv e;
    when b (lhs.set system_m nenv l v)
  | (@action.set_aligned (bv _) l e align) => throw "set_aligned: buggy case" -- FIXME: compiler bug
    -- v <- expression.eval os_state nenv e,
    -- if v.to_nat % eval_nat_expr nenv align = 0
    -- then lhs.set os_state nenv l v
    -- else throw "Unaligned set_aligned"
  | (@action.set_aligned _ l e align) => throw "set_aligned: not a bv"
  | (@action.local_def tp idx e) => do 
    v <- expression.eval system_m nenv e;
    modify (fun s => { s with locals := s.locals.insert idx (Sigma.mk tp v)})
  | (action.event e) => event.eval system_m nenv e

-- FIXME: check pattern.context |- environment
def pattern.eval (p : pattern) (e : environment nenv)
    : system_m Unit :=
    evaluator.run' system_m nenv (List.mapM (action.eval system_m nenv) p.actions >>= fun _ => pure ()) e
    -- pure ((fun (v : Unit × evaluator_state nenv) => v.snd.system_state) <$> r)

end with_nat_env

end x86

