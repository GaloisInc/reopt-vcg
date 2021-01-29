-- Evaluates actions in an environment.
import Galois.Data.Bitvec
import Std.Data.RBMap
import X86Semantics.Common
import X86Semantics.BackendAPI

-- import .sexpr

open Std (RBMap RBMap.fromList)


axiom I_am_really_sorry : ∀(P : Prop),  P 

-- FIXME: move
def annotate {ε} {m} [Monad m] [MonadExcept ε m]
  {a} (f : ε -> ε) (c : m a) : m a := tryCatch c (fun e => throw (f e))

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

section with_backend

variables {backend : Backend}

def M (be : Backend) := be.monad

instance Monad_M: Monad (M backend) := backend.Monad_backend
instance MonadExcept_M: MonadExcept String (M backend) := backend.MonadExcept_backend

@[reducible]
def value : type -> Type
  | (bv n) => backend.s_bv n
  | int    => Int -- We support int constants only
  | bit    => backend.s_bool 
  | float fc => backend.s_float fc
  | x86_80  => Unit
  | (vec w tp) => Array /- (eval_nat_expr w) -/ (value tp)
  | (pair tp tp') => value tp × value tp'
  | (fn arg res) => (value arg) -> (value res)

-- def value.repr : ∀{tp : type}, @value backend tp -> String
--   | (bv e), b => repr b
--   | int, v    => repr v
--   | bit, b    => repr b
--   | (float fc), _ => "<float>"
--   | x86_80, _     => "<x86_80>"
--   | (vec w tp), v => "<array>"
--   | (pair tp tp'), (x, y) => "(" ++ value.repr x ++ ", " ++ value.repr y ++ ")"
--   | (fn arg res), _ => "<function>"

-- namespace value

-- def value.repr : ∀{tp : type}, value tp -> String
--   | (bv e) b                => has_repr.repr b
--   | (fn _ _ ) _             => "<function>"
--   | _ _                     => "Unsupported type"

-- instance value_repr {tp : type} : has_repr (value tp) := ⟨value.repr⟩

-- end value

namespace reg

axiom inject_ax0 : 8 + gpreg_type.width gpreg_type.reg8h ≤ 64
axiom inject_ax1 : ∀(rtp : gpreg_type), 0 + gpreg_type.width rtp ≤ 64
axiom avx_inject_ax1 : ∀(rtp : avxreg_type), 0 + avxreg_type.width rtp ≤ 256

def inject : ∀(rtp : gpreg_type), backend.s_bv rtp.width -> backend.s_bv 64 -> backend.s_bv 64
  | gpreg_type.reg32, b, _   => backend.s_uext _ _ b
  | gpreg_type.reg8h, b, old => backend.s_bvsetbits 8 old b -- inject_ax0
  | gpreg_type.reg64, b, _   => b -- special case to keep output compact
  | rtp,              b, old => backend.s_bvsetbits 0 old b -- (inject_ax1 rtp) -- (begin cases rtp; simp end)

def project : ∀(rtp : gpreg_type), backend.s_bv 64 -> backend.s_bv rtp.width
  | gpreg_type.reg8h, b => backend.s_bvgetbits 8 8 b -- inject_ax0 -- (begin simp [gpreg_type.width], exact dec_trivial end)
  | gpreg_type.reg64, b => b -- special case to keep output compact
  | rtp,              b => backend.s_bvgetbits 0 rtp.width b -- (inject_ax1 rtp) -- (begin cases rtp; simp end)

-- FIXME: this depends on the mode, no? SSE instructions inject, while AVX clear upper bits
def avx_inject : ∀(rtp : avxreg_type), backend.s_bv rtp.width -> backend.s_bv 256 -> backend.s_bv 256 
  := fun rtp b old => backend.s_bvsetbits 0 old b -- (avx_inject_ax1 rtp) -- (begin cases rtp; simp end)

def avx_project : ∀(rtp : avxreg_type), backend.s_bv 256 -> backend.s_bv rtp.width
    := fun rtp b =>  backend.s_bvgetbits 0 rtp.width b

end reg

inductive arg_lval
  | reg {} {tp : type}  : concrete_reg tp -> arg_lval 
  | memloc (width : Nat) (addr : backend.machine_word) : arg_lval

-- namespace arg_lval

-- def repr : arg_lval -> String
--   | (reg r)             => r.repr
--   | (memloc width addr) => HasRepr.repr addr ++ "@" ++ HasRepr.repr width

-- instance arg_lval_repr : HasRepr arg_lval := ⟨repr⟩

-- end arg_lval

-- This also needs to be a StateMonad machine_state (it owns that)
-- class SystemM (m : Type -> Type) extends Monad m, MonadState machine_state m, MonadExcept String m :=
--   (os_transition    {} : m Unit )
--   (emit_read_event  {} : machine_word -> ∀(n : Nat), bitvec n -> m Unit)
--   (emit_write_event {}  : machine_word -> ∀(n : Nat), bitvec n -> m Unit)

-- section with_nat_env

-- variables (system_m : Type -> Type) [SystemM system_m]

-- Corresponding to the binder type, more or less.
inductive arg_value 
  -- covers reg, addr, and lhs bindings
  | lval             : @arg_lval backend -> arg_value
  | rval {tp : type} : @value backend tp -> arg_value

-- namespace arg_value

-- def repr : arg_value -> String 
--   | (lval l) => l.repr
--   | (rval v)  => v.repr

-- instance arg_value_repr : has_repr arg_value := ⟨repr⟩

-- end arg_value

@[reducible]
def environment := List (@arg_value backend)

-- machine state is stored in the underlying monad
structure evaluator_state : Type :=
  (environment   : @environment backend) -- read only, but reading can fail
  (locals        : RBMap Nat (Sigma (@value backend)) (fun (n n' : Nat) => decide (n < n')))

namespace evaluator_state

def init : @evaluator_state backend := 
  { environment   := []
  , locals        := {}
  }

end evaluator_state

-- Monad for evaluating with failure.  This nesting might be useful to get the ip where things break?
@[reducible]
def evaluator := StateT (@evaluator_state backend) (ExceptT String (M backend))

-- FIXME: this is repeated from the stdlib, not sure why it needs to be
instance (ε): MonadExcept ε (Except ε) := 
  { throw := fun e => Except.error e, 
    tryCatch := fun m f => match m with | (Except.error e) => f e | _ => m
  }

instance (ε) [Inhabited ε] : Alternative (Except ε) := 
  { failure := Except.error arbitrary
  , orElse  := MonadExcept.orelse }

instance MonadExcept_ExceptT (ε) (m)  [Monad m]: MonadExcept ε (ExceptT ε m) := 
  { throw := fun e => ExceptT.mk (pure (Except.error e))
  , tryCatch := fun m f => ExceptT.mk $ do
                    let v ← m.run
                    match v with
                    | (Except.error e) => (f e).run
                    | _ => ExceptT.mk (pure v)
  }

instance Alternative_ExceptT (ε) (m) [Inhabited ε] [Monad m] : Alternative (ExceptT ε m) := 
  { failure := throw arbitrary
  , orElse  := MonadExcept.orelse
  }


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

namespace value 

def eval_cong {tp tp' : type} (v : @value backend tp)  (pf : tp = tp') : @value backend tp' := 
  have h : @value backend tp = @value backend tp' from congrArg (@value backend) pf
  cast h v

-- This allows us to resolve arith in nat_exprs
def type_check {m} [Monad m] [MonadExcept String m] (tp : type) (v : @value backend tp) (tp' : type)
  : m (@value backend tp') :=
  if H : tp = tp'
  then pure (v.eval_cong H)
  else throw "type_check: arg type mismatch"

end value

-- def system_m.map_machine_state (f : machine_state → machine_state) : system_m system_config.os_state Unit :=
--   modify (fun (s : system_state system_config.os_state) => { s with machine_state := f s.machine_state })

-- section SystemM
-- open SystemM

-- system_m stuff

def M.read_memory_at (addr : backend.machine_word) (n : Nat) : M backend (backend.s_bv n)  := do 
  let w ← backend.read_word addr (n / 8)
  if h : 8 * (n / 8) = n
  then pure (Eq.ndrecOn h w) -- emit_read_event addr n res;
  else throw "read_memory_at: width not a multiple of 8"

-- (store_word (n : Nat) (addr : s_bv 64) (b : s_bv (8 * n)) : monad Unit)

def M.write_memory_at : ∀{tp : type} (addr : backend.machine_word) (bytes : @value backend tp), M backend Unit
  | (bv width), addr, bytes =>
    if H : width = 8 * (width / 8)
    then
      let bytes' : backend.s_bv (8 * (width / 8)) := cast (congrArg backend.s_bv H) bytes 
      backend.store_word (width / 8) addr bytes' -- emit_write_event addr width bytes
    else
      throw "write_memory_at: width not a multiple of 8"
  | _, _, _ => throw "write_memory_at not a bv"

-- end SystemM

namespace evaluator

protected
def run {a : Type} (m : evaluator a) (s : evaluator_state) : M backend (Except String (a × @evaluator_state backend)) :=
  (m.run s).run

def run' {a : Type} (m : evaluator a) (e : environment) : M backend a := do 
  let r ← evaluator.run m { environment := e, locals := {} }
  match r with
  | Except.ok v    => pure v.fst
  | Except.error e => throw e

def run_M {a : Type} (m : M backend a) : @evaluator backend a :=
    monadLift m
    -- adaptState (fun (s : evaluator_state) => (s.system_state, s))
    --          (fun s s' => { s' with system_state := s })
    --          m

def read_memory_at (addr : backend.machine_word) (n : Nat) 
  : @evaluator backend (backend.s_bv n) := evaluator.run_M (M.read_memory_at addr n)

def write_memory_at {tp : type} (addr : backend.machine_word) (bytes : value tp) :
  @evaluator backend Unit :=  evaluator.run_M (M.write_memory_at addr bytes)

def arg_at_idx (idx : Nat) : @evaluator backend (@arg_value backend) := do
  let s ← get
  match s.environment.get? idx with
  | (some a) => pure a
  | none     => throw "evaluator.arg_at_idx: no arg at idx"

-- We should factor out the type check, although it might depend on
-- the functor (value in this case) if we generalise equality
def local_at_idx (idx : Nat) (tp : type) : @evaluator backend (@value backend tp) := do
  let s ← get
  match s.locals.find? idx with
  | (some (Sigma.mk tp' v)) => value.type_check _ v tp
  | none                    => throw "local_at_idx: no arg at idx"

end evaluator

namespace concrete_reg

def set' : ∀{tp : type}, concrete_reg tp -> @value backend tp -> M backend Unit
  | _, (concrete_reg.gpreg idx rtp), b => do
        let w <- backend.get_gpreg idx;
        backend.set_gpreg idx (reg.inject rtp b w) 
  | _, (concrete_reg.flagreg idx),   b => 
        backend.set_flag idx b
  | _, (concrete_reg.avxreg idx rtp), b => do
        let w <- backend.get_avxreg idx;
        backend.set_avxreg idx (reg.avx_inject rtp b w)

def set {tp : type} (r : concrete_reg tp) (v : @value backend tp) : @evaluator backend Unit
  := evaluator.run_M (set' r v)

def cond_set' : ∀{tp : type}, backend.s_bool -> concrete_reg tp -> @value backend tp -> M backend Unit
  | _, c, (concrete_reg.gpreg idx rtp), b => do
          let w <- backend.get_gpreg idx;
          backend.s_cond_set_gpreg c idx (reg.inject rtp b w) 
  | _, c, (concrete_reg.flagreg idx),   b => 
          backend.s_cond_set_flag c idx b
  | _, c, (concrete_reg.avxreg idx rtp), b => do
          let w <- backend.get_avxreg idx;
          backend.s_cond_set_avxreg c idx (reg.avx_inject rtp b w)

def cond_set {tp : type} (c : backend.s_bool) (r : concrete_reg tp) (v : @value backend tp) : @evaluator backend Unit
  := evaluator.run_M (cond_set' c r v)
  
def from_state : ∀{tp : type}, concrete_reg tp -> M backend (@value backend tp)
  | _, (concrete_reg.gpreg idx rtp)  => reg.project rtp <$> backend.get_gpreg idx
  | _, (concrete_reg.flagreg idx)    => backend.get_flag idx
  | _, (concrete_reg.avxreg idx rtp) => reg.avx_project rtp <$> backend.get_avxreg idx

def read {tp : type} (r : concrete_reg tp) : @evaluator backend (@value backend tp) := 
  evaluator.run_M (concrete_reg.from_state r)

end concrete_reg

namespace arg_lval 

def to_value' : @arg_lval backend -> ∀(tp : type), M backend (@value backend tp)
  | (@arg_lval.reg backend tp r), tp' => do 
    let v ← concrete_reg.from_state r;
    value.type_check tp v tp'
  | (arg_lval.memloc width addr), tp' => do
    let w ← M.read_memory_at addr width;
    value.type_check (bv width) w tp'

def to_value (lv : @arg_lval backend) (tp : type) : @evaluator backend (@value backend tp) :=
  evaluator.run_M (to_value' lv tp)

def set_value : @arg_lval backend -> ∀{tp : type}, @value backend tp -> @evaluator backend Unit
  | (@arg_lval.reg _ tp r), tp', v => do
    let v' ← value.type_check _ v tp
    concrete_reg.set r v'
  | (arg_lval.memloc _width addr), tp, v =>
    evaluator.write_memory_at addr v


end arg_lval
-- def read_memory_at (av : arg_value) (n : Nat) : evaluator trace_event (bitvec (8 * n)) :=
--   match av with 
--   | (@arg_value.bv 64 addr) => 
--   | _                      => throw "addr.read: not a 64-bit bitvecor"
--   end

-- Can fail if types mismatch
def arg_value.to_value : @arg_value backend -> ∀(tp : type), @evaluator backend (@value backend tp)
  | (arg_value.lval l), tp => arg_lval.to_value l tp
  | (arg_value.rval v), tp => value.type_check _ v tp

def arg_value.set_value : @arg_value backend -> ∀{tp : type}, @value backend tp -> @evaluator backend Unit
  | (arg_value.lval l), tp, v => arg_lval.set_value l v
  | _, _, _ => throw "arg_value.set_value: not an lvalue"

def addr.read : ∀{tp : type}, addr tp -> @evaluator backend (@value backend tp)
  | tp, (addr.arg _ idx) => do 
    let av ← evaluator.arg_at_idx idx
    arg_value.to_value av tp

def addr.set : ∀{tp : type}, addr tp -> @value backend tp -> @evaluator backend Unit
  | tp, (addr.arg _ idx), v => do 
    let av ← evaluator.arg_at_idx idx -- FIXME: we should really check if this is a memloc first.
    arg_value.set_value av v

-- This is the least-worst option.  The other alternative is to have a
-- value constructor for functions, which we only need here.
inductive hlist.{u,v} {α : Type u} (f : α -> Type v): List α -> Type (max u v)
  | hnil  : hlist f []
  | hcons {xs : List α} (x : α) : f x -> hlist f xs -> hlist f (x :: xs)

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

-- lemma eval_default_2 {e} : nat_expr.eval_default e 2 = 2 := rfl

-- lemma nat_expr_eval_2 : eval_nat_expr 2 = 2 := rfl

namespace type

def has_eq : type -> Prop
  | (bv _)     => True
  | int        => False -- not required
  | bit        => True
  | float _    => True 
  | x86_80     => True
  | (vec _ tp) => has_eq tp 
  | (pair tp tp') => has_eq tp ∧ has_eq tp'
  | (fn _ _)   => False -- could probably come up with something, but nothing efficient

def has_mux : type -> Prop
  | (bv _)     => True
  | int        => False -- not needed
  | bit        => True
  | float _    => True 
  | x86_80     => True
  | (vec _ tp) => has_mux tp 
  | (pair tp tp') => has_mux tp ∧ has_mux tp'
  | (fn _ _)   => False -- could probably come up with something, but nothing efficient

@[reducible]
def has_eq_dec : ∀(tp : type), Decidable (has_eq tp) 
  | (bv _)     => isTrue True.intro
  | int        => isFalse notFalse
  | bit        => isTrue True.intro  
  | float _    => isTrue True.intro  
  | x86_80     => isTrue True.intro  
  | (vec _ tp) => has_eq_dec tp
  | (pair tp tp') =>
    have hL : Decidable (has_eq tp)  from has_eq_dec tp
    have hR : Decidable (has_eq tp') from has_eq_dec tp'
    have h  : Decidable (has_eq tp ∧ has_eq tp') from inferInstance
    h
  | (fn _ _)   => isFalse notFalse

@[reducible]
def has_mux_dec : ∀(tp : type), Decidable (has_mux tp) 
  | (bv _)     => isTrue True.intro
  | int        => isFalse notFalse
  | bit        => isTrue True.intro  
  | float _    => isTrue True.intro  
  | x86_80     => isTrue True.intro  
  | (vec _ tp) => has_mux_dec tp
  | (pair tp tp') =>
    have hL : Decidable (has_mux tp)  from has_mux_dec tp
    have hR : Decidable (has_mux tp') from has_mux_dec tp'
    have h  : Decidable (has_mux tp ∧ has_mux tp') from inferInstance
    h
  | (fn _ _)   => isFalse notFalse

instance decidable_pred_type_has_eq  :  DecidablePred has_eq := has_eq_dec
instance decidable_pred_type_has_mux :  DecidablePred has_mux := has_mux_dec

end type

namespace value

def partial_eq : ∀{tp : type}, type.has_eq tp -> @value backend tp -> @value backend tp -> backend.s_bool
  | (bv _), _, v1, v2      => backend.s_bveq v1 v2
  | bit,    _, v1, v2      => backend.s_bool_eq v1 v2
  | float _,  _, v1, v2    => backend.true
  | x86_80,  _, v1, v2     => backend.true
  | (vec _ tp), pf, v1, v2 => 
     let pf' : type.has_eq tp := pf;
     let bs  := List.zipWith (partial_eq pf') (Array.toList v1) (Array.toList v2); -- ).all (fun (v : (value tp × value tp)) => value.partial_eq pf' v.fst v.snd)
     List.foldr backend.s_and (backend.true) bs
  | (pair tp tp'), pf, v1, v2 => 
     backend.s_and (partial_eq pf.left v1.fst v2.fst) (partial_eq pf.right v1.snd v2.snd)

def mux (b : backend.s_bool) : ∀{tp : type}, type.has_mux tp 
  -> @value backend tp -> @value backend tp -> @value backend tp
  | (bv _), _, v1, v2      => backend.s_mux_bv   b v1 v2
  | bit,    _, v1, v2      => backend.s_mux_bool b v1 v2
  | float _,  _, v1, v2    => backend.s_mux_float b v1 v2
  | x86_80,  _, v1, v2      => ()
  -- This is very inefficient, maybe make Arrays part of backend?  This type is mainly for AVX etc.
  | (vec _ tp), pf, v1, v2 => 
     let pf' : type.has_mux tp := pf;
     let bs  := List.zipWith (mux b pf') (Array.toList v1) (Array.toList v2); -- ).all (fun (v : (value tp × value tp)) => value.partial_eq pf' v.fst v.snd)
     bs.toArray
  | (pair tp tp'), pf, v1, v2 => (mux b pf.left v1.fst v2.fst, mux b pf.right v1.snd v2.snd)

end value

def prim.eval : ∀{tp : type}, prim tp -> @evaluator backend (@value backend tp)
  -- `(eq tp)` returns `true` if two values are equal.
  | _, (prim.eq tp) => 
    if pf : type.has_eq tp 
    then pure (value.partial_eq pf)
    else throw "prim.eval.eq: eq at unsupported type"
  -- `(neq tp)` returns `true` if two values are not equal.
  | _, (prim.neq tp) => 
    if pf : type.has_eq tp 
    then pure (fun v1 v2 => backend.s_not (value.partial_eq pf v1 v2))
    else throw "prim.eval.neq: neq at unsupported type"
  -- `(mux tp) c t f` evaluates to `t` when `c` is true and `f` otherwise.
  -- This only evaluates `t` when `c` is true, and only evaluates `f` when
  -- `c` is false.
  | _, (prim.mux tp) => 
    if pf : type.has_mux tp
    then pure (fun bv v1 v2 => value.mux bv pf v1 v2)
    else throw "prim.eval.mux: mux at unsupported type"
  -- `zero` is the zero bit
  | _, prim.bit_zero => pure backend.false
  -- `one` is the one bit
  | _, prim.bit_one => pure backend.true

  | _, prim.bit_or  => pure backend.s_or
  | _, prim.bit_and => pure backend.s_and
  | _, prim.bit_xor => pure backend.s_xor

  -- `bvnat` constructs a bit vector from a natural number.
  | _, (prim.bv_nat w n)    => pure (backend.s_bv_imm w n)
  | _, (prim.bv_int_sext w) => pure (backend.s_bv_imm_int w)

  -- `(add i)` returns the sum of two i-bit numbers.
  | _, (prim.add i)        => pure (backend.s_bvadd i)
  -- `(adc i)` returns the sum of two i-bit numbers and a carry bit.
  | _, (prim.adc i)         => pure (fun x y b => 
        backend.s_bvadd _ x (backend.s_bvadd _ y (backend.bit_to_bitvec _ b)))
  | _, (prim.uadc_overflows i) => pure (fun x y b => 
        backend.s_bvult (backend.s_bvadd _ x (backend.s_bvadd _ y (backend.bit_to_bitvec _ b))) x)
  | _, (prim.sadc_overflows i) => pure (fun x y b => 
        backend.s_bvslt (backend.s_bvadd _ x (backend.s_bvadd _ y (backend.bit_to_bitvec _ b))) x)
  -- `(bvsub i)` substracts two i-bit bitvectors.
  | _, (prim.sub i) => pure (backend.s_bvsub i)
  -- `(ssbb_overflows i)` true if signed sub overflows, the bit
  -- is a borrow bit.
  -- FIXME: is this correct?
  | _, (prim.ssbb_overflows i) => pure (fun x y b =>
        backend.s_bvslt (backend.s_bvsub _ (backend.s_bvsub _ x y) (backend.bit_to_bitvec _ b)) x)
  -- `(usbb_overflows i)` true if unsigned sub overflows,
  -- the bit is a borrow bit.
  | _, (prim.usbb_overflows i) => pure (fun x y b =>
        backend.s_bvult (backend.s_bvsub _ x (backend.bit_to_bitvec _ b)) y)
  -- `(neg tp)` Two's Complement negation.
  | _, (prim.neg i) => pure (backend.s_bvneg i)

  -- `(mul i)` returns the product of two i-bit numbers.
  | _, (prim.mul i)            => pure (backend.s_bvmul i)

  -- `(quotRem i) n d` returns a pair `(q,r)` where `q` is a `floor (n/d)`
  -- and `r` is `n - d * floor (n/d)`.
  -- `n` and `d` are treated as unsigned values.
  -- If `d = 0` or `floor(n/d) >= 2^n`, then this triggers a #DE exception.
  | _, (prim.quotRem i) => throw "prim.eval.quotRem unimplemented"

  -- `(squotRem i) n d` returns a pair `(q,r)` where `q` is a `trunc (n/d)`
  -- and `r` is `n - d * trunc (n/d)`.  `trunc` always round to zero.
  -- `n` and `d` are treated as signed values.
  -- If `d = 0`, `trunc(n/d) >= 2^(n-1)` or `trunc(n/d) < -2^(n-1), then this
  -- triggers a #DE exception when evaluated.
  | _, (prim.squotRem i) => throw "prim.eval.squotRem unimplemented"

  | _, (prim.ule i) => pure (fun x y => backend.s_not (backend.s_bvult y x))
  | _, (prim.ult i) => pure (fun x y => backend.s_bvult x y)
  | _, (prim.sle i) => pure (fun x y => backend.s_not (backend.s_bvslt y x))
  | _, (prim.slt i) => pure (fun x y => backend.s_bvslt x y)

  -- `(slice w u l)` takes bits `u` through `l` out of a `w`-bit number.
  --  prim (bv w .→ bv (u+1-l))
  | _, (prim.slice w u l) => pure (fun v => backend.s_bvextract w u l v)
       -- let n := u + 1 - l;
       -- H <- annotate' "slice" (assert (w = w - n + n));
       -- let f : bitvec w → bitvec n := (bitvec.slice u l (w - n) H.default);
       -- pure f
  -- `(sext i o)` sign extends an `i`-bit number to a `o`-bit number.
  | _, (prim.sext i o) => do -- H <- annotate' "sext" (assert (i ≤ o));
                             pure (backend.s_sext i o)
  -- `(uext i o)` unsigned extension of an `i`-bit number to a `o`-bit number.
  | _, (prim.uext i o) => do -- H <- annotate' "uext" (assert (i ≤ o));
                             pure (backend.s_uext i o)
  -- `(trunc i o)` truncates an `i`-bit number to a `o`-bit number.
  | _, (prim.trunc i o) => do -- H <- annotate' "trunc" (assert (o ≤ i));
                               pure (backend.s_trunc i o)

  | _, (prim.cat i j) => pure (fun x y =>  (backend.s_bvappend x y))
  --(begin simp [eval_nat_expr, nat_expr.eval_default_mul_eq, nat_expr.eval, eval_default_2, two_mul], 
  --end)

  -- | bv_least_nibble (i:Nat) : prim (bv i .→ bv 4)
  | _, (prim.msb i)    => pure (backend.s_bvmsb i)
  | _, (prim.bv_and i) => pure (backend.s_bvand i)
  | _, (prim.bv_or i)  => pure (backend.s_bvor i)
  | _, (prim.bv_xor i) => pure (backend.s_bvxor i)
  | _, (prim.bv_complement i) => pure (backend.s_bvnot i)
  | _, (prim.shl i j)    => pure (fun x (y : backend.s_bv j) => 
        backend.s_bvshl _ x (backend.s_uext _ _ y))
   --- `(shr i) x y` shifts the bits in `x` to the right by
   --- `y` bits where `y` is treated as an unsigned integer.
   --- The new bits shifted in from the right are all zero.
   | _, (prim.shr i j) => pure (fun x (y : backend.s_bv j) => 
        backend.s_bvlshr x (backend.s_uext _ _ y))
   --- `(sar i) x y` arithmetically shifts the bits in `x` to
   --- the left by `y` bits where `y` is treated as an unsigned integer.
   --- The new bits shifted in all match the most-significant bit in y.
   | _, (prim.sar i j) => pure (fun x (y : backend.s_bv j) => 
        backend.s_bvsshr x (backend.s_uext _ _ y))
   
  | _, (prim.even_parity i) => pure (fun b => backend.s_not (backend.s_parity b))
  -- `(bsf i)` returns the index of least-significant bit that is 1.
  | _, (prim.bsf i)         => throw "prim.eval.bsf unimplemented"
  -- `(bsr i)` returns the index of most-significant bit that is 1.
  | _, (prim.bsr i)         => throw "prim.eval.bsr unimplemented"
  -- `(bswap i)` reverses the bytes in the bitvector.
  | _, (prim.bswap i)       => throw "prim.eval.bswap unimplemented"
  -- `(btc w j) base idx` interprets base as bitvector and returns
  -- a bitvector contains the same bits as `base` except the `i`th bit
  -- (where 0 denotes the least-significant bit) is complemented.
  -- The value `i` is `idx` as a unsigned integer modulo `w`.
  | _, (prim.btc w j)         => throw "prim.eval.btc unimplemented"
  -- `(btr w j) base idx` interprets base as bitvector and returns
  -- a bitvector contains the same bits as `base` except the `i`th bit
  -- (where 0 denotes the least-significant bit) is cleared.
  -- The value `i` is `idx` as a unsigned integer modulo `w`.
  | _, (prim.btr w j)         => throw "prim.eval.btr unimplemented"
  -- `(bts w j) base idx` interprets base as bitvector and returns
  -- a bitvector contains the same bits as `base` except the `i`th bit
  -- (where 0 denotes the least-significant bit) is set.
  -- The value `i` is `idx` as a unsigned integer modulo `w`.
  | _, (prim.bts w j)         => throw "prim.eval.bts unimplemented"

  | _, prim.bv_bitcast_to_fp fc => 
       pure (backend.s_bv_bitcast_to_fp fc)
  | _, prim.fp_bitcast_to_bv fc => pure (backend.s_fp_bitcast_to_bv fc )
  | _, prim.fp_add fc           => pure (backend.s_fp_add fc           )
  | _, prim.fp_sub fc           => pure (backend.s_fp_sub fc           )
  | _, prim.fp_mul fc           => pure (backend.s_fp_mul fc           ) 
  | _, prim.fp_div fc           => pure (backend.s_fp_div fc           ) 
  | _, prim.fp_sqrt fc          => pure (backend.s_fp_sqrt fc          ) 
  | _, prim.fp_ordered fc       => pure (backend.s_fp_ordered fc       ) 
  | _, prim.fp_min fc           => pure (backend.s_fp_min fc           ) 
  | _, prim.fp_max fc           => pure (backend.s_fp_max fc           ) 
  | _, prim.fp_lt  fc           => pure (backend.s_fp_lt  fc           ) 
  | _, prim.fp_le  fc           => pure (backend.s_fp_le  fc           ) 
  | _, prim.int_convert_to_fp fc n => 
       if H : 32 = n
       then pure (cast (congrArg (fun m => value (bv m .→ float fc)) H) 
                       (backend.s_int_convert_to_fp fc true))
       else if H' : 64 = n
            then pure (cast (congrArg (fun m => value (bv m .→ float fc)) H') 
                       (backend.s_int_convert_to_fp fc false))
            else throw "int_convert_to_fp: expecting 32 or 64 bit size"

  | _, prim.fp_convert_to_int fc n rm =>
       if H : 32 = n
       then pure (cast (congrArg (fun m => value (float fc .→ bv m)) H) 
                       (backend.s_fp_convert_to_int fc true rm))
       else if H' : 64 = n
            then pure (cast (congrArg (fun m => value (float fc .→ bv m)) H') 
                       (backend.s_fp_convert_to_int fc false rm))
            else throw "int_convert_to_fp: expecting 32 or 64 bit size"

  | _, prim.fp_convert_to_fp sfc dfc rm  => pure (backend.s_fp_convert_to_fp sfc dfc rm)
  | _, prim.fp_literal fc m esign e => pure (backend.s_fp_literal fc m esign e)

  -- `bv_to_x86_80` converts a bitvector to an extended precision number (lossless)
  | _, (prim.bv_to_x86_80 w)  => throw "prim.eval.bv_to_x86_80 unimplemented"
  -- `float_to_x86_80` converts a float to an extended precision number (lossless)
  | _, prim.float_to_x86_80   => throw "prim.eval.float_to_x86_80 unimplemented"
  -- `double_to_x86_80` converts a double to an extended precision number (lossless)
  | _, prim.double_to_x86_80   => throw "prim.eval.double_to_x86_80 unimplemented"
  -- `x87_fadd` adds two extended precision values using the flags in the x87 register.
  | _, prim.x87_fadd           => throw "prim.eval.dx87_fadd unimplemented"

  -- Return first element of a pair
  | _, (prim.pair_fst x y) => pure (fun (v : value x × value y) => v.fst)
  -- Return second element of a pair.
  | _, (prim.pair_snd x y) => pure (fun (v : value x × value y) => v.snd)

-- FIXME: move into the backend?
def value.make_undef : ∀(tp : type), @value backend tp 
  | (bv e) => backend.s_bv_imm e 0
  | bit    => backend.false
  | int    => Int.ofNat 0
  | float fc => backend.s_fp_literal fc 0 false 0
  | x86_80  => ()
  | (vec w tp) => mkArray w (make_undef tp)
  | (pair tp tp') => (make_undef tp, make_undef tp')
  | (fn arg res) => fun _ => make_undef res

def expression.eval : ∀{tp : type}, expression tp -> @evaluator backend (@value backend tp)
  | _, (expression.primitive p) => prim.eval p
  | _, (@expression.bit_test wr wi re idxe) => do
    let r   ← eval re
    let idx ← eval idxe
    pure (backend.s_bit_test r idx)
  | _, (expression.mulc m xe) => do
    let x ← eval xe
    pure (backend.s_bvmul _ (backend.s_bv_imm 64 m) x)
  | _, (expression.quotc m xe) => throw "eval.quotc unimplemented"
  | _, (expression.undef tp)   => pure (value.make_undef tp)
  | _, (expression.app f a) => (eval f) <*> (eval a)
  | _, (expression.get_reg r) => concrete_reg.read r
  | _, expression.get_rip     => evaluator.run_M (backend.s_get_ip)
  | _, (expression.read tp addre) => do
    let addr   <- eval addre;
    (match tp with
      | (bv we) => evaluator.read_memory_at addr we
      | _ => throw "eval.read Trying to store non-bitvector")

  | _, (expression.streg idx) => throw "eval.streg unimplemented"
  | _, (expression.get_local idx tp) => evaluator.local_at_idx idx tp
  -- This is overly general, we might not know that av here is an rval
  | _, (expression.imm_arg idx tp) => do
    let av ← evaluator.arg_at_idx idx
    match av with
    | (arg_value.rval v) => value.type_check _ v tp
    | _ => throw "eval.imm_arg Not an rval"

  | _, (expression.addr_arg idx) => do
    let av ← evaluator.arg_at_idx idx
    match av with
    | (arg_value.lval (arg_lval.memloc _ addr)) => pure addr
    | _ => throw "eval.addr_arg Not an memloc lval"
  -- FIXME: isn't specific to arg_lval
  | _, (expression.read_arg idx tp) => do
    let av ← evaluator.arg_at_idx idx
    arg_value.to_value av tp

def lhs.set : ∀{tp : type}, lhs tp -> @value backend tp -> @evaluator backend Unit
  | _, (lhs.set_reg r), v        => concrete_reg.set r v
  | _, (lhs.write_addr ae tp), v => do
    let a ← expression.eval ae
    evaluator.write_memory_at a v
  | _, (lhs.write_arg idx _tp), v => do
    let av ← evaluator.arg_at_idx idx
    -- fixme: we ignore tp here?
    arg_value.set_value av v
  | _, (lhs.streg idx), v  => throw "lhs.set: unsupported FP write"

def lhs.read : ∀{tp : type}, lhs tp -> @evaluator backend (@value backend tp)
  | _, (lhs.set_reg r)        => concrete_reg.read r
  | _, (lhs.write_addr ae tp) => do
    let addr ← expression.eval ae
    match tp with
    | (bv we) => evaluator.read_memory_at addr we
    | _ => throw "lhs.read Trying to store non-bitvector"
  | _, (lhs.write_arg idx tp) => do
    let av ← evaluator.arg_at_idx idx;
    -- fixme: we ignore tp here?
    arg_value.to_value av tp
  | _, (lhs.streg idx) => throw "lhs.set: unsupported FP write"

def evaluator.push64 (v : value (bv 64)) : @evaluator backend Unit := do
  let sp ← lhs.read rsp
  let sp' := backend.s_bvsub _ sp (backend.s_bv_imm _ 8)
  lhs.set rsp sp'
  evaluator.write_memory_at sp' v

-- def read_cpuid : @evaluator backend Unit :=
--   -- Copied from the cpuid results from my macbook
--   -- Note: CPUID is allowed to return 0s 
--   let cpuid_values : RBMap Nat (Nat × Nat × Nat × Nat) (fun x y => decide (x < y)) :=
--     RBMap.fromList [ (0, (0xd, 0x756e6547, 0x6c65746e, 0x49656e69))
--                     , (1, (0x40661, 0x2100800, 0x7ffafbff, 0xbfebfbff))
--                     , (2, (0x76036301, 0xf0b5ff, 0x0, 0xc10000))
--                     , (3, (0x0, 0x0, 0x0, 0x0))
--                     , (4, (0x1c004121, 0x1c0003f, 0x3f, 0x0))
--                     , (5, (0x40, 0x40, 0x3, 0x42120))
--                     , (6, (0x77, 0x2, 0x9, 0x0))
--                     , (7, (0x0, 0x27ab, 0x0, 0x9c000000))
--                     , (8, (0x0, 0x0, 0x0, 0x0))
--                     , (9, (0x0, 0x0, 0x0, 0x0))
--                     , (10, (0x7300403, 0x0, 0x0, 0x603))
--                     , (11, (0x1, 0x2, 0x100, 0x6))
--                     , (12, (0x0, 0x0, 0x0, 0x0))
--                     , (13, (0x7, 0x340, 0x340, 0x0))
--                     , (2147483648, (0x80000008, 0x0, 0x0, 0x0))
--                     , (2147483649, (0x0, 0x0, 0x21, 0x2c100800))
--                     , (2147483650, (0x65746e49, 0x2952286c, 0x726f4320, 0x4d542865))
--                     , (2147483651, (0x37692029, 0x3839342d, 0x20514830, 0x20555043))
--                     , (2147483652, (0x2e322040, 0x48473038, 0x7a, 0x0))
--                     , (2147483653, (0x0, 0x0, 0x0, 0x0))
--                     , (2147483654, (0x0, 0x0, 0x1006040, 0x0))
--                     , (2147483655, (0x0, 0x0, 0x0, 0x100))
--                     , (2147483656, (0x3027, 0x0, 0x0, 0x0))
--                     ] (fun x y => decide (x < y)); -- FIXME: we need to look at rcx sometimes as well
--     let cpuid_fn (n : Nat) : (Nat × Nat × Nat × Nat) :=
--       match cpuid_values.find? n with
--       | none     => (0, 0, 0, 0)
--       | (some r) => r;
--     do 
--       raxv <- lhs.read rax;
--       match cpuid_fn raxv.to_nat with 
--       | (axv, bxv, cxv, dxv) => do 
--         lhs.set eax (backend.s_bv 32 axv);
--         lhs.set ebx (backend.s_bv 32 bxv);
--         lhs.set ecx (backend.s_bv 32 cxv);
--         lhs.set edx (backend.s_bv 32 dxv) 

def event.eval : event -> @evaluator backend Unit
  | event.syscall => evaluator.run_M backend.s_os_transition
    -- adaptState (fun (s : evaluator_state) => (s.system_state, s))
    --            (fun s s' => { s' with system_state := s })
    --            (system_m.os_transition)
  | (event.unsupported msg) => throw ("event.eval: unsupported: " ++ msg)
  | event.pop_x87_register_stack => throw "pop_x87_register_stack"
  | (event.call addr) => do
    let new_ip ← expression.eval addr
    let old_ip ← evaluator.run_M backend.s_get_ip
    evaluator.push64 old_ip
    evaluator.run_M (backend.s_set_ip new_ip)

  | (event.jmp addr) => do
    let new_ip ← expression.eval addr
    evaluator.run_M (backend.s_set_ip new_ip)
  | (event.branch c addr) => do
    let new_ip ← expression.eval addr
    let b      ← expression.eval c;
    evaluator.run_M (backend.s_cond_set_ip b new_ip)
  | event.hlt => throw "halt"
  | (event.xchg addr1 addr2) => throw "xchg"
  | event.cpuid => evaluator.run_M backend.s_read_cpuid

def action.eval : action -> @evaluator backend Unit
  | (action.set l e) => do
    let v ← expression.eval e
    lhs.set l v
  | (@action.set_cond tp r c e) => do
    let b ← expression.eval c
    let v ← expression.eval e
    match r with
    | reg.concrete r' => concrete_reg.cond_set b r' v
    | reg.arg idx => do
      let av ← evaluator.arg_at_idx idx
      match av with 
      | arg_value.lval (@arg_lval.reg _ tp' r') => 
        if H : tp = tp'
        then concrete_reg.cond_set b r' (cast (congrArg _ H) v)
        else throw "BUG: type mismatch in set_cond"
      | _ => throw "BUG: non-reg destination in set_cond"
    

  | (@action.set_aligned (bv _) l e align) => throw "set_aligned: buggy case" -- FIXME: compiler bug
    -- v <- expression.eval os_state e,
    -- if v.to_nat % eval_nat_expr align = 0
    -- then lhs.set os_state l v
    -- else throw "Unaligned set_aligned"
  | (@action.set_aligned _ l e align) => throw "set_aligned: not a bv"
  | (@action.local_def tp idx e) => do 
    let v ← expression.eval e
    modify (fun s => { s with locals := s.locals.insert idx (Sigma.mk tp v)})
  | (action.event e) => event.eval e

-- FIXME: check pattern.context |- environment
def pattern.eval (p : pattern) (e : environment) : M backend Unit :=
    evaluator.run' (discard (List.mapM action.eval p.actions)) e
    -- pure ((fun (v : Unit × evaluator_state) => v.snd.system_state) <$> r)

end with_backend

end x86

