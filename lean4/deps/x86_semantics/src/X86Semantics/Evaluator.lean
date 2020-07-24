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

section with_backend

variables {backend : Backend}

def M (be : Backend) := be.monad

instance Monad_M: Monad (M backend) := backend.Monad_backend
instance MonadExcept_M: MonadExcept String (M backend) := backend.MonadExcept_backend

@[reducible]
def value : type -> Type
  | (bv n) => backend.s_bv n
  | bit    => backend.s_bool 
  | float  => Unit -- FIXME
  | double => Unit -- FIXME
  | x86_80 => Unit -- FIXME  
  | (vec w tp) => Array /- (eval_nat_expr w) -/ (value tp)
  | (pair tp tp') => value tp × value tp'
  | (fn arg res) => (value arg) -> (value res)

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

def inject : ∀(rtp : gpreg_type), backend.s_bv rtp.width -> backend.s_bv 64 -> backend.s_bv 64
  | gpreg_type.reg32, b, _   => backend.s_uext _ _ b
  | gpreg_type.reg8h, b, old => backend.s_bvsetbits 8 old b -- inject_ax0
  | gpreg_type.reg64, b, _   => b -- special case to keep output compact
  | rtp,              b, old => backend.s_bvsetbits 0 old b -- (inject_ax1 rtp) -- (begin cases rtp; simp end)

def project : ∀(rtp : gpreg_type), backend.s_bv 64 -> backend.s_bv rtp.width
  | gpreg_type.reg8h, b => backend.s_bvgetbits 8 8 b -- inject_ax0 -- (begin simp [gpreg_type.width], exact dec_trivial end)
  | gpreg_type.reg64, b => b -- special case to keep output compact
  | rtp,              b => backend.s_bvgetbits 0 rtp.width b -- (inject_ax1 rtp) -- (begin cases rtp; simp end)

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

namespace value 

def eval_cong {tp tp' : type} (v : @value backend tp)  (pf : tp = tp') 
  : @value backend tp' := Eq.recOn pf v

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

def M.read_memory_at (addr : backend.machine_word) (n : Nat) : M backend (backend.s_bv n) 
  := do w <- backend.read_word addr (n / 8);
        if H : 8 * (n / 8) = n
        then pure (Eq.ndrecOn H w) -- emit_read_event addr n res;
        else throw "read_memory_at: width not a multiple of 8"

def M.write_memory_at : ∀{tp : type} (addr : backend.machine_word) 
  (bytes : @value backend tp), M backend Unit
  | (bv width), addr, bytes =>
    (if H : width = 8 * (width / 8)
     then backend.store_word (width / 8) addr (Eq.ndrecOn H bytes) -- emit_write_event addr width bytes
     else throw "write_memory_at: width not a multiple of 8")
  | _, _, _ => throw "write_memory_at not a bv"

-- end SystemM

namespace evaluator
def run {a : Type} (m : evaluator a) (s : evaluator_state) 
        : M backend (Except String (a × @evaluator_state backend)) :=
    (m.run s).run

def run' {a : Type} (m : evaluator a) (e : environment) : M backend a :=
  do r <- m.run { environment := e, locals := {} };
     match r with
     | Except.ok v    => pure v.fst
     | Except.error e => throw e

def run_M {a : Type} (m : M backend a) : @evaluator backend a :=
    monadLift m
    -- adaptState (fun (s : evaluator_state) => (s.system_state, s))
    --          (fun s s' => { s' with system_state := s })
    --          m

-- This throws away any evaluator state updates, and turns exceptions into backend exceptions
def mux_m (b : backend.s_bool)
          (m1 : @evaluator backend Unit) 
          (m2 : @evaluator backend Unit)
          : @evaluator backend Unit := do
    s <- get;
    let tunnel (m : @evaluator backend Unit) : M backend Unit :=
      (do r <- (m.run s : M backend (Except String (Unit × @evaluator_state backend)));
         match r with
         | Except.ok v    => pure ()
         | Except.error e => throw e);
     run_M (backend.s_mux_m b (tunnel m1) (tunnel m2))

-- def evaluator.map_machine_state (f : machine_state → machine_state) : evaluator system_m Unit :=
--     monadLift (modify f : system_m Unit)

-- def evaluator.with_machine_state {a : Type} (f : machine_state → a) : evaluator system_m a :=
--     monadLift (f <$> (get : system_m machine_state))

def read_memory_at (addr : backend.machine_word) (n : Nat) 
  : @evaluator backend (backend.s_bv n) := evaluator.run_M (M.read_memory_at addr n)

def write_memory_at {tp : type} (addr : backend.machine_word) (bytes : value tp) :
  @evaluator backend Unit :=  evaluator.run_M (M.write_memory_at addr bytes)

def arg_at_idx (idx : Nat) : @evaluator backend (@arg_value backend) :=
  do s <- get;
     match s.environment.get? idx with
       | (some a) => pure a
       | none     => throw "evaluator.arg_at_idx: no arg at idx"

-- We should factor out the type check, although it might depend on
-- the functor (value in this case) if we generalise equality
def local_at_idx (idx : Nat) (tp : type) : @evaluator backend (@value backend tp) :=
  do s <- get;
     (match s.locals.find? idx with
     | (some (Sigma.mk tp' v)) => value.type_check _ v tp
     | none                    => throw "local_at_idx: no arg at idx")

end evaluator

namespace concrete_reg

def set' : ∀{tp : type}, concrete_reg tp -> @value backend tp -> M backend Unit
  | ._, (concrete_reg.gpreg idx rtp), b => do
        w <- backend.get_gpreg idx;
        backend.set_gpreg idx (reg.inject rtp b w) 
  | ._, (concrete_reg.flagreg idx),   b => 
        backend.set_flag idx b

def set {tp : type} (r : concrete_reg tp) (v : @value backend tp) : @evaluator backend Unit
  := evaluator.run_M (set' r v)
  
def from_state : ∀{tp : type}, concrete_reg tp -> M backend (@value backend tp)
  | _, (concrete_reg.gpreg idx rtp) => reg.project rtp <$> backend.get_gpreg idx
  | _, (concrete_reg.flagreg idx)   => backend.get_flag idx

def read {tp : type} (r : concrete_reg tp) : @evaluator backend (@value backend tp) := 
  evaluator.run_M (concrete_reg.from_state r)

end concrete_reg

namespace arg_lval 

def to_value' : @arg_lval backend -> ∀(tp : type), M backend (@value backend tp)
  | (@arg_lval.reg backend tp r), tp' => do 
    v <- concrete_reg.from_state r;
    value.type_check tp v tp'
  | (arg_lval.memloc width addr), tp' => do
    w <- M.read_memory_at addr width;
    value.type_check (bv width) w tp'

def to_value (lv : @arg_lval backend) (tp : type) : @evaluator backend (@value backend tp)
  := evaluator.run_M (to_value' lv tp)

def set_value : @arg_lval backend -> ∀{tp : type}, @value backend tp 
  -> @evaluator backend Unit
  | (@arg_lval.reg _ tp r), tp', v => do v' <- value.type_check _ v tp;
                                         concrete_reg.set r v'
  | (arg_lval.memloc _width addr), tp, v => evaluator.write_memory_at addr v


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
      av <- evaluator.arg_at_idx idx;
      arg_value.to_value av tp

def addr.set : ∀{tp : type}, addr tp -> @value backend tp -> @evaluator backend Unit
  | tp, (addr.arg _ idx), v => do 
      av <- evaluator.arg_at_idx idx; -- FIXME: we should really check if this is a memloc first.
      arg_value.set_value av v

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

-- lemma eval_default_2 {e} : nat_expr.eval_default e 2 = 2 := rfl

-- lemma nat_expr_eval_2 : eval_nat_expr 2 = 2 := rfl

namespace type

def has_eq : type -> Prop
  | (bv _)     => True
  | bit        => True
  | float      => True 
  | double     => True 
  | x86_80     => True
  | (vec _ tp) => has_eq tp 
  | (pair tp tp') => has_eq tp ∧ has_eq tp'
  | (fn _ _)   => False -- could probably come up with something, but nothing efficient

def has_mux : type -> Prop
  | (bv _)     => True
  | bit        => True
  | float      => True 
  | double     => True 
  | x86_80     => True
  | (vec _ tp) => has_mux tp 
  | (pair tp tp') => has_mux tp ∧ has_mux tp'
  | (fn _ _)   => False -- could probably come up with something, but nothing efficient

@[reducible]
def has_eq_dec : ∀(tp : type), Decidable (has_eq tp) 
  | (bv _)     => isTrue True.intro
  | bit        => isTrue True.intro  
  | float      => isTrue True.intro  
  | double     => isTrue True.intro  
  | x86_80     => isTrue True.intro  
  | (vec _ tp) => has_eq_dec tp
  | (pair tp tp') => @And.Decidable _ _ (has_eq_dec tp) (has_eq_dec tp')
  | (fn _ _)   => isFalse notFalse

@[reducible]
def has_mux_dec : ∀(tp : type), Decidable (has_mux tp) 
  | (bv _)     => isTrue True.intro
  | bit        => isTrue True.intro  
  | float      => isTrue True.intro  
  | double     => isTrue True.intro  
  | x86_80     => isTrue True.intro  
  | (vec _ tp) => has_mux_dec tp
  | (pair tp tp') => @And.Decidable _ _ (has_mux_dec tp) (has_mux_dec tp')
  | (fn _ _)   => isFalse notFalse

instance decidable_pred_type_has_eq:  DecidablePred has_eq := has_eq_dec
instance decidable_pred_type_has_mux: DecidablePred has_mux := has_mux_dec

end type

namespace value

def partial_eq : ∀{tp : type}, type.has_eq tp -> @value backend tp -> @value backend tp
  -> backend.s_bool
  | (bv _), _, v1, v2      => backend.s_bveq v1 v2
  | bit,    _, v1, v2      => backend.s_bool_eq v1 v2
  | float,  _, v1, v2      => backend.s_bool_imm true
  | double, _, v1, v2      => backend.s_bool_imm true
  | x86_80, _, v1, v2      => backend.s_bool_imm true
  | (vec _ tp), pf, v1, v2 => 
     let pf' : type.has_eq tp := pf;
     let bs  := List.zipWith (partial_eq pf') (Array.toList v1) (Array.toList v2); -- ).all (fun (v : (value tp × value tp)) => value.partial_eq pf' v.fst v.snd)
     List.foldr backend.s_and (backend.s_bool_imm true) bs
  | (pair tp tp'), pf, v1, v2 => 
     backend.s_and (partial_eq pf.left v1.fst v2.fst) (partial_eq pf.right v1.snd v2.snd)

def mux (b : backend.s_bool) : ∀{tp : type}, type.has_mux tp 
  -> @value backend tp -> @value backend tp -> @value backend tp
  | (bv _), _, v1, v2      => backend.s_mux_bv   b v1 v2
  | bit,    _, v1, v2      => backend.s_mux_bool b v1 v2
  | float,  _, v1, v2      => ()
  | double, _, v1, v2      => ()
  | x86_80, _, v1, v2      => ()
  -- This is very inefficient, maybe make Arrays part of backend?  This type is mainly for AVX etc.
  | (vec _ tp), pf, v1, v2 => 
     let pf' : type.has_mux tp := pf;
     let bs  := List.zipWith (mux pf') (Array.toList v1) (Array.toList v2); -- ).all (fun (v : (value tp × value tp)) => value.partial_eq pf' v.fst v.snd)
     bs.toArray
  | (pair tp tp'), pf, v1, v2 => (mux pf.left v1.fst v2.fst, mux pf.right v1.snd v2.snd)

end value

def prim.eval : ∀{tp : type}, prim tp -> @evaluator backend (@value backend tp)
  -- `(eq tp)` returns `true` if two values are equal.
  | ._, (prim.eq tp) => 
    if pf : type.has_eq tp 
    then pure (value.partial_eq pf)
    else throw "prim.eval.eq: eq at unsupported type"
  -- `(neq tp)` returns `true` if two values are not equal.
  | ._, (prim.neq tp) => 
    if pf : type.has_eq tp 
    then pure (fun v1 v2 => backend.s_not (value.partial_eq pf v1 v2))
    else throw "prim.eval.neq: neq at unsupported type"
  -- `(mux tp) c t f` evaluates to `t` when `c` is true and `f` otherwise.
  -- This only evaluates `t` when `c` is true, and only evaluates `f` when
  -- `c` is false.
  | ._, (prim.mux tp) => 
    if pf : type.has_mux tp
    then pure (fun bv v1 v2 => value.mux bv pf v1 v2)
    else throw "prim.eval.mux: mux at unsupported type"
  -- `zero` is the zero bit
  | ._, prim.bit_zero => pure backend.false
  -- `one` is the one bit
  | ._, prim.bit_one => pure backend.true

  | ._, prim.bit_or  => pure backend.s_or
  | ._, prim.bit_and => pure backend.s_and
  | ._, prim.bit_xor => pure backend.s_xor

  -- `bvnat` constructs a bit vector from a natural number.
  | ._, (prim.bv_nat w n) => pure (backend.s_bv_imm w n)
  -- `(add i)` returns the sum of two i-bit numbers.
  | ._, (prim.add i)        => pure (backend.s_bvadd i)
  -- `(adc i)` returns the sum of two i-bit numbers and a carry bit.
  | ._, (prim.adc i)         => pure (fun x y b => 
        backend.s_bvadd _ x (backend.s_bvadd _ y (backend.bit_to_bitvec _ b)))
  | ._, (prim.uadc_overflows i) => pure (fun x y b => 
        backend.s_bvult (backend.s_bvadd _ x (backend.s_bvadd _ y (backend.bit_to_bitvec _ b))) x)
  | ._, (prim.sadc_overflows i) => pure (fun x y b => 
        backend.s_bvslt (backend.s_bvadd _ x (backend.s_bvadd _ y (backend.bit_to_bitvec _ b))) x)
  -- `(bvsub i)` substracts two i-bit bitvectors.
  | ._, (prim.sub i) => pure (backend.s_bvsub i)
  -- `(ssbb_overflows i)` true if signed sub overflows, the bit
  -- is a borrow bit.
  -- FIXME: is this correct?
  | ._, (prim.ssbb_overflows i) => pure (fun x y b =>
        backend.s_bvslt (backend.s_bvsub _ (backend.s_bvsub _ x y) (backend.bit_to_bitvec _ b)) x)
  -- `(usbb_overflows i)` true if unsigned sub overflows,
  -- the bit is a borrow bit.
  | ._, (prim.usbb_overflows i) => pure (fun x y b =>
        backend.s_bvult (backend.s_bvsub _ x (backend.bit_to_bitvec _ b)) y)
  -- `(neg tp)` Two's Complement negation.
  | ._, (prim.neg i) => pure (backend.s_bvneg i)

  -- `(mul i)` returns the product of two i-bit numbers.
  | ._, (prim.mul i)            => pure (backend.s_bvmul i)

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

  | ._, (prim.ule i) => pure (fun x y => backend.s_not (backend.s_bvult y x))
  | ._, (prim.ult i) => pure (fun x y => backend.s_bvult x y)

  -- `(slice w u l)` takes bits `u` through `l` out of a `w`-bit number.
  --  prim (bv w .→ bv (u+1-l))
  | tp, (prim.slice w u l) => pure (fun v => backend.s_bvextract w u l v)
       -- let n := u + 1 - l;
       -- H <- annotate' "slice" (assert (w = w - n + n));
       -- let f : bitvec w → bitvec n := (bitvec.slice u l (w - n) H.default);
       -- pure f
  -- `(sext i o)` sign extends an `i`-bit number to a `o`-bit number.
  | ._, (prim.sext i o) => do -- H <- annotate' "sext" (assert (i ≤ o));
                             pure (backend.s_sext i o)
  -- `(uext i o)` unsigned extension of an `i`-bit number to a `o`-bit number.
  | ._, (prim.uext i o) => do -- H <- annotate' "uext" (assert (i ≤ o));
                             pure (backend.s_uext i o)
  -- `(trunc i o)` truncates an `i`-bit number to a `o`-bit number.
  | ._, (prim.trunc i o) => do -- H <- annotate' "trunc" (assert (o ≤ i));
                               pure (backend.s_trunc i o)

  | ._, (prim.cat i) => pure (fun x y => 
       let prf : i + i = (2 * i) := I_am_really_sorry _;
       Eq.recOn prf (backend.s_bvappend x y))
  --(begin simp [eval_nat_expr, nat_expr.eval_default_mul_eq, nat_expr.eval, eval_default_2, two_mul], 
  --end)

  -- | bv_least_nibble (i:Nat) : prim (bv i .→ bv 4)
  | ._, (prim.msb i)    => pure (backend.s_bvmsb i)
  | ._, (prim.bv_and i) => pure (backend.s_bvand i)
  | ._, (prim.bv_or i)  => pure (backend.s_bvor i)
  | ._, (prim.bv_xor i) => pure (backend.s_bvxor i)
  | ._, (prim.bv_complement i) => pure (backend.s_bvnot i)
  | ._, (prim.shl i)    => pure (fun x (y : backend.s_bv 8) => 
        backend.s_bvshl _ x (backend.s_uext _ _ y))
  --- `(shl_carry w) c b i` returns the `i`th bit
  --- in the bitvector [c]++b where `i` is treated as an unsigned
  --- number with `0` as the most-significant bit.
  -- e.g., If `i` is `0`, then this returns `c`.  If `i`
  -- exceeds the number of bits in `[c] ++ b` (i.e., i >= w+1),
  -- the the result is false.
  | ._, (prim.shl_carry w) => throw "prim.eval.shl_carry unimplemented"
-- pure (fun c x (y : backend.s_bv 8) => 
 --        backend.s_bvshl _ x (backend.s_uext _ _ y))

 -- pure (fun c b (i :  8) => 
 --       match i.to_nat with
 --       | Nat.zero        => c
 --       -- FIXME: is this the intended behaviour?
 --       | (Nat.succ n) => if n < w
 --                         then bitvec.nth b (w - n - 1) else false 
 --       )
   --- `(shr i) x y` shifts the bits in `x` to the right by
   --- `y` bits where `y` is treated as an unsigned integer.
   --- The new bits shifted in from the right are all zero.
   | ._, (prim.shr i) => pure (fun x (y : backend.s_bv 8) => 
        backend.s_bvlshr x (backend.s_uext _ _ y))
   --- `(shr_carry w) b c i` returns the `i`th bit
   --- in the bitvector b++[c] where `i` is treated as an unsigned
   --- number with `0` as the least-significant bit.
   -- e.g., If `i` is `0`, then this returns `c`.  If `i`
   -- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
   -- the the result is false.
  | ._, (prim.shr_carry w) => throw "prim.eval.shr_carry unimplemented"
 -- pure (fun b c (i : bitvec 8) => 
       -- match i.to_nat with
       -- | Nat.zero     => c
       -- | (Nat.succ n) => -- @ite _ (n < eval_nat_expr w) (Nat.decLt _ _) _ (bitvec.nth b n) false
       --   if n <  w then bitvec.nth b n else false
       -- )
   --- `(sar i) x y` arithmetically shifts the bits in `x` to
   --- the left by `y` bits where `y` is treated as an unsigned integer.
   --- The new bits shifted in all match the most-significant bit in y.
   | ._, (prim.sar i) => pure (fun x (y : backend.s_bv 8) => 
        backend.s_bvsshr x (backend.s_uext _ _ y))
   --- `(sar_carry w) b c i` returns the `i`th bit
   --- in the bitvector b++[c] where `i` is treated as an unsigned
   --- number with `0` as the least-significant bit.
   -- e.g., If `i` is `0`, then this returns `c`.  If `i`
   -- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
   -- the the result is equal to the most-signfiicant bit.
   | ._, (prim.sar_carry w) => throw "prim.eval.sar_carry unimplemented"
       --  pure (fun b c (i : bitvec 8) => 
       -- match i.to_nat with
       -- | Nat.zero     => c
       -- | (Nat.succ n) =>
       --   -- @ite _ (n < eval_nat_expr w) (Nat.decLt _ _) _ 
       --   --      (bitvec.nth b n)
       --   --      (bitvec.msb b)
       -- (if n < w then bitvec.nth b n else bitvec.msb b))
   
  | ._, (prim.even_parity i) => pure (fun b => backend.s_not (backend.s_parity b))
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
  | ._, (prim.pair_fst x y) => pure (fun (v : value x × value y) => v.fst)
  -- Return second element of a pair.
  | ._, (prim.pair_snd x y) => pure (fun (v : value x × value y) => v.snd)

-- FIXME: move into the backend?
def value.make_undef : ∀(tp : type), @value backend tp 
  | (bv e) => backend.s_bv_imm e 0
  | bit    => backend.s_bool_imm false
  | float  => ()
  | double => ()
  | x86_80 => ()
  | (vec w tp) => mkArray w (value.make_undef tp)
  | (pair tp tp') => (value.make_undef tp, value.make_undef tp')
  | (fn arg res) => fun _ => value.make_undef res

def expression.eval : ∀{tp : type}, expression tp -> @evaluator backend (@value backend tp)
  | ._, (expression.primitive p) => prim.eval p
  | ._, (@expression.bit_test wr wi re idxe) => do
    r   <- expression.eval re;
    idx <- expression.eval idxe;
    pure (backend.s_bit_test r idx)
  | ._, (expression.mulc m xe) => do
    x <- expression.eval xe;
    pure (backend.s_bvmul _ (backend.s_bv_imm 64 m) x)
  | ._, (expression.quotc m xe) => throw "expression.eval.quotc unimplemented"
  | ._, (expression.undef tp)   => pure (value.make_undef tp)
  | ._, (expression.app f a) => (expression.eval f) <*> (expression.eval a)
  | ._, (expression.get_reg r) => concrete_reg.read r
  | ._, (expression.read tp addre) => do
    addr   <- expression.eval addre;
    (match tp with
      | (bv we) => evaluator.read_memory_at addr we
      | _ => throw "expression.eval.read Trying to store non-bitvector")

  | ._, (expression.streg idx) => throw "expression.eval.streg unimplemented"
  | ._, (expression.get_local idx tp) => evaluator.local_at_idx idx tp
  -- This is overly general, we might not know that av here is an rval
  | ._, (expression.imm_arg idx tp) => do
    av <- evaluator.arg_at_idx idx;
    (match av with
    | (arg_value.rval v) => value.type_check _ v tp
    | _ => throw "expression.eval.imm_arg Not an rval")

  | ._, (expression.addr_arg idx) => do
    av <- evaluator.arg_at_idx idx;
    (match av with
    | (arg_value.lval (arg_lval.memloc _ addr)) => pure addr
    | _ => throw "expression.eval.addr_arg Not an memloc lval")
  -- FIXME: isn't specific to arg_lval
  | ._, (expression.read_arg idx tp) => do
    av <- evaluator.arg_at_idx idx;
    arg_value.to_value av tp

def lhs.set : ∀{tp : type}, lhs tp -> @value backend tp -> @evaluator backend Unit
  | ._, (lhs.set_reg r), v        => concrete_reg.set r v
  | ._, (lhs.write_addr ae tp), v => do
    a <- expression.eval ae;
    evaluator.write_memory_at a v
  | ._, (lhs.write_arg idx _tp), v => do
    av <- evaluator.arg_at_idx idx;
    -- fixme: we ignore tp here?
    arg_value.set_value av v
  | ._, (lhs.streg idx), v  => throw "lhs.set: unsupported FP write"

def lhs.read : ∀{tp : type}, lhs tp -> @evaluator backend (@value backend tp)
  | ._, (lhs.set_reg r)        => concrete_reg.read r
  | ._, (lhs.write_addr ae tp) => do
    addr <- expression.eval ae;
   (match tp with
     | (bv we) => evaluator.read_memory_at addr we
     | _ => throw "lhs.read Trying to store non-bitvector")
  | ._, (lhs.write_arg idx tp) => do
    av <- evaluator.arg_at_idx idx;
    -- fixme: we ignore tp here?
    arg_value.to_value av tp
  | ._, (lhs.streg idx) => throw "lhs.set: unsupported FP write"

def evaluator.push64 (v : value (bv 64)) : @evaluator backend Unit := do
  sp <- lhs.read rsp;
  let sp' := backend.s_bvsub _ sp (backend.s_bv_imm _ 8); do
    lhs.set rsp sp';
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
    new_ip <- expression.eval addr;
    old_ip <- evaluator.run_M backend.s_get_ip;
    evaluator.push64 old_ip;
    evaluator.run_M (backend.s_set_ip new_ip)

  | (event.jmp addr) => do
    new_ip <- expression.eval addr;
    evaluator.run_M (backend.s_set_ip new_ip)
  | (event.branch c addr) => do
    new_ip <- expression.eval addr;
    b      <- expression.eval c;
    evaluator.run_M (backend.s_cond_set_ip b new_ip)
  | event.hlt => throw "halt"
  | (event.xchg addr1 addr2) => throw "xchg"
  | event.cpuid => evaluator.run_M backend.s_read_cpuid

def action.eval : action -> @evaluator backend Unit
  | (action.set l e) => do v <- expression.eval e;
                           lhs.set l v
  | (action.set_cond l c e) => do
    b <- expression.eval c;
    v <- expression.eval e;
    evaluator.mux_m b (lhs.set l v) (pure ())
  | (@action.set_aligned (bv _) l e align) => throw "set_aligned: buggy case" -- FIXME: compiler bug
    -- v <- expression.eval os_state e,
    -- if v.to_nat % eval_nat_expr align = 0
    -- then lhs.set os_state l v
    -- else throw "Unaligned set_aligned"
  | (@action.set_aligned _ l e align) => throw "set_aligned: not a bv"
  | (@action.local_def tp idx e) => do 
    v <- expression.eval e;
    modify (fun s => { s with locals := s.locals.insert idx (Sigma.mk tp v)})
  | (action.event e) => event.eval e

-- FIXME: check pattern.context |- environment
def pattern.eval (p : pattern) (e : environment) : M backend Unit :=
    evaluator.run' (discard (List.mapM action.eval p.actions)) e
    -- pure ((fun (v : Unit × evaluator_state) => v.snd.system_state) <$> r)

end with_backend

end x86

