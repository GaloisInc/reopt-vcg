-- Evaluates actions in an environment.
import galois.data.bitvec
import .common
import .machine_memory
import .sexpr

-- FIXME: move
def annotate {ε} {m} [monad m] [monad_except ε m]
  {a} (f : ε -> ε) (c : m a) : m a := catch c (λe, throw (f e))

def annotate' {m} [monad m] [monad_except string m]
  {a} (e : string) (c : m a) : m a := annotate (λs, e ++ ": " ++ s) c

namespace mc_semantics

-- This represents only nats (not lhs or expression binders), and is
-- used to instantiate nat_exprs
@[reducible]
def nat_env := list (option nat)

namespace nat_expr

@[reducible]
def eval (e : nat_env) : nat_expr -> option ℕ 
  | (lit n)     := some n
  | (var idx)   := monad.join (list.nth e idx)
  | (add e1 e2) := (+) <$> (eval e1) <*> (eval e2) 
  | (sub e1 e2) := (λx y, x - y) <$> (eval e1) <*> (eval e2) 
  | (mul e1 e2) := (*) <$> (eval e1) <*> (eval e2) 
  | (div e1 e2) := (/) <$> (eval e1) <*> (eval e2) 

def wf_nat_expr (nenv : nat_env) : nat_expr -> Prop 
  | (lit _)     := true
  | (var idx)   := option.is_some (monad.join (list.nth nenv idx))
  | (add e1 e2) := wf_nat_expr e1 ∧ wf_nat_expr e2
  | (sub e1 e2) := wf_nat_expr e1 ∧ wf_nat_expr e2
  | (mul e1 e2) := wf_nat_expr e1 ∧ wf_nat_expr e2
  | (div e1 e2) := wf_nat_expr e1 ∧ wf_nat_expr e2

lemma eval_add_eq {e} {x y} : eval e (x + y) = (+) <$> (eval e x) <*> (eval e y) :=
  by { cases x; cases y; simp [ has_add.add, nat_expr.do_add, nat_expr.eval] }

lemma eval_sub_eq {e} {x y} : eval e (x - y) = (λx y, x - y) <$> (eval e x) <*> (eval e y) :=
  by { cases x; cases y; simp [ has_sub.sub, nat_expr.do_sub, nat_expr.eval]  }

lemma eval_mul_eq {e} {x y} : eval e (x * y) = (*) <$> (eval e x) <*> (eval e y) :=
  by { cases x; cases y; simp [ has_mul.mul, nat_expr.do_mul, nat_expr.eval] }

@[reducible]
def eval_default (e : nat_env) : nat_expr -> ℕ 
  | (lit n)     := n
  | (var idx)   := match list.nth e idx with | (some (some n)) := n | _ := 0 end
  | (add e1 e2) := (eval_default e1) + (eval_default e2) 
  | (sub e1 e2) := (eval_default e1) - (eval_default e2) 
  | (mul e1 e2) := (eval_default e1) * (eval_default e2) 
  | (div e1 e2) := (eval_default e1) / (eval_default e2) 

-- instance {nenv} : decidable_pred (wf_nat_expr nenv) := 
-- begin
--   unfold decidable_pred,
--   intros e,
--   induction e; simp [wf_nat_expr],
--   case lit { apply is_true, trivial },
--   case var { apply coe_decidable_eq },
--   apply_instance, 
  
-- end

lemma eval_default_add_eq {e} {x y} : eval_default e (x + y) = (eval_default e x) + (eval_default e y) :=
  by { cases x; cases y; simp [ has_add.add, nat_expr.do_add, eval_default] }

lemma eval_default_sub_eq {e} {x y} : eval_default e (x - y) = (eval_default e x) - (eval_default e y) :=
  by { cases x; cases y; simp [ has_sub.sub, nat_expr.do_sub, nat_expr.eval_default]  }

lemma eval_default_mul_eq {e} {x y} : eval_default e (x * y) = (eval_default e x) * (eval_default e y) :=
  by { cases x; cases y; simp [ has_mul.mul, nat_expr.do_mul, nat_expr.eval_default] }


-- @[reducible]
-- def eval : nat_expr -> ℕ 
--   | (nat_expr.lit n)     := n
--   -- | (nat_expr.var idx)   := match list.nth nat_env idx with | (some (some n)) := n | _ := 0 end
--   | (nat_expr.var idx)   := 0
--  -- FIXME, maybe use sorry?
--   | (nat_expr.add e1 e2) := (eval e1) + (eval e2) 
--   | (nat_expr.sub e1 e2) := (eval e1) - (eval e2) 
--   | (nat_expr.mul e1 e2) := (eval e1) * (eval e2) 
--   | (nat_expr.div e1 e2) := (eval e1) / (eval e2) 

end nat_expr

namespace type 

@[reducible]
def eval (nenv : nat_env) : type -> option type 
  | (bv e) := (λn, bv (nat_expr.lit n)) <$> nat_expr.eval nenv e
  | (fn arg res) := fn <$> (eval arg) <*> (eval res)
  | tp     := return tp

def eval_default (nenv : nat_env) : type -> type 
  | (bv e) := bv (nat_expr.lit (nat_expr.eval_default nenv e))
  | (fn arg res) := fn (eval_default arg) (eval_default res)
  | tp           := tp

def assert_types {m} [monad m] [monad_except string m] 
  (nenv : nat_env) 
  (t1 t2 : type) : m unit :=
  if eval_default nenv t1 = eval_default nenv t2
  then return () 
  else throw $ "Type mismatch: " ++ t1.pp ++ " and " ++ t2.pp ++ " in " ++ repr nenv

def assert_bv {m} [monad m] [monad_except string m] (nenv : nat_env) (tp : type) : m ℕ :=
  match tp with
  | (bv e) := return (nat_expr.eval_default nenv e)
  | _      := throw "Not a bitvecor"
  end             

end type
end mc_semantics


namespace x86

open mc_semantics
open mc_semantics.type

@[reducible]
def machine_word := bitvec 64

namespace reg

def inject : Π(rtp : gpreg_type), bitvec rtp.width' -> machine_word -> machine_word
  | gpreg_type.reg32 b _   := bitvec.append (bitvec.zero 32) b
  | gpreg_type.reg8h b old := old.set_bits 48 b (of_as_true trivial)
  | rtp              b old := old.set_bits (64 - rtp.width') b (begin cases rtp; simp end)

def project : Π(rtp : gpreg_type), machine_word -> bitvec rtp.width'
  | gpreg_type.reg8h b := b.get_bits 48 8 (begin simp [gpreg_type.width'], exact dec_trivial end)
  | rtp              b := b.get_bits (64 - rtp.width') rtp.width' (begin cases rtp; simp end)

end reg

structure machine_state : Type :=
  (mem    : memory)
  (gpregs : array 16 machine_word)
  (flags  : array 32 bool)
  (ip     : machine_word)

namespace machine_state

-- Constructs an empty machine state, with 0 where we need a value.
def empty : machine_state := 
  { mem    := memory.empty
  , gpregs := mk_array 16 0
  , flags  := mk_array 32 ff
  , ip     := 0
  }

def get_gpreg  (s : machine_state) (idx : fin 16) : machine_word := array.read s.gpregs idx

def update_gpreg (idx : fin 16) (f : machine_word -> machine_word) (s : machine_state) : machine_state :=
  { s with gpregs := array.write s.gpregs idx (f (get_gpreg s idx)) } 

def get_flag  (s : machine_state) (idx : fin 32) : bool := array.read s.flags idx

def update_flag (idx : fin 32) (f : bool -> bool) (s : machine_state) : machine_state :=
  { s with flags := array.write s.flags idx (f (get_flag s idx))} 

-- def store_bytes (addr : machine_word) (bs : list (bitvec 8)) (s : machine_state) : machine_state := 
--   { s with mem := s.mem.store_bytes addr bs }

-- def read_bytes (s : machine_state) (addr : machine_word) (n : ℕ) : option (list (bitvec 8)) :=
--   s.mem.read_bytes addr n

-- lemma read_bytes_length {s : machine_state} {addr : machine_word} {n : ℕ} {bs : list (bitvec 8)}
--   : read_bytes s addr n = some bs -> bs.length = n := memory.read_bytes_length

def store_word {n : ℕ} (s : machine_state) (addr : machine_word) (b : bitvec (8 * n)) : machine_state := 
  { s with mem := s.mem.store_word addr b }

def read_word (s : machine_state) (addr : machine_word) (n : ℕ) : option (bitvec (8 * n)) :=
  s.mem.read_word addr n

def print_regs (s : machine_state) : string :=
  let lines := list.zip_with (λn (r : bitvec 64), n ++ ": " ++ r.pp_hex ++ ", ") reg.r64_names s.gpregs.to_list
  in string.join lines

def print_set_flags (s : machine_state) : string :=
  let lines := list.zip_with (λn (r : bool), if r then n else "") reg.flag_names s.flags.to_list
  in "[" ++ string.intercalate ", " (list.filter (λs, s.length > 0) lines) ++ "]"

end machine_state

inductive arg_lval
  | reg {} {tp : type}  : concrete_reg tp -> arg_lval 
  | memloc (width : ℕ) (addr : machine_word) : arg_lval 

namespace arg_lval

def repr : arg_lval -> string
  | (reg r)             := r.repr
  | (memloc width addr) := has_repr.repr addr ++ "@" ++ has_repr.repr width

instance arg_lval_repr : has_repr arg_lval := ⟨repr⟩

end arg_lval

section with_nat_env

-- OS stuff
parameters (os_state : Type)

structure system_state := 
  (machine_state : machine_state)
  (os_state      : os_state)

@[reducible]
def system_m := state_t system_state (except string)
parameter (os_transition : system_m unit)

parameter (nenv : nat_env)

@[reducible]
def eval_nat_expr (e : nat_expr) : nat
  := nat_expr.eval_default nenv e

@[reducible]
def eval_type : type -> type := type.eval_default nenv
  -- | (bv e) := bv (nat_expr.lit (eval_nat_expr e))
  -- | (fn arg res) := fn (eval_type arg) (eval_type res)
  -- | tp     := tp

@[reducible]
def value : type -> Type
  | (bv e) := bitvec (eval_nat_expr e) -- We use the _normalised_ value here.
  | bit    := bool
  | float  := unit -- FIXME
  | double := unit -- FIXME
  | x86_80 := unit -- FIXME  
  | (vec w tp) := array (eval_nat_expr w) (value tp) -- FIXME
  | (pair tp tp') := value tp × value tp'
  | (fn arg res) := (value arg) -> (value res)

-- namespace value

-- def value.repr : Π{tp : type}, value tp -> string
--   | (bv e) b                := has_repr.repr b
--   | (fn _ _ ) _             := "<function>"
--   | _ _                     := "Unsupported type"


-- instance value_repr {tp : type} : has_repr (value tp) := ⟨value.repr⟩

-- end value

-- Corresponding to the binder type, more or less.
inductive arg_value 
  -- natv is here for completeness --- the presumption is that a
  -- one_of param is only used in types, but in case it is not, we
  -- include a binding in the environment,
  | natv             : ℕ        -> arg_value 
  -- covers reg, addr, and lhs bindings
  | lval             : arg_lval -> arg_value
  | rval {tp : type} : value tp -> arg_value

-- namespace arg_value

-- def repr : arg_value -> string 
--   | (lval l) := l.repr
--   | (rval v)  := v.repr

-- instance arg_value_repr : has_repr arg_value := ⟨repr⟩

-- end arg_value

@[reducible]
def environment := list arg_value

structure evaluator_state : Type :=
  (system_state : system_state)
  (environment  : environment) -- read only, but reading can fail
  (locals       : rbmap ℕ (sigma value))

-- namespace evaluator_state

def evaluator_state.init (sst : system_state) : evaluator_state := 
  { system_state  := sst
  , environment   := []
  , locals        := mk_rbmap ℕ (sigma value)
  }

-- end evaluator_state

-- Monad for evaluating with failure.  This nesting might be useful to get the ip where things break?
@[reducible]
def evaluator := state_t evaluator_state (except string)

-- FIXME: are these an oversight in the stdlib? 
instance (ε): monad_except ε (except ε) := 
  { throw := λα e, except.error e, catch := λα m f, match m with | (except.error e) := f e | _ := m end }

instance (ε) (m) [monad_except ε m] : has_orelse m := 
  { orelse := λα, monad_except.orelse }

instance (ε) [inhabited ε] : alternative (except ε) := 
  { failure := λα, except.error (default ε)}

-- namespace type

-- If evaluation of the expr fails, we return the original type.  
-- def normalise (e : environment) : type -> type
--   | (base b)     := base (base_type.normalise e b)
--   | (fn arg res) := fn (normalise arg) (normalise res)
  
-- def equiv (e : environment) (t1 : type) (t2 : type) : Prop :=
--   normalise e t1 = normalise e t2

-- instance (e) : decidable_rel (equiv e) :=
--   λa b, begin simp [equiv], apply_instance end

-- end type

-- namespace value

lemma value.type_eval_is_id: Π{tp : type}, value (eval_type tp) = value tp :=
begin  
  intros,
  induction tp,
  case bv { refl },
  case fn { simp [value, eval_type, type.eval_default], rw [ tp_ih_arg, tp_ih_res ] },
  repeat { refl }
end

def value.eval_cong {tp tp' : type} (pf : eval_type tp = eval_type tp') (v : value tp) : value tp' :=
begin
  rw <- value.type_eval_is_id,
  rw <- value.type_eval_is_id at v,
  exact (eq.rec v pf)   
end

-- This allows us to resolve arith in nat_exprs
def value.type_check {m} [monad m] [monad_except string m] (tp : type) (v : value tp) (tp' : type) 
  : m (value tp') :=
  if H : eval_type tp = eval_type tp'
  then return (value.eval_cong H v)
  else throw "type_check: arg type mismatch"

-- end value


-- namespace evaluator

def evaluator.run {a : Type} (m : evaluator a) (s : evaluator_state) : except string (a × evaluator_state) :=
  (m.run s)

def evaluator.read_memory_at (addr : machine_word) (n : ℕ) : evaluator (bitvec n) := do
    s <- get, 
    match s.system_state.machine_state.read_word addr (n / 8) with
    | none := throw "read_memory_at: no bytes at addr" 
    | (some w) := 
      if H : 8 * (n / 8) = n
      then return (bitvec.cong H w)
      else throw "evaluator.read_memory_at: width not a multiple of 8"
    end

def evaluator.map_machine_state (f : machine_state → machine_state) : evaluator unit :=
  modify (λ(s : evaluator_state), { s with system_state := { s.system_state with machine_state := f s.system_state.machine_state } })

def evaluator.write_memory_at : Π{tp : type} (addr : machine_word) (bytes : value tp), evaluator unit
  | (bv e) addr bytes :=
    let width := eval_nat_expr e
    in (if H : width = 8 * (width / 8)
        then evaluator.map_machine_state (λ(s : machine_state), s.store_word addr (bitvec.cong H bytes))
        else throw "evaluator.write_memory_at: width not a multiple of 8")
  | _ _ _ := throw "evaluator.write_memory_at not a bv"

def evaluator.arg_at_idx (idx : ℕ) : evaluator arg_value :=
  do s <- get,
     match s.environment.nth idx with
       | (some a) := return a
       | none     := throw "evaluator.arg_at_idx: no arg at idx"
     end

-- We should factor out the type check, although it might depend on
-- the functor (value in this case) if we generalise equality
def evaluator.local_at_idx (idx : ℕ) (tp : type) : evaluator (value tp) :=
  do s <- get,
     match s.locals.find idx with
     | (some (sigma.mk tp' v)) := value.type_check _ v tp
     | none     := throw "local_at_idx: no arg at idx"
     end

lemma width_width' : Π(rtp : gpreg_type), eval_nat_expr rtp.width = rtp.width' :=
begin
  intro, induction rtp; trivial
end

def concrete_reg.set : Π{tp : type}, concrete_reg tp -> value tp -> evaluator unit
  | ._ (concrete_reg.gpreg idx rtp) b := 
    let b' : bitvec rtp.width' := eq.rec b (width_width' rtp)
    in evaluator.map_machine_state (machine_state.update_gpreg idx (reg.inject rtp b'))
  | ._ (concrete_reg.flagreg idx)   b := 
    evaluator.map_machine_state (machine_state.update_flag idx (λ_, b))
  
def concrete_reg.from_state : Π{tp : type}, concrete_reg tp -> machine_state -> value tp
  | _ (concrete_reg.gpreg idx rtp) s := 
    let v := reg.project rtp (s.get_gpreg idx) 
    in begin simp [value, width_width' nenv rtp], exact v end
  | _ (concrete_reg.flagreg idx)   s := s.get_flag idx

def concrete_reg.read {tp : type} (r : concrete_reg tp) : evaluator (value tp) := 
    do s <- get, 
       return (concrete_reg.from_state r s.system_state.machine_state)

-- namespace arg_lval 

def arg_lval.to_value' {m} [monad m] [monad_except string m] 
  (s : machine_state)
  : arg_lval -> Π(tp : type), m (value tp)
  | (@arg_lval.reg tp r) tp' := value.type_check tp (concrete_reg.from_state r s) tp'
  | (arg_lval.memloc width addr) tp' :=
    match s.read_word addr (width / 8) with
    | none := throw "arg_lval.to_value': no bytes at addr" 
    | (some w) := value.type_check (bv (8 * (width / 8))) w tp'
    end

def arg_lval.to_value : arg_lval -> Π(tp : type), evaluator (value tp)
  | (@arg_lval.reg tp r) tp' := do v <- concrete_reg.read r,
                                   value.type_check tp v tp'
  | (arg_lval.memloc width addr) tp' := do
    v <- evaluator.read_memory_at addr width,
    value.type_check (bv width) v tp'

def arg_lval.set_value : arg_lval -> Π{tp : type}, value tp -> evaluator unit
  | (@arg_lval.reg tp r) tp' v := do v' <- value.type_check _ v tp,
                                     concrete_reg.set r v'
  | (arg_lval.memloc _width addr) tp v := do
    evaluator.write_memory_at addr v

-- def read_memory_at (av : arg_value) (n : ℕ) : evaluator (bitvec (8 * n)) :=
--   match av with 
--   | (@arg_value.bv 64 addr) := 
--   | _                      := throw "addr.read: not a 64-bit bitvecor"
--   end

-- Can fail if types mismatch
def arg_value.to_value : arg_value -> Π(tp : type), evaluator (value tp)
  | (arg_value.natv _ _)  _ := throw "arg_value.to_value: saw a natv"
  | (arg_value.lval _ l) tp := arg_lval.to_value l tp
  | (arg_value.rval v) tp := value.type_check _ v tp

def arg_value.set_value : arg_value -> Π{tp : type}, value tp -> evaluator unit
  | (arg_value.lval _ l) tp v := arg_lval.set_value l v
  | _ _ _ := throw "arg_value.set_value: not an lvalue"

def addr.read : Π{tp : type}, addr tp -> evaluator (value tp)
  | tp (addr.arg idx) := do 
      av <- evaluator.arg_at_idx idx,
      arg_value.to_value av tp -- FIXME: we should really check if this is a memloc first.
      -- w  <- av.read_memory_at n,
      -- return (value.bv w)

def addr.set : Π{tp : type}, addr tp -> value tp -> evaluator unit
  | tp (addr.arg idx) v := do 
      av <- evaluator.arg_at_idx idx, -- FIXME: we should really check if this is a memloc first.
      arg_value.set_value av v

-- This is the least-worst option.  The other alternative is to have a
-- value constructor for functions, which we only need here.
inductive {u v} hlist {α : Type u} (f : α -> Type v): list α -> Type (max u v)
  | hnil  : hlist []
  | hcons {xs : list α} (x : α) : f x -> hlist xs -> hlist (x :: xs)

-- namespace nat_expr

-- def eval' (ne : nat_expr) : evaluator ℕ := do
--   s <- get,
--   match nat_expr.eval s.environment ne with
--   | none := throw "nat_expr.eval': couldn't eval"
--   | (some n) := return n
--   end
-- end nat_expr

-- def prim_binop (e : nat_expr) (p : Π{n : ℕ}, bitvec n -> bitvec n -> bitvec n) :=
--   evaluator.with_nat_expr_as_nat' (λi, value (bv i .→ bv i .→ bv i)) e (λn, return (@p n))

-- lemma eval_add_eq {x y} : eval_nat_expr (x + y) =  (eval_nat_expr x + eval_nat_expr y) :=
-- begin
--   simp [eval_nat_expr, nat_expr.eval_add_eq, has_seq.seq], 
-- end

  -- by { cases x; cases y; simp [
  --                              has_add.add, has_seq.seq, nat_expr.do_add
  --                             , nat_expr.eval] }

-- FIXME: move
-- Might be easier to define in terms of to_int/from_int etc.
def bitvec.uext {n} (m : ℕ) (p: n ≤ m) (x:bitvec n) : bitvec m :=
  bitvec.set_bits 0 0 x (begin simp, exact p end)
  
def bitvec.sext {n} (m : ℕ) (p: n ≤ m) (x:bitvec n) : bitvec m :=
  bitvec.set_bits (if x.msb then (bitvec.zero m).not else 0) 0 x (begin simp, exact p end)

def bitvec.trunc {n} (m : ℕ) (p: m ≤ n) (x:bitvec n) : bitvec m :=
  bitvec.get_bits x 0 m (begin simp, exact p end)

def bit_to_bitvec (n : ℕ) (b : bool) : bitvec n := 
  if b then 1 else 0

lemma eval_default_2 {e} : nat_expr.eval_default e 2 = 2 := rfl

lemma nat_expr_eval_2 : eval_nat_expr 2 = 2 := rfl

def type.has_eq : type -> Prop
  | (bv _)     := true
  | bit        := true
  | float      := true 
  | double     := true 
  | x86_80     := true
  | (vec _ tp) := type.has_eq tp 
  | (pair tp tp') := type.has_eq tp ∧ type.has_eq tp'
  | (fn _ _)   := false -- could probably come up with something, but nothing efficient

@[reducible]
def type.has_eq_dec : Π(tp : type), decidable (type.has_eq tp) 
  | (bv _)     := is_true true.intro  
  | bit        := is_true true.intro  
  | float      := is_true true.intro  
  | double     := is_true true.intro  
  | x86_80     := is_true true.intro  
  | (vec _ tp) := type.has_eq_dec tp
  | (pair tp tp') := @and.decidable _ _ (type.has_eq_dec tp) (type.has_eq_dec tp')
  | (fn _ _)   := is_false not_false

instance decidable_pred_type_has_eq: decidable_pred type.has_eq := type.has_eq_dec

def value.partial_eq : Π{tp : type}, type.has_eq tp -> value tp -> value tp -> bool
  | (bv _) _ v1 v2      := (v1 = v2)
  | bit    _ v1 v2      := (v1 = v2)
  | float  _ v1 v2      := (v1 = v2)
  | double  _ v1 v2     := (v1 = v2)
  | x86_80  _ v1 v2     := (v1 = v2)
  | (vec _ tp) pf v1 v2 := 
    let pf' : type.has_eq tp := pf
    in (list.zip (array.to_list v1) (array.to_list v2)).all (λ(v : (value tp × value tp)), value.partial_eq pf' v.fst v.snd)
  | (pair tp tp') pf v1 v2 := 
    band (value.partial_eq pf.left v1.fst v2.fst) (value.partial_eq pf.right v1.snd v2.snd)

-- Returns the number of bits that are tt mod 2
def bitvec.parity {n : ℕ} (b : bitvec n) : bool :=
  bitvec.foldl bxor ff b

example : bitvec.parity (3 : bitvec 4) = ff := by refl
example : bitvec.parity (7 : bitvec 4) = tt := by refl

def prim.eval : Π{tp : type}, prim tp -> evaluator (value tp)
  -- `(eq tp)` returns `true` if two values are equal.
  | ._ (prim.eq tp) := 
    if pf : type.has_eq tp 
    then return (value.partial_eq pf)
    else throw "prim.eval.eq: eq at unsupported type"
  -- `(neq tp)` returns `true` if two values are not equal.
  | ._ (prim.neq tp) := 
    if pf : type.has_eq tp 
    then return (λv1 v2, bnot (value.partial_eq pf v1 v2))
    else throw "prim.eval.neq: neq at unsupported type"
  -- `(mux tp) c t f` evaluates to `t` when `c` is true and `f` otherwise.
  -- This only evaluates `t` when `c` is true, and only evaluates `f` when
  -- `c` is false.
  | ._ (prim.mux tp) := return (λb l r, if b then l else r)

  -- `zero` is the zero bit
  | ._ prim.bit_zero := return ff
  -- `one` is the one bit
  | ._ prim.bit_one := return tt

  | ._ prim.bit_or  := return bor
  | ._ prim.bit_and := return band
  | ._ prim.bit_xor := return bxor

  -- `bvnat` constructs a bit vector from a natural number.
  | ._ (prim.bv_nat w n) := return (bitvec.of_nat (eval_nat_expr w) (eval_nat_expr n))
  -- `(add i)` returns the sum of two i-bit numbers.
  | ._ (prim.add i)        := return bitvec.add
  -- `(adc i)` returns the sum of two i-bit numbers and a carry bit.
  | ._ (prim.adc i)         := return (λx y b, bitvec.add x (bitvec.add y (bit_to_bitvec _ b)))
  | ._ (prim.uadc_overflows i) := return (λx y b, bitvec.ult (x + y + bit_to_bitvec (eval_nat_expr i) b) x)
  | ._ (prim.sadc_overflows i) := return (λx y b, bitvec.slt (x + y + bit_to_bitvec (eval_nat_expr i) b) x)
  -- `(bvsub i)` substracts two i-bit bitvectors.
  | ._ (prim.sub i) := return bitvec.sub
  -- `(ssbb_overflows i)` true if signed sub overflows, the bit
  -- is a borrow bit.
  -- FIXME: is this correct?
  | ._ (prim.ssbb_overflows i) := 
    return (λx y b, bitvec.slt x (x - y - bit_to_bitvec (eval_nat_expr i) b))
  -- `(usbb_overflows i)` true if unsigned sub overflows,
  -- the bit is a borrow bit.
  | ._ (prim.usbb_overflows i) := return (λx y b, bitvec.ult x (x - y - bit_to_bitvec (eval_nat_expr i) b))

  -- `(neg tp)` Two's Complement negation.
  | ._ (prim.neg i) := return bitvec.neg

  -- `(mul i)` returns the product of two i-bit numbers.
  | ._ (prim.mul i)            := return bitvec.mul

  -- `(quotRem i) n d` returns a pair `(q,r)` where `q` is a `floor (n/d)`
  -- and `r` is `n - d * floor (n/d)`.
  -- `n` and `d` are treated as unsigned values.
  -- If `d = 0` or `floor(n/d) >= 2^n`, then this triggers a #DE exception.
  | ._ (prim.quotRem i) := throw "prim.eval.quotRem unimplemented"

  -- `(squotRem i) n d` returns a pair `(q,r)` where `q` is a `trunc (n/d)`
  -- and `r` is `n - d * trunc (n/d)`.  `trunc` always round to zero.
  -- `n` and `d` are treated as signed values.
  -- If `d = 0`, `trunc(n/d) >= 2^(n-1)` or `trunc(n/d) < -2^(n-1), then this
  -- triggers a #DE exception when evaluated.
  | ._ (prim.squotRem i) := throw "prim.eval.squotRem unimplemented"

  | ._ (prim.ule i) := return (λx y, bitvec.ule x y)
  | ._ (prim.ult i) := return (λx y, bitvec.ult x y)

  -- `(slice w u l)` takes bits `u` through `l` out of a `w`-bit number.
  --  prim (bv w .→ bv (u+1-l))
  --  slice {w: ℕ} (u l k:ℕ) (H: w = k + (u + 1 - l)) (x: bitvec w) : bitvec (u + 1 - l)
  | tp (prim.slice w u l) := do
       let n := eval_nat_expr u + 1 - eval_nat_expr l,
       H <- annotate' "slice" (assert (eval_nat_expr w = (eval_nat_expr w - n + n))),
       return (begin
         have rewr : value nenv (bv (u + 1 - l)) = value nenv (bv (nat_expr.lit n)) :=
           begin simp [n, value, nat_expr.eval_default_sub_eq
                      , nat_expr.eval_default_add_eq
                      , eval_nat_expr, nat_expr.eval_default], rw add_comm, refl end,
         simp [value], rw rewr,
         exact (bitvec.slice (eval_nat_expr nenv u) (eval_nat_expr nenv l) (eval_nat_expr nenv w - n) H.default)
        end)
  -- `(sext i o)` sign extends an `i`-bit number to a `o`-bit number.
  | ._ (prim.sext i o) := do H <- annotate' "sext" (assert (eval_nat_expr i ≤ eval_nat_expr o)),
                             return (bitvec.sext (eval_nat_expr o) H.default)
  -- `(uext i o)` unsigned extension of an `i`-bit number to a `o`-bit number.
  | ._ (prim.uext i o) := do H <- annotate' "uext" (assert (eval_nat_expr i ≤ eval_nat_expr o)),
                             return (bitvec.uext (eval_nat_expr o) H.default)
  -- `(trunc i o)` truncates an `i`-bit number to a `o`-bit number.
  | ._ (prim.trunc i o) := do H <- annotate' "trunc" (assert (eval_nat_expr o ≤ eval_nat_expr i)),
                              return (bitvec.trunc (eval_nat_expr o) H.default)

  | ._ (prim.cat i) := return (λx y, bitvec.cong
                                    (begin simp [eval_nat_expr, nat_expr.eval_default_mul_eq, nat_expr.eval, eval_default_2, two_mul], 
                                     end)
                                    (bitvec.append x y))
  -- | bv_least_nibble (i:ℕ) : prim (bv i .→ bv 4)
  | ._ (prim.msb i) := return bitvec.msb
  | ._ (prim.bv_and i) := return bitvec.and
  | ._ (prim.bv_or i)  := return bitvec.or
  | ._ (prim.bv_xor i) := return bitvec.xor
  | ._ (prim.bv_complement i) := return bitvec.not
  | ._ (prim.shl i)    := return (λx (y : bitvec 8), bitvec.shl x y.to_nat)
  --- `(shl_carry w) c b i` returns the `i`th bit
  --- in the bitvector [c]++b where `i` is treated as an unsigned
  --- number with `0` as the most-significant bit.
  -- e.g., If `i` is `0`, then this returns `c`.  If `i`
  -- exceeds the number of bits in `[c] ++ b` (i.e., i >= w+1),
  -- the the result is false.
  | ._ (prim.shl_carry w) := return (λc b (i : bitvec 8), 
       match i.to_nat with
       | nat.zero        := c
       -- FIXME: is this the intended behaviour?
       | (nat.succ n) := if n < eval_nat_expr w
                         then bitvec.nth b (eval_nat_expr w - n - 1) else ff 
       end)
   --- `(shr i) x y` shifts the bits in `x` to the right by
   --- `y` bits where `y` is treated as an unsigned integer.
   --- The new bits shifted in from the right are all zero.
   | ._ (prim.shr i) := return (λx (y : bitvec 8), bitvec.ushr x y.to_nat)
   --- `(shr_carry w) b c i` returns the `i`th bit
   --- in the bitvector b++[c] where `i` is treated as an unsigned
   --- number with `0` as the least-significant bit.
   -- e.g., If `i` is `0`, then this returns `c`.  If `i`
   -- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
   -- the the result is false.
  | ._ (prim.shr_carry w) := return (λb c (i : bitvec 8), 
       match i.to_nat with
       | nat.zero     := c
       | (nat.succ n) := @ite (n < eval_nat_expr w) (nat.decidable_lt _ _) _ (bitvec.nth b n) ff
-- if n < eval_nat_expr w 
-- then bitvec.nth b n
-- else ff 
       end)
   --- `(sar i) x y` arithmetically shifts the bits in `x` to
   --- the left by `y` bits where `y` is treated as an unsigned integer.
   --- The new bits shifted in all match the most-significant bit in y.
   | ._ (prim.sar i) := return (λx (y : bitvec 8), bitvec.sshr x y.to_nat)
   --- `(sar_carry w) b c i` returns the `i`th bit
   --- in the bitvector b++[c] where `i` is treated as an unsigned
   --- number with `0` as the least-significant bit.
   -- e.g., If `i` is `0`, then this returns `c`.  If `i`
   -- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
   -- the the result is equal to the most-signfiicant bit.
   | ._ (prim.sar_carry w) := return (λb c (i : bitvec 8), 
       match i.to_nat with
       | nat.zero     := c
       | (nat.succ n) := 
         @ite (n < eval_nat_expr w) (nat.decidable_lt _ _) _ 
              (bitvec.nth b n)
              (bitvec.msb b)
-- (if n < eval_nat_expr w 
--                           then bitvec.nth b n
--                           else bitvec.msb b)
         end)
   
  | ._ (prim.even_parity i) := return (λb, bitvec.parity b = ff)
  -- `(bsf i)` returns the index of least-significant bit that is 1.
  | ._ (prim.bsf i)         := throw "prim.eval.bsf unimplemented"
  -- `(bsr i)` returns the index of most-significant bit that is 1.
  | ._ (prim.bsr i)         := throw "prim.eval.bsr unimplemented"
  -- `(bswap i)` reverses the bytes in the bitvector.
  | ._ (prim.bswap i)       := throw "prim.eval.bswap unimplemented"
  -- `(btc w j) base idx` interprets base as bitvector and returns
  -- a bitvector contains the same bits as `base` except the `i`th bit
  -- (where 0 denotes the least-significant bit) is complemented.
  -- The value `i` is `idx` as a unsigned integer modulo `w`.
  | ._ (prim.btc w j)         := throw "prim.eval.btc unimplemented"
  -- `(btr w j) base idx` interprets base as bitvector and returns
  -- a bitvector contains the same bits as `base` except the `i`th bit
  -- (where 0 denotes the least-significant bit) is cleared.
  -- The value `i` is `idx` as a unsigned integer modulo `w`.
  | ._ (prim.btr w j)         := throw "prim.eval.btr unimplemented"
  -- `(bts w j) base idx` interprets base as bitvector and returns
  -- a bitvector contains the same bits as `base` except the `i`th bit
  -- (where 0 denotes the least-significant bit) is set.
  -- The value `i` is `idx` as a unsigned integer modulo `w`.
  | ._ (prim.bts w j)         := throw "prim.eval.bts unimplemented"

  -- `bv_to_x86_80` converts a bitvector to an extended precision number (lossless)
  | ._ (prim.bv_to_x86_80 w)  := throw "prim.eval.bv_to_x86_80 unimplemented"
  -- `float_to_x86_80` converts a float to an extended precision number (lossless)
  | ._ prim.float_to_x86_80   := throw "prim.eval.float_to_x86_80 unimplemented"
  -- `double_to_x86_80` converts a double to an extended precision number (lossless)
  | ._ prim.double_to_x86_80   := throw "prim.eval.double_to_x86_80 unimplemented"
  -- `x87_fadd` adds two extended precision values using the flags in the x87 register.
  | ._ prim.x87_fadd           := throw "prim.eval.dx87_fadd unimplemented"

  -- Return first element of a pair
  | ._ (prim.pair_fst x y) := return (λ(v : value x × value y), v.fst)
  -- Return second element of a pair.
  | ._ (prim.pair_snd x y) := return (λ(v : value x × value y), v.snd)

def value.make_undef : Π(tp : type), value tp 
  | (bv e) := bitvec.of_nat (eval_nat_expr e) 0
  | bit    := ff
  | float  := ()
  | double := ()
  | x86_80 := ()
  | (vec w tp) := mk_array (eval_nat_expr w) (value.make_undef tp)
  | (pair tp tp') := (value.make_undef tp, value.make_undef tp')
  | (fn arg res) := λ_, value.make_undef res

def expression.eval : Π{tp : type}, expression tp -> evaluator (value tp)
  | ._ (expression.primitive p) := prim.eval p
  | ._ (@expression.bit_test wr wi re idxe) := do
    r   <- expression.eval re,
    idx <- expression.eval idxe,
    let idx' := idx.to_nat % eval_nat_expr wr 
    in return (r.nth idx')
  | ._ (expression.mulc m xe) := do
    x <- expression.eval xe,
    return (bitvec.mul (bitvec.of_nat 64 (eval_nat_expr m)) x)
  | ._ (expression.quotc m xe) := throw "expression.eval.quotc unimplemented"
  | ._ (expression.undef tp)   := return (value.make_undef tp)
  | ._ (expression.app f a) := (expression.eval f) <*> (expression.eval a)
  | ._ (expression.get_reg r) := concrete_reg.read r
  | ._ (expression.read tp addre) := do
    addr   <- expression.eval addre,
    match tp with
      | (bv we) := evaluator.read_memory_at addr (eval_nat_expr we)
      | _ := throw "expression.eval.read Trying to store non-bitvector"
    end
  | ._ (expression.streg idx) := throw "expression.eval.streg unimplemented"
  | ._ (expression.get_local idx tp) := evaluator.local_at_idx idx tp
  -- This is overly general, we might not know that av here is an rval
  | ._ (expression.imm_arg idx tp) := do
    av <- evaluator.arg_at_idx idx,
    match av with
    | (arg_value.rval v) := value.type_check _ v tp
    | _ := throw "expression.eval.imm_arg Not an rval"
    end
  | ._ (expression.addr_arg idx) := do
    av <- evaluator.arg_at_idx idx,
    match av with
    | (arg_value.lval _ (arg_lval.memloc _ addr)) := return addr
    | _ := throw "expression.eval.addr_arg Not an memloc lval"
    end
  -- FIXME: isn't specific to arg_lval
  | ._ (expression.read_arg idx tp) := do
    av <- evaluator.arg_at_idx idx,
    arg_value.to_value av tp

def evaluator.set_ip (new_ip : bitvec 64) : evaluator unit :=
  evaluator.map_machine_state (λ(s : machine_state), { s with ip := new_ip })

def lhs.set : Π{tp : type}, lhs tp -> value tp -> evaluator unit
  | ._ (lhs.set_reg r) v        := concrete_reg.set r v
  | ._ (lhs.write_addr ae tp) v := do
    a <- expression.eval ae,
    evaluator.write_memory_at a v
  | ._ (lhs.write_arg idx _tp) v := do
    av <- evaluator.arg_at_idx idx,
    -- fixme: we ignore tp here?
    arg_value.set_value av v
  | ._ (lhs.streg idx) v  := throw "lhs.set: unsupported FP write"

def lhs.read : Π{tp : type}, lhs tp -> evaluator (value tp)
  | ._ (lhs.set_reg r)        := concrete_reg.read r
  | ._ (lhs.write_addr ae tp) := do
    addr <- expression.eval ae,
    match tp with
      | (bv we) := evaluator.read_memory_at addr (eval_nat_expr we)
      | _ := throw "lhs.read Trying to store non-bitvector"
    end
  | ._ (lhs.write_arg idx tp) := do
    av <- evaluator.arg_at_idx idx,
    -- fixme: we ignore tp here?
    arg_value.to_value av tp
  | ._ (lhs.streg idx) := throw "lhs.set: unsupported FP write"

def evaluator.push64 (v : value (bv 64)) : evaluator unit := do
  sp <- lhs.read rsp,
  let sp' := sp - 8 in do
    lhs.set rsp sp',
    evaluator.write_memory_at sp' v



def read_cpuid : evaluator unit :=
  -- Copied from the cpuid results from my macbook
  -- Note: CPUID is allowed to return 0s 
  let cpuid_values : rbmap ℕ (bitvec 32 × bitvec 32 × bitvec 32 × bitvec 32) :=
    rbmap.from_list [ (0, (0xd, 0x756e6547, 0x6c65746e, 0x49656e69))
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
                    ] in -- FIXME: we need to look at rcx sometimes as well
    let cpuid_fn (n : ℕ) : (bitvec 32 × bitvec 32 × bitvec 32 × bitvec 32) :=
      match cpuid_values.find n with
      | none     := (0, 0, 0, 0)
      | (some r) := r
      end
    in do 
      raxv <- lhs.read rax,
      match cpuid_fn raxv.to_nat with 
      | (axv, bxv, cxv, dxv) := do 
        lhs.set eax axv,
        lhs.set ebx bxv,
        lhs.set ecx cxv,
        lhs.set edx dxv
      end


def event.eval : event -> evaluator unit
  | event.syscall :=
    adapt_state (λ(s : evaluator_state), (s.system_state, s))
                (λs s', { s' with system_state := s })
                os_transition
  | (event.unsupported msg) := throw ("event.eval: unsupported: " ++ msg)
  | event.pop_x87_register_stack := throw "pop_x87_register_stack"
  | (event.call addr) := do
    new_ip <- expression.eval addr,
    s <- get,
    evaluator.push64 s.system_state.machine_state.ip,
    evaluator.set_ip new_ip

  | (event.jmp addr) := do
    new_ip <- expression.eval addr,
    evaluator.set_ip new_ip
  | (event.branch c addr) := do
    new_ip <- expression.eval addr,
    b      <- expression.eval c,
    when b (evaluator.set_ip new_ip)
  | event.hlt := throw "halt"
  | (event.xchg addr1 addr2) := throw "xchg"
  | event.cpuid := read_cpuid

-- def lhs.read : Π{tp : type}, lhs tp -> evaluator (value tp)
--   | ._ (lhs.reg r)       := reg.read r
--   | ._ (lhs.addr a)      := addr.read a
--   | ._ (lhs.arg idx tp)  := do av <- evaluator.arg_at_idx idx, 
--                                   arg_value.to_value av tp
--   | ._ (lhs.streg idx)   := throw "lhs.read: unsupported FP read"
    
def action.eval : action -> evaluator unit
  | (action.set l e) := do v <- expression.eval e,
                           lhs.set l v
  | (action.set_cond l c e) := do
    b <- expression.eval c,
    v <- expression.eval e,
    when b (lhs.set l v)
  | (@action.set_aligned (bv _) l e align) := do
    v <- expression.eval e,
    if v.to_nat % eval_nat_expr align = 0
    then lhs.set l v
    else throw "Unaligned set_aligned"
  | (@action.set_aligned _ l e align) := throw "set_aligned: not a bv"
  | (@action.local_def tp idx e) := do 
    v <- expression.eval e,
    modify (λs, { s with locals := s.locals.insert idx (sigma.mk tp v)})
  | (action.event e) := event.eval e

-- FIXME: check pattern.context |- environment
def pattern.eval (p : pattern) (e : environment) (s : system_state) : except string system_state :=
  -- only machine_state is preserved across instructions
  let st := { evaluator_state.init s with environment := e }
  in do (_, s') <- evaluator.run (monad.mapm' action.eval p.actions) st, return s'.system_state

end with_nat_env

end x86

