-- Evaluates actions in an environment.
import galois.data.bitvec
import x86_semantics.common
import .tactic
import tactic.find

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

end type
end mc_semantics


namespace x86

open mc_semantics
open mc_semantics.type

@[reducible]
def machine_word := bitvec 64

namespace reg

def inject : Π(rtp : gpreg_type), bitvec rtp.width -> machine_word -> machine_word
  | gpreg_type.reg32 b _   := bitvec.append (bitvec.zero 32) b
  | gpreg_type.reg8h b old := old.set_bits 48 b (of_as_true trivial)
  | rtp              b old := old.set_bits (64 - rtp.width) b (begin cases rtp; dec_trivial_tac end)

def project : Π(rtp : gpreg_type), machine_word -> bitvec rtp.width
  | gpreg_type.reg8h b := b.get_bits 48 8 (by dec_trivial_tac)
  | rtp              b := b.get_bits (64 - rtp.width) rtp.width (begin cases rtp; dec_trivial_tac end)

end reg

def memory := rbmap machine_word (bitvec 8) (bitvec.ult) -- FIXME: 8?

structure machine_state : Type :=
  (mem    : memory)
  (gpregs : array 16 machine_word)
  (flags  : array 32 bool)
  (ip     : machine_word)

namespace machine_state

-- Constructs an empty machine state, with 0 where we need a value.
def empty : machine_state := 
  { mem    := mk_rbmap machine_word (bitvec 8) (bitvec.ult)
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

def store_bytes (addr : machine_word) (bs : list (bitvec 8)) (s : machine_state) : machine_state := 
  { s with mem := (list.foldl (λ(v : memory × machine_word) b, (rbmap.insert v.fst v.snd b, v.snd + 1)) (s.mem, addr) bs).fst }

-- [0 ..< x]
def upto0_lt : Π(m : ℕ), list ℕ
  | 0            := []
  | (nat.succ n) := upto0_lt n ++ [n]

namespace upto0_lt

lemma length_is_n : Π{n : ℕ}, (upto0_lt n).length = n :=
begin
  intros n, 
  induction n,
  { refl },
  { simp [upto0_lt, n_ih] }
end

end upto0_lt

lemma {u v} option.bind.is_some {a : Type u} {b : Type v} {v : option a} {f : a -> option b} {x : b}:
  option.bind v f = some x -> (∃v', v = some v' ∧ f v' = some x) :=
begin
  cases v,
  { simp [option.bind] },
  { simp [option.bind] }
end

lemma list.mmap.length_at_option {a b : Type} {f : a -> option b} : Π{xs : list a} {ys : list b},
  list.mmap f xs = some ys -> xs.length = ys.length :=
begin
  intros,
  induction xs generalizing ys,
  { simp [list.mmap, option_t.pure, return, pure] at a_1, rw <- a_1, refl},
  { simp, simp [list.mmap, bind, option.bind] at a_1, 
    destruct a_1, intros, 
    destruct h, simp, intros, simp [return, pure] at a_3,
    rw (xs_ih a_2), rw <- a_3, simp [list.length]
  }
end

def read_bytes (s : machine_state) (addr : machine_word) (n : ℕ) : option (list (bitvec 8)) :=
  monad.mapm (λn, s.mem.find (addr + bitvec.of_nat 64 n)) (upto0_lt n)

lemma read_bytes_length {s : machine_state} {addr : machine_word} {n : ℕ} {bs : list (bitvec 8)}
  : read_bytes s addr n = some bs -> bs.length = n :=
begin
  intros H,
  simp [read_bytes] at H,
  have H' := list.mmap.length_at_option H,
  simp [upto0_lt.length_is_n] at H',
  rw H'
end

def store_word {n : ℕ} (s : machine_state) (addr : machine_word) (b : bitvec (8 * n)) : machine_state := 
  store_bytes addr (b.split_list 8) s

def read_word (s : machine_state) (addr : machine_word) (n : ℕ) : option (bitvec (8 * n)) :=
  (λbs, bitvec.concat_list bs (8 * n)) <$> read_bytes s addr n

def print_regs (s : machine_state) : string :=
  let lines := list.zip_with (λn r, n ++ ": " ++ repr r ++ "\n") reg.r64_names s.gpregs.to_list 
  in string.join lines

end machine_state

-- Argument to functions in value, gets around the positivity
-- requirement on inductive types.
-- inductive value_fnarg : type -> Type
--   | bv {n : ℕ} : bitvec n -> value_fnarg (bv n)
--   | bit : bool -> value_fnarg bit

-- inductive value : type -> Type
--   | bv {n : ℕ} : bitvec n -> value (bv n)
--   | bit : bool -> value bit
--   | func  {tp tp' : type} : (value tp -> value tp') -> value (fn tp tp')

inductive arg_lval
  | reg {} {tp : type} : reg tp -> arg_lval
  | memloc (width : ℕ) (addr : machine_word) : arg_lval

namespace arg_lval

def repr : arg_lval -> string
  | (reg r)             := r.repr
  | (memloc width addr) := has_repr.repr addr ++ "@" ++ has_repr.repr width

instance arg_lval_repr : has_repr arg_lval := ⟨repr⟩

end arg_lval

section with_nat_env

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
  | (vec w tp) := unit -- FIXME
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
  (machine_state : machine_state)
  (environment : environment) -- read only, but reading can fail
  (locals : rbmap ℕ (sigma value))

-- namespace evaluator_state

def evaluator_state.empty : evaluator_state := 
  { machine_state := machine_state.empty
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

def evaluator.read_memory_at (addr : machine_word) (n : ℕ) : evaluator (bitvec (8 * n)) := do
    s <- get, 
    match s.machine_state.read_word addr n with
    | none := throw "read_memory_at: no bytes at addr" 
    | (some w) := return w
    end

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
  
def reg.set : Π{tp : type}, reg tp -> value tp -> evaluator unit
  | ._ (reg.concrete_gpreg idx rtp) b := 
    modify (λ(s : evaluator_state), { s with machine_state := machine_state.update_gpreg idx (reg.inject rtp b) s.machine_state })
  | ._ (reg.concrete_flagreg idx)   b := 
    modify (λ(s : evaluator_state), { s with machine_state := machine_state.update_flag idx (λ_, b) s.machine_state })

def reg.from_state : Π{tp : type}, reg tp -> machine_state -> value tp
  | ._ (reg.concrete_gpreg idx rtp) s := reg.project rtp (s.get_gpreg idx)
  | ._ (reg.concrete_flagreg idx)   s := s.get_flag idx

def reg.read {tp : type} (r : reg tp) : evaluator (value tp) := do s <- get, return (reg.from_state r s.machine_state)

-- namespace arg_lval 

def arg_lval.to_value' {m} [monad m] [monad_except string m] 
  (s : machine_state)
  : arg_lval -> Π(tp : type), m (value tp)
  | (@arg_lval.reg tp r) tp' := value.type_check tp (reg.from_state r s) tp'
  | (arg_lval.memloc width addr) tp' :=
    match s.read_word addr (width / 8) with
    | none := throw "arg_lval.to_value': no bytes at addr" 
    | (some w) := value.type_check (bv (8 * (width / 8))) w tp'
    end

def arg_lval.to_value : arg_lval -> Π(tp : type), evaluator (value tp)
  | (@arg_lval.reg tp r) tp' := do v <- reg.read r,
                                   value.type_check tp v tp'
  | (arg_lval.memloc width addr) tp' := do
    v <- evaluator.read_memory_at addr (width / 8),
    value.type_check (bv (8 * (width / 8))) v tp'

def arg_lval.set_value : arg_lval -> Π{tp : type}, value tp -> evaluator unit
  | (@arg_lval.reg tp r) tp' v := do v' <- value.type_check _ v tp,
                                     reg.set r v'
  | (arg_lval.memloc width addr) (bv (nat_expr.lit n)) bytes :=  -- FIXME: use nat_expr.eval instead of assuming lit
    if H : n = 8 * (width / 8)
    then modify (λs, { s with machine_state := s.machine_state.store_word addr (bitvec.cong H bytes) })
    else throw "arg_lval.set_value: width mismatch"
  | _ _ _ := throw "arg_lval.set_value: malformed set"

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

def addr.read : Π{n : ℕ}, addr n -> evaluator (value (bv (8 * n)))
  | n (addr.arg idx) := do 
      av <- evaluator.arg_at_idx idx,
      arg_value.to_value av (bv (8 * n)) -- FIXME: we should really check if this is a memloc first.
      -- w  <- av.read_memory_at n,
      -- return (value.bv w)

def addr.set : Π{n : ℕ}, addr n -> value (bv (8 * n)) -> evaluator unit
  | n (addr.arg idx) v := do 
      av <- evaluator.arg_at_idx idx, -- FIXME: we should really check if this is a memloc first.
      arg_value.set_value av v
    
def lhs.set : Π{tp : type}, lhs tp -> value tp -> evaluator unit
  | ._ (lhs.reg r) v      := reg.set r v
  | ._ (lhs.addr a) v     := addr.set a v
  | ._ (lhs.arg idx _tp) v := do av <- evaluator.arg_at_idx idx,
                                 -- fixme: we ignore tp here?
                                 arg_value.set_value av v
  | ._ (lhs.streg idx) v  := throw "lhs.set: unsupported FP write"

def lhs.read : Π{tp : type}, lhs tp -> evaluator (value tp)
  | ._ (lhs.reg r)       := reg.read r
  | ._ (lhs.addr a)      := addr.read a
  | ._ (lhs.arg idx tp)  := do av <- evaluator.arg_at_idx idx, 
                                  arg_value.to_value av tp
  | ._ (lhs.streg idx)   := throw "lhs.read: unsupported FP read"

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

section

local infixr `.→`:30 := fn

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

def prim.eval : Π{tp : type}, prim tp -> evaluator (value tp)
  -- `(add i)` returns the sum of two i-bit numbers.
  | ._ (prim.add i)        := return bitvec.add
  -- `(adc i)` returns the sum of two i-bit numbers and a carry bit.
  | ._ (prim.adc i)         := return (λx y b, bitvec.add x (bitvec.add y (bit_to_bitvec _ b)))
  -- `(mul i)` returns the product of two i-bit numbers.
  | ._ (prim.mul i)            := return bitvec.mul
  -- `(quot i)` returns the quotient of two i-bit numbers.
  -- | quot (i:ℕ) : prim (bv i .→ bv i .→ bv i)
  -- `(rem i)` returns the remainder of two i-bit numbers.
  -- | rem (i:ℕ) : prim (bv i .→ bv i .→ bv i)
  -- `(squot i)` returns the signed quotient of two i-bit numbers.
  -- | squot (i:ℕ) : prim (bv i .→ bv i .→ bv i)
  -- `(srem i)` returns the signed remainder of two i-bit numbers.
  -- | srem (i:ℕ) : prim (bv i .→ bv i .→ bv i)
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

  -- `(bsf i)` returns the index of least-significant bit that is 1.
  -- | bsf   (i:ℕ) : prim (bv i .→ bv i)
  -- `(bsr i)` returns the index of most-significant bit that is 1.
  -- | bsr   (i:ℕ) : prim (bv i .→ bv i)
  -- `(bswap i)` reverses the bytes in the bitvector.
  -- | bswap (i:ℕ) : prim (bv i .→ bv i)
  -- `zero` is the zero bit
  | ._ prim.bit_zero := return ff
  -- `one` is the one bit
  | ._ prim.bit_one := return tt
  -- `(eq tp)` returns `true` if two values are equal.
  -- | (eq (tp:type) : prim (tp .→ tp .→ bit)
  -- `(neq tp)` returns `true` if two values are not equal.
  -- | neq (tp:type) : prim (tp .→ tp .→ bit)
  -- `(neg tp)` Two's Complement negation.
  | ._ (prim.neg i) := return bitvec.neg
  -- `x87_fadd` adds two extended precision values using the flags in the x87 register.
  -- | x87_fadd : prim (x86_80 .→ x86_80 .→ x86_80)
  -- `float_to_x86_80` converts a float to an extended precision number (lossless)
  -- | float_to_x86_80  : prim (float .→ x86_80)
  -- `double_to_x86_80` converts a double to an extended precision number (lossless)
  -- | double_to_x86_80 : prim (double .→ x86_80)
  -- `bv_to_x86_80` converts a bitvector to an extended precision number (lossless)
  -- | bv_to_x86_80  (w : one_of [16,32]) : prim (bv w .→ x86_80)
  -- `bvnat` constructs a bit vector from a natural number.
  | ._ (prim.bv_nat w n) := return (bitvec.of_nat (eval_nat_expr w) (eval_nat_expr n))
  -- `(bvadd i)` adds two i-bit bitvectors.
  | ._ (prim.add i) := return bitvec.add
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

  | ._ (prim.uadc_overflows i) := return (λx y b, bitvec.ult (x + y + bit_to_bitvec (eval_nat_expr i) b) x)
  | ._ (prim.sadc_overflows i) := return (λx y b, bitvec.slt (x + y + bit_to_bitvec (eval_nat_expr i) b) x)
  | ._ (prim.and i) := return bitvec.and
  | ._ (prim.or i)  := return bitvec.or
  | ._ (prim.xor i) := return bitvec.xor
  | ._ (prim.shl i) := return (λx (y : bitvec (eval_nat_expr i)), bitvec.shl x y.to_nat)
  -- `(bvbit i)` interprets the second argument as a bit index and returns
  -- that bit from the first argument.
  | ._ (prim.bv_bit i) := return (λx (y : bitvec (eval_nat_expr i)), bitvec.nth x y.to_nat)
  | ._ (prim.complement i) := return bitvec.not
  | ._ (prim.cat i) := return (λx y, bitvec.cong
                                    (begin simp [eval_nat_expr, nat_expr.eval_default_mul_eq, nat_expr.eval, eval_default_2, two_mul], 
                                     end)
                                    (bitvec.append x y))
-- | bv_least_nibble (i:ℕ) : prim (bv i .→ bv 4)
  | ._ (prim.msb i) := return bitvec.msb
-- | least_byte (i:ℕ) : prim (bv i .→ bv 8)
-- | even_parity (i:ℕ) : prim (bv i .→ bit)
  | _  _             := throw "prim.eval: unimplemented prim"


end

def expression.eval : Π{tp : type}, expression tp -> evaluator (value tp)
  | ._ (expression.primitive p) := prim.eval p
  | ._ (expression.app f a) := (expression.eval f) <*> (expression.eval a)
  | ._ (expression.get l)   := lhs.read l
  -- Return the expression in the local variable at the given index.
  | ._ (expression.get_local idx tp) := evaluator.local_at_idx idx tp -- fixme: why nat_expr here over nat?


def evaluator.set_ip (new_ip : bitvec 64) : evaluator unit :=
  modify (λ(s : evaluator_state), 
          {s with machine_state := { s.machine_state with ip := new_ip}})

def event.eval : event -> evaluator unit
  | event.syscall := throw "syscall"
  | (event.unsupported msg) := throw ("event.eval: unsupported: " ++ msg)
  | event.pop_x87_register_stack := throw "pop_x87_register_stack"
  | (event.call addr) := do 
    new_ip <- expression.eval addr,
    evaluator.set_ip new_ip
  | (event.jmp addr) := do
    new_ip <- expression.eval addr,
    evaluator.set_ip new_ip
  | (event.branch c addr) := do
    new_ip <- expression.eval addr,
    b      <- expression.eval c,
    when b (evaluator.set_ip new_ip)
  | event.ret := throw "ret"
  | event.hlt := throw "halt"
  | (event.xchg addr1 addr2) := throw "xchg"

-- FIXME: move
-- Make a value for 'undefined', which means we just pick an arbitrary value.
def value.undef : Π (tp : type), value tp
  | (bv e) := bitvec.zero (eval_nat_expr e)
  | bit    := false
  | float  := () -- FIXME
  | double := () -- FIXME
  | x86_80 := () -- FIXME  
  | (vec w tp) := () -- FIXME
  | (fn arg res) := λ_, value.undef res

def action.eval : action -> evaluator unit
  | (action.set l e) := do v <- expression.eval e,
                           lhs.set l v
  | (action.set_cond l c e) := do
    b <- expression.eval c,
    v <- expression.eval e,
    when b (lhs.set l v)
  | (@action.set_undef tp l)    := lhs.set l (value.undef tp)
  | (@action.set_undef_cond tp l c) := do
    b <- expression.eval c,
    when b (lhs.set l (value.undef tp))
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
def pattern.eval (p : pattern) (e : environment) (s : machine_state) : except string machine_state :=
  -- only machine_state is preserved across instructions
  let st := { evaluator_state.empty with machine_state := s, environment := e } 
  in do (_, s') <- evaluator.run (monad.mapm' action.eval p.actions) st, return s'.machine_state

end with_nat_env

end x86

