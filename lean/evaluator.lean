-- Evaluates actions in an environment.
import galois.data.bitvec
import .common
import tactic.find

namespace x86

open mc_semantics
open mc_semantics.type

@[reducible]
def machine_word := bitvec 64

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

end machine_state

inductive value : type -> Type
  | bv {n : ℕ} : bitvec n -> value (bv n)
  | bit : bool -> value bit

namespace value

def repr : Π{tp : type}, value tp -> string
  | ._ (bv b)  := has_repr.repr b
  | ._ (bit b) := has_repr.repr b

instance value_repr {tp : type} : has_repr (value tp) := ⟨repr⟩

end value

inductive arg_lval 
  | reg {tp : type} : reg tp -> arg_lval
  | memloc (width : ℕ) (addr : machine_word) : arg_lval

namespace arg_lval

def repr : arg_lval -> string
  | (reg r)             := r.repr
  | (memloc width addr) := has_repr.repr addr ++ "@" ++ has_repr.repr width

instance arg_lval_repr : has_repr arg_lval := ⟨repr⟩

end arg_lval

-- Corresponding to the binder type, more or less.
inductive arg_value 
  | natv             : ℕ -> arg_value
  | lval             : arg_lval -> arg_value
  | rval {tp : type} : value tp -> arg_value

namespace arg_value

def repr : arg_value -> string 
  | (natv n) := n.repr
  | (lval l) := l.repr
  | (rval v)  := v.repr

instance arg_value_repr : has_repr arg_value := ⟨repr⟩

end arg_value

@[reducible]
def environment := list arg_value

structure evaluator_state : Type :=
  (machine_state : machine_state)
  (environment : environment) -- read only, but reading can fail
  (locals : rbmap ℕ (sigma value))

namespace evaluator_state

def empty : evaluator_state := 
  { machine_state := machine_state.empty
  , environment   := []
  , locals        := mk_rbmap ℕ (sigma value)
  }

end evaluator_state

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



/- Normalisation of types (containing nat_exprs) -/
namespace arg_value

def as_nat : arg_value -> option ℕ 
  | (natv n) := some n
  | _        := none

end arg_value

namespace nat_expr

def eval (e : environment) : nat_expr -> option ℕ 
  | (nat_expr.lit n)     := some n
  | (nat_expr.var idx)   := list.nth e idx >>= λa, a.as_nat
  | (nat_expr.add e1 e2) := (+) <$> (eval e1) <*> (eval e2) 
  | (nat_expr.sub e1 e2) := (λx y, x - y) <$> (eval e1) <*> (eval e2) 
  | (nat_expr.mul e1 e2) := (*) <$> (eval e1) <*> (eval e2) 
  | (nat_expr.div e1 e2) := (/) <$> (eval e1) <*> (eval e2) 

end nat_expr


namespace base_type

-- If evaluation of the expr fails, we return the original type.  
def normalise (e : environment) : base_type -> base_type
  | (base_type.bv expr) := 
    base_type.bv (match nat_expr.eval e expr with 
                 | none := expr
                 | (some n) := nat_expr.lit n
                 end)
  | t        := t
  
end base_type

namespace type

-- If evaluation of the expr fails, we return the original type.  
def normalise (e : environment) : type -> type
  | (base b)     := base (base_type.normalise e b)
  | (fn arg res) := fn (normalise arg) (normalise res)
  
def equiv (e : environment) (t1 : type) (t2 : type) : Prop :=
  normalise e t1 = normalise e t2

instance (e) : decidable_rel (equiv e) :=
  λa b, begin simp [equiv], apply_instance end

end type

namespace value

-- This allows us to resolve arith in nat_exprs
def type_check {tp : type} (v : value tp) (tp' : type) : evaluator (value tp') :=
  if H : tp = tp'
  then return (eq.rec v H)
  else throw "type_check: arg type mismatch"

end value

namespace evaluator

def run {a : Type} (m : evaluator a) (s : evaluator_state) : except string (a × evaluator_state) :=
  (m.run s)

def read_memory_at (addr : machine_word) (n : ℕ) : evaluator (bitvec (8 * n)) := do
    s <- get, 
    match s.machine_state.read_word addr n with
    | none := throw "read_memory_at: no bytes at addr" 
    | (some w) := return w
    end

def arg_at_idx (idx : ℕ) : evaluator arg_value :=
  do s <- get,
     match s.environment.nth idx with
       | (some a) := return a
       | none     := throw "evaluator.arg_at_idx: no arg at idx"
     end

-- We should factor out the type check, although it might depend on
-- the functor (value in this case) if we generalise equality
def local_at_idx (idx : ℕ) (tp : type) : evaluator (value tp) :=
  do s <- get,
     match s.locals.find idx with
     | (some (sigma.mk tp' v)) := v.type_check tp
     | none     := throw "local_at_idx: no arg at idx"
     end

def normalise_type (t : type) : evaluator type :=
  do s <- get,
     return (type.normalise s.environment t)

def type_as_bv : type -> evaluator ℕ
 | (type.base (base_type.bv (nat_expr.lit n))) := return n
 | _ := throw "type_as_bv: Not a lit BV"

end evaluator

  
namespace reg

def inject : Π(rtp : gpreg_type), bitvec rtp.width -> machine_word -> machine_word
  | gpreg_type.reg32 bv _   := bitvec.append (bitvec.zero 32) bv
  | gpreg_type.reg8h bv old := old.set_bits 48 bv (of_as_true trivial)
  | rtp              bv old := old.set_bits (64 - rtp.width) bv (begin cases rtp; dec_trivial_tac end)

def project : Π(rtp : gpreg_type), machine_word -> bitvec rtp.width
  | gpreg_type.reg8h bv := bv.get_bits 48 8 (by dec_trivial_tac)
  | rtp              bv := bv.get_bits (64 - rtp.width) rtp.width (begin cases rtp; dec_trivial_tac end)

def set : Π{tp : type}, reg tp -> value tp -> evaluator unit
  | ._ (concrete_gpreg idx rtp) (value.bv b) := 
    modify (λ(s : evaluator_state), { s with machine_state := machine_state.update_gpreg idx (inject rtp b) s.machine_state })
  | ._ (concrete_flagreg idx) (value.bit b) := 
    modify (λ(s : evaluator_state), { s with machine_state := machine_state.update_flag idx (λ_, b) s.machine_state })

def read : Π{tp : type}, reg tp -> evaluator (value tp)
  | ._ (concrete_gpreg idx rtp) := do s <- get,
                                      return (value.bv (project rtp (s.machine_state.get_gpreg idx)))
  | ._ (concrete_flagreg idx)   := do s <- get,
                                      return (value.bit (s.machine_state.get_flag idx))

end reg

namespace arg_lval 

def to_value : arg_lval -> Π(tp : type), evaluator (value tp)
  | (@reg tp r) tp' := 
    if H : tp = tp'
    then eq.rec r.read H
    else throw "to_value: reg type mismatch"
  | (memloc width addr) tp' := do
    v <- value.bv <$> evaluator.read_memory_at addr (width / 8),
    v.type_check tp'

def set_value : arg_lval -> Π{tp : type}, value tp -> evaluator unit
  | (@reg tp r) tp' v := do v' <- v.type_check tp,
                            r.set v'
  | (memloc width addr) (base (base_type.bv _)) (@value.bv n bytes) := 
    if H : n = 8 * (width / 8)
    then modify (λs, { s with machine_state := s.machine_state.store_word addr (bitvec.cong H bytes) })
    else throw "arg_lval.set_value: width mismatch"
  | _ _ _ := throw "arg_lval.set_value: malformed set"

end arg_lval 

namespace arg_value

-- def read_memory_at (av : arg_value) (n : ℕ) : evaluator (bitvec (8 * n)) :=
--   match av with 
--   | (@arg_value.bv 64 addr) := 
--   | _                      := throw "addr.read: not a 64-bit bitvecor"
--   end

-- Can fail if types mismatch
def to_value : arg_value -> Π(tp : type), evaluator (value tp)
  | (natv _) _ := throw "to_value: natv"
  | (lval l) tp := l.to_value tp
  | (rval v) tp := v.type_check tp

def set_value : arg_value -> Π{tp : type}, value tp -> evaluator unit
  | (lval l) tp v := l.set_value v
  | _ _ _ := throw "arg_value.set_value: not an lvalue"

end arg_value

namespace addr

def read : Π{n : ℕ}, addr n -> evaluator (value (bv (8 * n)))
  | n (addr.arg idx) := do 
      av <- evaluator.arg_at_idx idx,
      av.to_value (bv (8 * n)) -- FIXME: we should really check if this is a memloc first.
      -- w  <- av.read_memory_at n,
      -- return (value.bv w)

def set : Π{n : ℕ}, addr n -> value (bv (8 * n)) -> evaluator unit
  | n (addr.arg idx) v := do 
      av <- evaluator.arg_at_idx idx, -- FIXME: we should really check if this is a memloc first.
      av.set_value v
    
end addr

namespace lhs

def set : Π{tp : type}, lhs tp -> value tp -> evaluator unit
  | ._ (reg r) v      := r.set v
  | ._ (addr a) v     := a.set v
  | ._ (arg idx _tp) v := do av <- evaluator.arg_at_idx idx, av.set_value v -- fixme: we ignore tp here?
  | ._ (streg idx) v  := throw "lhs.set: unsupported FP write"

def read : Π{tp : type}, lhs tp -> evaluator (value tp)
  | ._ (reg r)       := r.read
  | ._ (addr a)      := a.read
  | ._ (arg idx tp)  := do av <- evaluator.arg_at_idx idx, av.to_value tp
  | ._ (streg idx)   := throw "lhs.read: unsupported FP read"

end lhs

namespace prim

def eval : Π{tp : type}, prim tp -> evaluator (value tp)
  | ._ zero        := return (value.bit false)
  | ._ one         := return (value.bit true)
  | ._ (bvnat (nat_expr.lit w) (nat_expr.lit n)) := return (value.bv (bitvec.of_nat w n))
  | _ _          := throw "prim.eval: non-fully applied prim"

end prim

namespace expression

def eval : Π{tp : type}, expression tp -> evaluator (value tp)
  | ._ (primitive p) := p.eval
  | ._ (app f a) := throw "eval: app"
  | ._ (get l)   := l.read
  -- Return the expression in the local variable at the given index.
  | ._ (get_local (nat_expr.lit idx) tp) := evaluator.local_at_idx idx tp -- fixme: why nat_expr here over nat?
  | _ _ := throw "expression.eval: missing case"

end expression

namespace action

def eval : action -> evaluator unit
  | (set l e) := do v <- e.eval,
                    l.set v
  | (@local_def tp (nat_expr.lit idx) e) := do 
    v <- e.eval,
    modify (λs, { s with locals := s.locals.insert idx (sigma.mk tp v)})
  | (event e) := throw "event"
  | (mk_undef l) := throw "mk_undef"
  | _ := throw "action.eval: missing case"

end action

namespace pattern

-- FIXME: check pattern.context |- environment
def eval (p : pattern) (e : environment) : evaluator unit := do
  -- only machine_state is preserved across instructions
  modify (λs, { evaluator_state.empty with machine_state := s.machine_state, environment := e }),
  monad.mapm' action.eval p.actions,
  return ()

end pattern

end x86

