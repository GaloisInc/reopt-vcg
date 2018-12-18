-- Evaluend qates actions in an environment.
import .bitvec
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

namespace machine_state

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
  { simp [option.bind], intros, apply exists.intro v, simp, assumption }
end

lemma list.mmap.length_at_option {a b : Type} {f : a -> option b} : Π{xs : list a} {ys : list b},
  list.mmap f xs = some ys -> xs.length = ys.length :=
begin
  intros,
  induction xs generalizing ys,
  { simp [list.mmap, option_t.pure, return, pure] at a_1, rw <- a_1, refl},
  { simp, simp [list.mmap, bind, option.bind] at a_1, 
    have H := option.bind.is_some a_1, destruct H, intros, 
    destruct h, simp, intros, have H' := option.bind.is_some right, destruct H', simp, intros, 
    destruct h_1, intros, rw (xs_ih left_1),
    simp [return, pure] at right_1, rw <- right_1, simp 
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

def split_word : Π{n : ℕ}, bitvec (8 * n) -> list (bitvec 8) -- array n ...
  | 0             _  := []
  | (nat.succ n)  bv := 
    let pf := calc 8   ≤ 8 * 1            : by dec_trivial_tac
                   ... ≤ 8 * (nat.succ n) : begin apply nat.mul_le_mul_left, apply nat.succ_le_succ, apply nat.zero_le end
    in let v := bitvec.split_at' pf bv in v.snd :: split_word v.fst

lemma split_word_zero {n:ℕ} {x: bitvec (n * 0) }: @split_word 0 x = [] :=
  by simp [split_word]

def concat_word : Π{n : ℕ} ( bs : list (bitvec n) ), bitvec (n * bs.length) := sorry

def store_word {n : ℕ} (s : machine_state) (addr : machine_word) (b : bitvec (8 * n)) : machine_state := 
  store_bytes addr (split_word b) s

def read_word (s : machine_state) (addr : machine_word) (n : ℕ) : option (bitvec (8 * n)) :=
begin
  intros, 
  let bs := (read_bytes s addr n),
  have H : bs = read_bytes s addr n := rfl,
  cases (read_bytes s addr n),
  {exact none},
  {simp [bs] at H, have rbl := read_bytes_length H, have r := concat_word val, 
   rw rbl at r, exact (some r) 
  }
end  

end machine_state

inductive arg_value 
  | natv : ℕ -> arg_value
  | bv  (n : ℕ) : bitvec n -> arg_value -- Do we always have n?
  | reg (tp : type) : reg tp -> arg_value

inductive value : type -> Type
  | bv {n : ℕ} : bitvec n -> value (bv n)
  | bit : bool -> value bit

def environment := list arg_value

structure evaluator_state : Type :=
  (machine_state : machine_state)
  (environment : environment) -- read only, but reading can fail
  (locals : rbmap ℕ (sigma value))

-- Monad for evaluating with failure
@[reducible]
def evaluator := except_t string (state evaluator_state)

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
       | (some (sigma.mk tp' v)) :=
         if H : tp' = tp
         then return (eq.rec v H)
         else throw "local_at_idx: arg type mismatch"
       | none     := throw "local_at_idx: no arg at idx"
     end

-- Replaces the lower n bits of the second argument with those from the first.
def inject_subvec {n m : ℕ} (H : n ≤ m . dec_trivial_tac) (b : bitvec n) (b' : bitvec m) : bitvec m :=
  bitvec.cong (nat.sub_add_cancel H)
              (bitvec.append (bitvec.split_at' H b').fst b)

namespace reg

def inject : Π(rtp : gpreg_type), bitvec rtp.width -> machine_word -> machine_word
  | gpreg_type.reg32 bv _   := bitvec.append (bitvec.zero 32) bv
  | gpreg_type.reg8h bv old := 
    let upper48 := (@bitvec.split_at' _ 16 (begin dec_trivial_tac end) old).fst in
    let lower8  := (@bitvec.split_at' _ 8  (begin dec_trivial_tac end) old).snd
    in bitvec.cong (begin dec_trivial_tac end) (bitvec.append upper48 (bitvec.append bv lower8))
  | rtp              bv old := inject_subvec (begin cases rtp; dec_trivial_tac end) bv old

def project : Π(rtp : gpreg_type), machine_word -> bitvec rtp.width
  | gpreg_type.reg8h bv := 
    let lower16 := (@bitvec.split_at' _ 16 (by dec_trivial_tac) bv).snd 
    in (@bitvec.split_at' _ 8  (by dec_trivial_tac) lower16).fst
  | rtp              bv := (@bitvec.split_at' _ rtp.width (begin cases rtp; dec_trivial_tac end) bv).snd


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

namespace arg_value

-- Can fail if types mismatch
def to_value : arg_value -> Π(tp : type), evaluator (value tp)
  | (arg_value.natv _)  _ := throw "to_value: natv"
  | (arg_value.bv n b)   (base (base_type.bv (nat_expr.lit m))) := 
        if H : n = m
        then return (value.bv (bitvec.cong H b))
        else throw "to_value: nat size mismatch"
  | (arg_value.bv n b)   _ := throw "to_value: Non-lit type"
  | (arg_value.reg tp r) tp' := 
         if H : tp = tp'
         then eq.rec r.read H
         else throw "to_value: reg type mismatch"

def set_value : arg_value -> Π{tp : type}, value tp -> evaluator unit
  | (natv _) _ _ := throw "set_value: nat"
  -- is an address
  | (bv 64 addr) (base (base_type.bv _)) (@value.bv n bytes) := 
    if H : n % 8 = 0 
    then let pf := calc n   = n % 8 + 8 * (n / 8) : eq.symm (nat.mod_add_div n 8)
                        ... = 8 * (n / 8) : by simp [H]
         in modify (λs, { s with machine_state := s.machine_state.store_word addr (bitvec.cong pf bytes) })
    else throw "set_value: value size not a mutiple of 8"
  | (bv n b)   _   _ := throw "arg_value.set_value: addr isn't 64 bits"
  | (reg tp r) tp' v :=
    if H : tp' = tp
    then r.set (eq.rec v H)
    else throw "assert_arg_type: reg type mismatch"

end arg_value

namespace addr

def read : Π{n : ℕ}, addr n -> evaluator (value (bv (8 * n)))
  | n (addr.arg idx) := do 
      av <- arg_at_idx idx,
      match av with 
        | (arg_value.bv 64 addr) := do s <- get, 
                                       match s.machine_state.read_word addr n with
                                         | none := throw "addr.read: no bytes at addr" 
                                         | (some w) := return (value.bv w)
                                       end
        | _                      := throw "addr.read: not a 64-bit bitvecor"
      end

def set : Π{n : ℕ}, addr n -> value (bv (8 * n)) -> evaluator unit
  | n (addr.arg idx) (value.bv bytes) := do 
      av <- arg_at_idx idx,
      match av with 
        | (arg_value.bv 64 addr) := modify (λs, { s with machine_state := s.machine_state.store_word addr bytes })
        | _                      := throw "addr.set: not a 64-bit bitvecor"
      end
    
end addr

namespace lhs

def set : Π{tp : type}, lhs tp -> value tp -> evaluator unit
  | ._ (reg r) v      := r.set v
  | ._ (addr a) v     := a.set v
  | ._ (arg idx _tp) v := do av <- arg_at_idx idx, av.set_value v -- fixme: we ignore tp here?
  | ._ (streg idx) v  := throw "lhs.set: unsupported FP write"

def read : Π{tp : type}, lhs tp -> evaluator (value tp)
  | ._ (reg r)       := r.read
  | ._ (addr a)      := a.read
  | ._ (arg idx tp)  := do av <- arg_at_idx idx, av.to_value tp
  | ._ (streg idx)   := throw "lhs.read: unsupported FP read"

end lhs

namespace prim

def eval : Π{tp : type}, prim tp -> evaluator (value tp)
  | ._ zero        := return (value.bit false)
  | ._ one         := return (value.bit true)
  | ._ (bvnat (nat_expr.lit w) (nat_expr.lit n)) := return (value.bv (bitvec.of_nat w n))
  | _ _          := throw "prim.eval: non-fully applied prim"

def 

end prim

namespace expression

def eval : Π{tp : type}, expression tp -> evaluator (value tp)
  | ._ (primitive p) := p.eval
  | ._ (app f a) := throw "eval: app"
  | ._ (get l)   := l.read
  -- Return the expression in the local variable at the given index.
  | ._ (get_local (nat_expr.lit idx) tp) := local_at_idx idx tp -- fixme: why nat_expr here over nat?
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
end x86

