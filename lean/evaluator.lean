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

def split_word : Π{n : ℕ}, bitvec (8 * n) -> list (bitvec 8) -- array n ...
  | 0             _  := []
  | (nat.succ n)  bv := 
    let pf := calc 8   ≤ 8 * 1            : by dec_trivial_tac
                   ... ≤ 8 * (nat.succ n) : begin apply nat.mul_le_mul_left, apply nat.succ_le_succ, apply nat.zero_le end
    in let v := bitvec.split_at' pf bv in v.snd :: split_word v.fst

def store_word {n : ℕ} (s : machine_state) (addr : machine_word) (b : bitvec (8 * n)) : machine_state := 
  store_bytes addr (split_word b) s

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
  (locals : rbmap ℕ (bitvec 64))

-- Monad for evaluating with failure
@[reducible]
def evaluator := except_t string (state evaluator_state)

def arg_at_idx (idx : ℕ) : evaluator arg_value :=
  do s <- get,
     match s.environment.nth idx with
       | (some a) := return a
       | none     := throw "evaluator.arg_at_idx: no arg at idx"
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
  | ._ (streg idx)   := throw "lhs.set: unsupported FP write"

end lhs

namespace expression

def eval : Π{tp : type}, expression tp -> evaluator (value tp)
  | ._ (primitive o) := throw "eval: raw primitive"
  | ._ (app f a) := throw "eval: app"
  | ._ (get l)   := l.read
  -- Return the expression in the local variable at the given index.
  | ._ (get_local idx tp) := sorry

end expression

namespace action

def eval : action -> evaluator unit
  | (set l v) := sorry
  | (local_def idx v) := sorry
  | (event e) := sorry
  | (mk_undef l) := sorry

end action

