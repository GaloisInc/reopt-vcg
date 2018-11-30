-- Evaluates actions in an environment.
import data.bitvec
import .common
import tactic.find

def bitvec.take (m : ℕ) {n : ℕ} (b : bitvec n) : bitvec (min m n) := vector.take m b
def bitvec.drop (m : ℕ) {n : ℕ} (b : bitvec n) : bitvec (n - m)   := vector.drop m b

#find _ + _ ≤ _

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
  | (nat.succ n)  bv := sorry -- bitvec.cong (begin simp [min] end) (bitvec.take 8 bv) :: split_word n (bitvec.drop 8 bv)

def store_word {n : ℕ} (addr : machine_word) (b : bitvec (8 * n)) (s : machine_state) : machine_state := 
  store_bytes addr (split_word b) s

end machine_state

inductive arg_value 
  | nat : ℕ -> arg_value
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

-- Replaces the lower n bits of the second argument with those from the first.
def inject_subvec {n m : ℕ} (H : n ≤ m . dec_trivial_tac) (b : bitvec n) (b' : bitvec m) : bitvec m :=
  bitvec.cong (begin simp [H, min, nat.sub_le, nat.add_sub_of_le] end) (bitvec.append (bitvec.take (m - n) b') b)

namespace reg

def inject : Π(rtp : gpreg_type), bitvec rtp.width -> machine_word -> machine_word
  | gpreg_type.reg32 bv _   := bitvec.append (bitvec.zero 32) bv
  | gpreg_type.reg8h bv old := @bitvec.append 48 16 (bitvec.take 48 old) 
                                                    (bitvec.append bv (bitvec.drop 56 old))
  | rtp              bv old := inject_subvec (begin cases rtp; dec_trivial_tac end) bv old

def set : Π{tp : type}, reg tp -> value tp -> evaluator unit
  | ._ (concrete_gpreg idx rtp) (value.bv b) := 
    modify (λ(s : evaluator_state), { s with machine_state := machine_state.update_gpreg idx (inject rtp b) s.machine_state })
  | ._ (concrete_flagreg idx) (value.bit b) := 
    modify (λ(s : evaluator_state), { s with machine_state := machine_state.update_flag idx (λ_, b) s.machine_state })

def get : Π{tp : type}, reg tp -> evaluator (value tp)
  | ._ (concrete_gpreg idx _) := do s <- get,
                                    return (s.machine_state.get_flag 
    modify (λ(s : evaluator_state), { s with machine_state := machine_state.update_gpreg idx (inject rtp b) s.machine_state })
  | ._ (concrete_flagreg idx) (value.bit b) := 
    modify (λ(s : evaluator_state), { s with machine_state := machine_state.update_flag idx (λ_, b) s.machine_state })


end reg

namespace arg_value

-- Can fail if types mismatch
def to_value : arg_value -> Π(tp : type) -> evaluator (value tp)
  | (nat _)  _ := throw "assert_arg_type: nat"
  | (bv n b)   (base (base_type.bv (nat_expr.lit m))) := 
        if n ≠ m 
        then throw "assert_arg_type: nat size mismatch"
        else return (bv b)
  | (reg tp) tp' := 
         if tp ♩ tp'
         then throw "assert_arg_type: reg type mismatch"
         else do s <- get,
                 s.machine_state.

end arg_value

-- can fail
def get_arg (idx : arg_idx) (tp : type) : evaluator (value tp) := do
  s <- get,
  match s.environment.nth idx with
    | none     := throw "Couldn't find index"
    | (some v) := do assert_arg_type v tp,
                     return 
  



namespace addr

def set : Π{tp : base_type}, addr tp -> value tp -> evaluator unit
  | ._ (arg idx) v := do
    
    modify (λ(s : evaluator_state), { s with machine_state :=  machine_state.store_word  })
  
 
end addr

namespace lhs




def set : Π{tp : type}, lhs tp -> value tp -> evaluator unit
  | ._ (reg r) v      := reg.set r v
  | ._ (addr a) v     := sorry
  | ._ (arg idx tp) v := sorry
  | ._ (streg idx) v  := sorry

end lhs

namespace expression

def eval : Π{tp : type}, expression tp -> evaluator (value tp)
  | ._ (primitive o) : expression rtp
-- Apply a function to an argument.
| app {rtp:type} {tp:type} (f : expression (type.fn tp rtp)) (a : expression tp) : expression rtp
  -- Get the expression associated with the assignable expression.
| get {tp:type} (l:lhs tp) : expression tp
  -- Return the expression in the local variable at the given index.
| get_local (idx:ℕ) (tp:type) : expression tp

  | ._ 

end expression


namespace action

def eval : action -> evaluator unit
  | (set l v) := sorry
  | (local_def idx v) := sorry
  | (event e) := sorry
  | (mk_undef l) := sorry

end action

end x86
