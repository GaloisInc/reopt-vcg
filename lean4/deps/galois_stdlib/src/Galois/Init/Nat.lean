
-- Missing stuff
namespace Nat

def shiftl (v : Nat) (n : Nat) := v * 2 ^ n
def shiftr (v : Nat) (n : Nat) := v / 2 ^ n
def bodd (n : Nat) : Bool := (n % 2) = 1
def ldiff : Nat → Nat → Nat := bitwise (λ a b => a && not b)
def lxor  : Nat → Nat → Nat := bitwise (λ a b => xor a b)

-- Copied
def test_bit (m n : Nat) : Bool := bodd (shiftr m n)

protected
def upto0_lt_helper : ∀(m : Nat), List Nat -> List Nat
  | 0,            acc => acc
  | (Nat.succ n), acc => upto0_lt_helper n (n :: acc)

def upto0_lt (m : Nat) : List Nat := Nat.upto0_lt_helper m []

namespace upto0_lt

-- lemma length_is_n' : ∀{n : Nat} {acc : list Nat}
--   , (upto0_lt_helper n acc).length = n + acc.length :=
-- begin
--   intros n, 
--   induction n,
--   { intro, simp, refl },
--   { intro, simp [upto0_lt_helper, n_ih]
--   , simp [nat.succ_add_eq_succ_add, nat.add_assoc, nat.add_comm, nat.add_left_comm] }
-- end

-- lemma length_is_n : ∀{n : Nat}, (upto0_lt n).length = n :=
-- begin
--   intros n, 
--   unfold upto0_lt, 
--   apply length_is_n',
-- end

end upto0_lt

end Nat
