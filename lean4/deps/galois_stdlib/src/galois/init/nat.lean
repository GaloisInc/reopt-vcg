
-- Missing stuff
namespace Nat

def shiftl (v : Nat) (n : Nat) := v * 2 ^ n
def shiftr (v : Nat) (n : Nat) := v / 2 ^ n
def bodd (n : Nat) : Bool := (n % 2) = 1
def ldiff : Nat → Nat → Nat := bitwise (λ a b => a && not b)
def lxor  : Nat → Nat → Nat := bitwise (λ a b => xor a b)

-- Copied
def test_bit (m n : Nat) : Bool := bodd (shiftr m n)


end Nat
