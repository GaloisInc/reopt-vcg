
-- Missing stuff
namespace Nat

def shiftl (v : ℕ) (n : ℕ) := v * 2 ^ n
def shiftr (v : ℕ) (n : ℕ) := v / 2 ^ n
def bodd (n : ℕ) : Bool := (n % 2) = 1
def ldiff : ℕ → ℕ → ℕ := bitwise (λ a b, a && not b)
def lxor  : ℕ → ℕ → ℕ := bitwise (λ a b, xor a b)

-- Copied
def test_bit (m n : ℕ) : Bool := bodd (shiftr m n)


end Nat
