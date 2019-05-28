import galois.init.nat

namespace Int



protected
def pow (v : Int) (n : ℕ) : Int 
  := (if Nat.bodd n ∧ v < 0 then (-1) else 1) * (Int.ofNat (v.natAbs ^ n))

instance intPow : HasPow Int ℕ := ⟨Int.pow⟩

def shiftl (v : Int) (n : ℕ) := v * 2 ^ n
def shiftr (v : Int) (n : ℕ) := v / 2 ^ n

end Int
