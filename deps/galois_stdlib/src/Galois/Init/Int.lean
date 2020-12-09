import Galois.Init.Nat

namespace Int



protected
def pow (v : Int) (n : Nat) : Int 
  := (if Nat.bodd n ∧ v < 0 then (-1) else 1) * (Int.ofNat (v.natAbs ^ n))

instance intPow : HPow Int Nat Int := ⟨Int.pow⟩

def shiftl (v : Int) (n : Nat) := v * 2 ^ n
def shiftr (v : Int) (n : Nat) := v / 2 ^ n

end Int
