import Galois.Init.Nat

namespace Int

instance intPow : Pow Int Nat := ⟨Int.pow⟩

def shiftl (v : Int) (n : Nat) := v * 2 ^ n
def shiftr (v : Int) (n : Nat) := v / 2 ^ n

end Int
