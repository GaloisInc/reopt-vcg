
-- import decodex86
import instruction

def main (xs : List String) : IO UInt32 := 
  let bs  := xs.map (λ(s : String), UInt8.ofNat (String.toNat s)) in 
  let arr := bs.toByteArray in do
    (match decodex86.decode arr 0 with
     | (Sum.inl e) := IO.println "error"
     | (Sum.inr i) := IO.println (repr i)),
    pure 0

