
-- Missing stuff
namespace Nat

def shiftl (v : Nat) (n : Nat) := v * 2 ^ n
def shiftr (v : Nat) (n : Nat) := v / 2 ^ n
def bodd (n : Nat) : Bool := (n % 2) = 1
def ldiff : Nat → Nat → Nat := bitwise (λ a b => a && not b)
def lxor  : Nat → Nat → Nat := bitwise (λ a b => xor a b)

-- Copied
def test_bit (m n : Nat) : Bool := bodd (shiftr m n)


private def to_hex_with_leading_zeros : List Char → Nat → Nat → String
| prev, 0, _ => prev.asString
| prev, (Nat.succ w), x =>
  let c := (Nat.land x 0xf).digitChar;
  to_hex_with_leading_zeros (c::prev) w (Nat.shiftr x 4)

private def to_hex' : List Char → Nat → Nat → String
| prev, 0, _ => prev.asString
| prev, w, 0 => prev.asString
| prev, (Nat.succ w), x =>
  let c := (Nat.land x 0xf).digitChar;
  to_hex' (c::prev) w (Nat.shiftr x 4)

  
--- Print Nat as hex with specified width
protected def pp_hex_at_width (n width:Nat) : String :=
"0x" ++ (to_hex' [] width n)


end Nat
