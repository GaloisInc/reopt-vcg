
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

private def ppHexAtWidthAux : 
List Char → 
-- ^ Accumulator of characters.
Nat → 
-- ^ Width of printed hex string (sans the `0x` prefix).
Nat → 
-- ^ Nat to convert to hex.
String
| prev, 0, _ => prev.asString
| prev, (Nat.succ w), x =>
  let c := (Nat.land x 0xf).digitChar;
  ppHexAtWidthAux (c::prev) w (Nat.shiftr x 4)


/-- Pretty-print Nat in hexadecimal with a `0x` prefix 
    at the specified width (i.e., with leading zeroes
    if necessary). Notes:
    + The width does not include the `0x` prefix;
    + If the number is too large to be printed
      at the specified width then the number's
      more significant hexadecimal digits will
      be truncated to fit the width. --/
protected def ppHexAtWidth (n width:Nat) : String :=
"0x" ++ (ppHexAtWidthAux [] width n)

protected def ppHexAux : List Char → Nat → Nat → String
| prev, 0, _ => prev.asString
| prev, w, 0 => prev.asString
| prev, (Nat.succ w), x =>
  let c := (Nat.land x 0xf).digitChar;
  ppHexAux (c::prev) w (Nat.shiftr x 4)

/-- Pretty-print Nat in hexadecimal with a `0x` prefix. --/
protected def ppHex (v : Nat) : String := 
  if v = 0 then "0x0" else "0x" ++ Nat.ppHexAux [] v v -- the first v is just for termination

private def hexCharToNat : Char → Option Nat
| '0' => Option.some 0
| '1' => Option.some 1
| '2' => Option.some 2
| '3' => Option.some 3
| '4' => Option.some 4
| '5' => Option.some 5
| '6' => Option.some 6
| '7' => Option.some 7
| '8' => Option.some 8
| '9' => Option.some 9
| 'a' => Option.some 10
| 'A' => Option.some 10
| 'b' => Option.some 11
| 'B' => Option.some 11
| 'c' => Option.some 12
| 'C' => Option.some 12
| 'd' => Option.some 13
| 'D' => Option.some 13
| 'e' => Option.some 14
| 'E' => Option.some 14
| 'f' => Option.some 15
| 'F' => Option.some 15
| _ => Option.none


private def fromHexStringAux : Nat → List Char → Option Nat
| n, [] => Option.some n
| n, (c::cs) => do
  cn ← hexCharToNat c;
  fromHexStringAux ((n * 16) + cn) cs


protected def fromHexString (str:String) : Option Nat :=
if str.take 2 == "0x" && str.length > 2
then fromHexStringAux 0 (str.drop 2).toList
else Option.none

end Nat
