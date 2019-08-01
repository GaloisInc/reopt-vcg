namespace Char

def isHexDigit (c:Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'f' ∨ 'A' ≤ c ∧ c ≤ 'F' ∨ '0' ≤ c ∧ c ≤ '9'

def hexToNat (c:Char) : Nat :=
  if 'a' ≤ c ∧ c ≤ 'f' then
    c.toNat - 'a'.toNat
  else if 'A' ≤ c ∧ c ≤ 'F' then
    c.toNat - 'A'.toNat
  else
    c.toNat - '0'.toNat


end Char


namespace String

def hexToNat (s : String) : Nat := s.foldl (λ n c, 16*n + c.hexToNat) 0

end String
