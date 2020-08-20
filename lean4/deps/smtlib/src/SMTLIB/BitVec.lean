
-- FIXME merge this with Galois.Init.Bitvec

import Galois.Init.Nat
import Galois.Init.Int

-- FIXME: obviously this needs to be replaced by actual proofs
axiom PowerHack (n : Nat) (e : Nat) : n < 2 ^ e

def BitVec (sz : Nat) := { x // x < 2 ^ sz }


namespace BitVec
-- open galois

instance {n : Nat} : DecidableEq (BitVec n) :=
  Subtype.DecidableEq


def toNat {w : Nat} (b : BitVec w) : Nat := b.val

-- instance (w:Nat) : DecidableEq (BitVec w) := 
--   { decEq := (λx y, @decEq _ (@Subtype.DecidableEq Nat (λn, n < 2 ^ w) _) x y) }

-- By default just show a BitVector as a nat.
instance (w:Nat) : HasRepr (BitVec w) := ⟨fun v => repr (v.toNat)⟩

section toHex

--- Print word as hex
def ppHex {n : Nat} (v : BitVec n) : String := Nat.ppHex v.toNat

end toHex

axiom zero_lt_pow (n : Nat) : 0 < 2 ^ n

section zero

  -- Create a zero BitVector
  protected
  def zero (n : Nat) : BitVec n :=
    ⟨0, zero_lt_pow n⟩

  -- BitVectors have a zero, at every length
  instance {n:Nat} : HasZero (BitVec n) := ⟨BitVec.zero n⟩

  -- @[simp]
  -- lemma BitVec_zero_zero (x : BitVec 0) : x.toNat = 0 :=
  --   begin
  --     cases x with x_val x_prop,
  --     { simp [Nat.pow_zero, Nat.lt_one_is_zero] at x_prop,
  --       simp, assumption
  --     }
  --   end

end zero

instance {n : Nat} : Inhabited (BitVec n) := {default := 0}

axiom one_le_pow_2 {n: Nat} (h : n > 0) : 1 < 2^n 

axiom Nat.zero_lt_succ (n : Nat) : 0 < Nat.succ n

section one

-- lemma one_le_pow_2 {n: Nat} (h : n > 0) : 1 < 2^n :=
--   calc 1   < 2^1 : by exact (of_as_true trivial)
--        ... ≤ 2^n : Nat.pow_le_pow_of_le_right (of_as_true trivial) h

  -- In pratice, it's more useful to allow 0 length BitVectors to have 1
  -- as well. This leads to a special case where the 0-length BitVector
  -- 1 is really just 0. This turns out to simplify things.
  protected
  def one : ∀(n:Nat), BitVec n
  | 0        => 0
  | (Nat.succ _) => ⟨1, one_le_pow_2 (Nat.zero_lt_succ _)⟩

  instance {n:Nat} : HasOne (BitVec n)  := ⟨BitVec.one n⟩

end one

protected def cong {a b : Nat} (h : a = b) : BitVec a → BitVec b
| ⟨x, p⟩ => ⟨x, h ▸ p⟩

-- lemma cong_val {n m : Nat} {H : n = m} (x : BitVec n)
-- : (BitVec.cong H x).toNat = x.toNat :=
-- begin
--   cases x, simp [BitVec.cong]
-- end

-- protected
-- lemma intro {n:Nat} : Π(x y : BitVec n), x.toNat = y.toNat → x = y
-- | ⟨x, h1⟩ ⟨.(_), h2⟩ rfl => rfl

-- FIXME: more efficient implementation of of_Nat
-- protected def of_nat (n : Nat) (x:Nat) : BitVec n := ⟨ x % (Nat.shiftl 1 n), power_hack _ _⟩

protected def ofNat (n : Nat) (x:Nat) : BitVec n :=
  ⟨ x % 2^n, Nat.modLt _ (Nat.posPowOfPos n (zero_lt_pow 1))⟩

instance Nat_to_BitVec_coe {w : Nat} : HasCoe Nat (BitVec w) := ⟨BitVec.ofNat w⟩

-- theorem ofNat_toNat {n : Nat} (x : BitVec n)
-- : BitVec.ofNat n (BitVec.toNat x) = x :=
--     begin
--       cases x,
--       simp [BitVec.toNat, BitVec.ofNat],
--       apply Nat.mod_eq_of_lt x_property,
--     end

-- theorem toNat_ofNat (k n : Nat)
-- : BitVec.toNat (BitVec.ofNat k n) = n % 2^k :=
--     begin
--       simp [BitVec.ofNat, BitVec.toNat]
--     end

--- Most significant bit
def msb {n:Nat} (x: BitVec n) : Bool := (Nat.shiftr x.toNat (n-1)) = 1

--- Least significant bit.
def lsb {n:Nat} (x: BitVec n) : Bool := Nat.bodd x.toNat

section conversion
  -- Operations For converting to/from BitVectors
  protected def to_int {n:Nat} (x: BitVec n) : Int :=
    match msb x with
    | false => Int.ofNat x.toNat
    | true  => Int.negOfNat (2^n - x.toNat)

  --- Convert an int to two's complement BitVector.
  protected def of_int : ∀(n : Nat), Int → BitVec n
  | n, (Int.ofNat x) => BitVec.ofNat n x
  | n, (Int.negSucc x) => BitVec.ofNat n (Nat.ldiff (2^n-1) x)

end conversion

section bitwise

  -- bitwise negation
  def not {w:Nat} (x: BitVec w) : BitVec w := ⟨2^w - x.toNat - 1, PowerHack _ _
    -- begin
    --   have xval_pos : 0 < x.toNat + 1,
    --   { apply (Nat.succ_pos x.toNat) },
    --   apply (Nat.sub_lt _ xval_pos),
    --   apply Nat.pos_pow_of_pos,
    --   apply (Nat.succ_pos 1)
    -- end
    ⟩

  -- logical bitwise and
  def and {w:Nat} (x y : BitVec w) : BitVec w := BitVec.ofNat w (Nat.land x.toNat y.toNat)
  -- diff x y = x & not y
  def diff {w:Nat} (x y : BitVec w) : BitVec w := BitVec.ofNat w (Nat.ldiff x.toNat y.toNat)
  -- logical bitwise or
  def or  {w:Nat} (x y : BitVec w) : BitVec w := BitVec.ofNat w (Nat.lor  x.toNat y.toNat)
  -- logical bitwise xor
  def xor {w:Nat} (x y : BitVec w) : BitVec w := BitVec.ofNat w (Nat.lxor x.toNat y.toNat)

  infix `.&&.`:70 := and
  infix `.||.`:65 := or

end bitwise

section arith
  -- Arithmetic operations on BitVectors
  variable {n : Nat}

  protected def add (x y : BitVec n) : BitVec n := BitVec.ofNat n (x.toNat + y.toNat)

  def adc (x y : BitVec n) : BitVec n × Bool := ⟨ BitVec.add x y , x.toNat + y.toNat ≥ 2^n ⟩

  -- Usual arithmetic subtraction
  protected def sub (x y : BitVec n) : BitVec n := BitVec.of_int n (x.to_int - y.to_int)


  -- 2s complement negation
  protected def neg {n:Nat} (x : BitVec n) : BitVec n :=
    ⟨if x.toNat = 0 then 0 else 2^n - x.toNat, PowerHack _ _
     -- begin
     --   by_cases (x.toNat = 0),
     --   { simp [h], exact Nat.pos_pow_of_pos _ (of_as_true trivial), },
     --   { simp [h],
     --     --x.toNat (2^n) x_toNat_pos,
     --     have pos : 0 < 2^n - x.toNat, { apply Nat.sub_pos_of_lt x.property },
     --     have x_toNat_pos: 0 < x.toNat, { apply Nat.pos_of_ne_zero h },
     --     apply Nat.sub_lt_of_pos_le x.toNat (2^n) x_toNat_pos,
     --     apply le_of_lt x.property,
     --   }
     -- end
     ⟩

  instance : HasAdd (BitVec n)  := ⟨BitVec.add⟩
  instance : HasSub (BitVec n)  := ⟨BitVec.sub⟩
  instance : HasNeg (BitVec n)  := ⟨BitVec.neg⟩

  protected def mul (x y : BitVec n) : BitVec n := BitVec.ofNat n (x.toNat * y.toNat)

  instance : HasMul (BitVec n) := ⟨BitVec.mul⟩

  def BitVec_pow (x: BitVec n) (k:Nat) : BitVec n := BitVec.ofNat n (x.toNat^k)

  instance BitVec_has_pow : HasPow (BitVec n) Nat := ⟨BitVec_pow⟩

end arith

section shift
  -- Shift related operations, including signed and unsigned shift.

  variable {n : Nat}

  -- shift left
  def shl (x : BitVec n) (i : Nat) : BitVec n := BitVec.ofNat n (Nat.shiftl x.toNat i)

  -- unsigned shift right
  def ushr (x : BitVec n) (i : Nat) : BitVec n := BitVec.ofNat n (Nat.shiftr x.toNat i)

  -- signed shift right
  def sshr (x: BitVec n) (i:Nat) : BitVec n := BitVec.of_int n (Int.shiftr (BitVec.to_int x) i)

end shift

section listlike
  -- Operations that treat BitVectors as a list of bits.

  --- Test if a specific bit with given index is set.
  def nth {w:Nat} (x : BitVec w) (idx : Nat) : Bool := Nat.test_bit x.toNat idx

  -- Change number of bits result while preserving unsigned value modulo output width.
  def uresize {m:Nat} (x: BitVec m) (n:Nat) : BitVec n := BitVec.ofNat _ x.toNat

  -- Change number of bits result while preserving signed value modulo output width.
  def sresize {m:Nat} (x: BitVec m) (n:Nat) : BitVec n := BitVec.of_int _ x.to_int

  open Nat

  -- BitVec specific version of vector.append
  def append {m n} (x: BitVec m) (y: BitVec n) : BitVec (m + n)
    := ⟨ x.toNat * 2^n + y.toNat, PowerHack _ _  /- Nat.mul_pow_add_lt_pow x.property y.property -/ ⟩

  protected
  def bsf' : ∀(n:Nat), Nat → Nat → Option Nat
    | 0,        idx, _ => none
    | (succ m), idx, x =>
      if Nat.test_bit x idx then
        some idx
      else
        bsf' m (idx+1) x

  --- index of least-significant bit that is 1.
  def bsf : ∀{n:Nat}, BitVec n → Option Nat
    | n, x => BitVec.bsf' n 0 x.toNat

  protected
  def bsr' : Nat → Nat → Option Nat
    | x, zero => none
    | x, (succ idx) =>
      if Nat.test_bit x idx then
        some idx
      else
        bsr' x idx

  --- index of the most-significant bit that is 1.
  def bsr : ∀{n:Nat}, BitVec n → Option Nat
    | n, x => BitVec.bsr' x.toNat n

  -- example : bsf (BitVec.ofNat 3 0) = none := of_as_true trivial
  -- example : bsr (BitVec.ofNat 3 0) = none := of_as_true trivial

  -- example : bsf (BitVec.ofNat 3 5) = some 0 := of_as_true trivial
  -- example : bsr (BitVec.ofNat 3 5) = some 2 := of_as_true trivial

  def slice {w: Nat} (u l k:Nat) (H: w = k + (u + 1 - l)) (x: BitVec w) : BitVec (u + 1 - l) :=
     BitVec.ofNat _ (Nat.shiftr x.toNat l)

  protected
  def foldl' {α : Sort _} (f : α -> Bool → α) (x : Nat) (init : α) : Nat → α
    | zero       => init
    | (succ idx) => f (foldl' idx) (x.test_bit idx)
    
  -- foldl follows nth's behaviour, so 
  -- foldl f i b = f (f (f i b!0) b!1) b!2 etc.
  def foldl {α : Sort _} {n : Nat} (f : α → Bool → α) (init : α) (b : BitVec n) : α :=
    BitVec.foldl' f b.toNat init n

  protected
  def foldr' {α : Sort _} (f : Bool → α → α) (x : Nat) (init : α) (n : Nat) : Nat → α
    | zero       => init
    | (succ idx) => f  (x.test_bit (n - succ idx)) (foldr' idx)
    
  -- foldr follows nth's behaviour, so 
  -- foldr f i b = f b!0 (f b!1 ... (f b!(n-1) i))
  def foldr {α : Sort _} {n : Nat} (f : Bool → α → α) (init : α) (b : BitVec n) : α :=
    BitVec.foldr' f b.toNat init n n

end listlike

section comparison
  -- Comparison operations, including signed and unsigned versions
  variable {n : Nat}

  def ult (x y : BitVec n) : Prop := x.toNat < y.toNat
  def ugt (x y : BitVec n) : Prop := ult y x
  def ule (x y : BitVec n) : Prop := ¬ (ult y x)
  def uge (x y : BitVec n) : Prop := ule y x

  def slt (x y : BitVec n) : Prop := x.to_int < y.to_int
  def sgt (x y : BitVec n) : Prop := slt y x
  def sle (x y : BitVec n) : Prop := ¬ (slt y x)
  def sge (x y : BitVec n) : Prop := sle y x

  -- local attribute [reducible] ult
  -- local attribute [reducible] ugt
  -- local attribute [reducible] ule
  -- local attribute [reducible] uge
  attribute [reducible] ult
  attribute [reducible] ugt
  attribute [reducible] ule
  attribute [reducible] uge


  instance decidable_ult {n} {x y : BitVec n} : Decidable (BitVec.ult x y) := inferInstance -- by apply_instance
  instance decidable_ugt {n} {x y : BitVec n} : Decidable (BitVec.ugt x y) := inferInstance -- by apply_instance
  instance decidable_ule {n} {x y : BitVec n} : Decidable (BitVec.ule x y) := inferInstance -- by apply_instance
  instance decidable_uge {n} {x y : BitVec n} : Decidable (BitVec.uge x y) := inferInstance -- by apply_instance

  -- local attribute [reducible] slt
  -- local attribute [reducible] sgt
  -- local attribute [reducible] sle
  -- local attribute [reducible] sge
  attribute [reducible] slt
  attribute [reducible] sgt
  attribute [reducible] sle
  attribute [reducible] sge

  instance decidable_slt {n} {x y : BitVec n} : Decidable (BitVec.slt x y) := inferInstance -- by apply_instance
  instance decidable_sgt {n} {x y : BitVec n} : Decidable (BitVec.sgt x y) := inferInstance -- by apply_instance
  instance decidable_sle {n} {x y : BitVec n} : Decidable (BitVec.sle x y) := inferInstance -- by apply_instance
  instance decidable_sge {n} {x y : BitVec n} : Decidable (BitVec.sge x y) := inferInstance -- by apply_instance

end comparison


def concat' {n:Nat} (input: List (BitVec n)): Nat :=
  List.foldl (fun v (a:BitVec n) => Nat.shiftl v n + a.toNat) 0 input

--- ConcateNation all BitVectors in the List together and return a new BitVector.
--
-- The most significant bits of are returned first.
def concat_list {m:Nat}(input: List (BitVec m)) (n:Nat) : BitVec n :=
  BitVec.ofNat _ (concat' input)

--- ConcateNation all BitVectors in the vector together and return a new BitVector.
--
-- The most significant bits of are returned first.
--
-- To minimize the need for proofs, we intentionally do not force that the output
-- has a specific length.
-- def concat_vec {w m : Nat}(input: vector (BitVec w) m) (n:Nat) : BitVec n :=
--   BitVec.ofNat _ (concat' input.to_list)

-- example : concat_list [(1 : BitVec 4), 0] 8 = (16 : BitVec 8) := by exact (of_as_true trivial)

--- Forms a List of BitVectors by taking a specific number of bits from parts of the
-- first argument.
--
-- The head of the List has the most-significant bits.
def split_to_list (x:Nat) (w:Nat) : Nat → List (BitVec w)
| Nat.zero => []
| (Nat.succ n) => BitVec.ofNat w (Nat.shiftr x (n*w)) :: split_to_list n

-- theorem length_split_to_list (x:Nat) (w : Nat) (m:Nat) : List.length (split_to_list x w m) = m :=
-- begin
--   induction m,
--   case Nat.zero { simp [split_to_list], },
--   case Nat.succ : m ind { simp [split_to_list, ind, Nat.succ_add], },
-- end

/- Split a single BitVector into a List of BitVectors with most-significant bits first. -/
def split_list {n:Nat} (x:BitVec n) (w:Nat) : List (BitVec w) := split_to_list x.toNat w (Nat.div n w)

/- Split a single BitVector into a vector of BitVectors with most-significant bits first. -/
-- def split_vec {n:Nat} (x:BitVec n) (w m:Nat) : vector (BitVec w) m :=
--  ⟨split_to_list x.toNat w m, length_split_to_list _ _ _⟩

-- example : split_list (16 : BitVec 8) 4 = [(1 : BitVec 4), 0] := by exact (of_as_true trivial)

--- Git bits [i..i+m] out of n.
def get_bits {n} (x:BitVec n) (i m : Nat) (p:i+m ≤ n) : BitVec m :=
  BitVec.ofNat m (Nat.shiftr x.toNat i)

--#eval ((get_bits (0x01234567 : BitVec 32) 8 16 (of_as_true trivial) = 0x2345) : Bool)

--- Set bits at given index.
def set_bits {n} (x:BitVec n) (i:Nat) {m} (y:BitVec m) (p:i+m ≤ n) : BitVec n :=
  let mask := BitVec.ofNat n (Nat.shiftl ((2^m)-1) i);
  or (diff x mask) (BitVec.ofNat n (Nat.shiftl y.toNat i))

--#eval ((set_bits (0x01234567 : BitVec 32) 8 (0x5432 : BitVec 16) (of_as_true trivial) = 0x01543267) : Bool)


end BitVec
