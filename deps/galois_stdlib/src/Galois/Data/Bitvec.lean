/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich, Jason Dagit

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
-- import galois.data.nat.basic
-- import data.vector

-- A `bitvec n` is a subtype of natural numbers such that the value of
-- the bitvec is strictly less than 2^n.
-- structure bitvec (sz:ℕ) :=
-- (to_nat : ℕ)
-- (property : to_nat < (2 ^ sz))

import Init.Data.Nat
import Galois.Init.Nat
import Galois.Init.Int

-- FIXME: obviously this needs to be replaced by actual proofs
axiom power_hack (n : Nat) (e : Nat) : n < 2 ^ e

def bitvec (sz : Nat) := { x // x < 2 ^ sz }

instance bitvec_DecidableEq {sz : Nat}: DecidableEq (bitvec sz) :=
  inferInstanceAs (DecidableEq { x // x < 2 ^ sz })


namespace bitvec
-- open galois

def to_nat {w : Nat} (b : bitvec w) : Nat := b.val

-- instance (w:Nat) : DecidableEq (bitvec w) := 
--   { decEq := (λx y, @decEq _ (@Subtype.DecidableEq Nat (λn, n < 2 ^ w) _) x y) }

-- By default just show a bitvector as a nat.
instance (w:Nat) : Repr (bitvec w) := ⟨fun v n => reprPrec (v.to_nat) n⟩

section to_hex

--- Print word as hex
def pp_hex {n : Nat} (v : bitvec n) : String := Nat.ppHex v.to_nat

end to_hex

axiom zero_lt_pow (n : Nat) : 0 < 2 ^ n

section zero

  -- Create a zero bitvector
  protected
  def zero (n : Nat) : bitvec n :=
    ⟨0, zero_lt_pow n⟩

  -- bitvectors have a zero, at every length
  instance {n:Nat} : Inhabited (bitvec n) := ⟨bitvec.zero n⟩

  -- @[simp]
  -- lemma bitvec_zero_zero (x : bitvec 0) : x.to_Nat = 0 :=
  --   begin
  --     cases x with x_val x_prop,
  --     { simp [Nat.pow_zero, Nat.lt_one_is_zero] at x_prop,
  --       simp, assumption
  --     }
  --   end

end zero

axiom one_le_pow_2 {n: Nat} (h : n > 0) : 1 < 2^n 

axiom Nat.zero_lt_succ (n : Nat) : 0 < Nat.succ n

section one

-- lemma one_le_pow_2 {n: Nat} (h : n > 0) : 1 < 2^n :=
--   calc 1   < 2^1 : by exact (of_as_true trivial)
--        ... ≤ 2^n : Nat.pow_le_pow_of_le_right (of_as_true trivial) h

  -- In pratice, it's more useful to allow 0 length bitvectors to have 1
  -- as well. This leads to a special case where the 0-length bitvector
  -- 1 is really just 0. This turns out to simplify things.
  protected
  def one : ∀(n:Nat), bitvec n
  | 0        => bitvec.zero 0
  | (Nat.succ _) => ⟨1, one_le_pow_2 (Nat.zero_lt_succ _)⟩

end one

protected def cong {a b : Nat} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ => ⟨x, h ▸ p⟩

-- lemma cong_val {n m : Nat} {H : n = m} (x : bitvec n)
-- : (bitvec.cong H x).to_Nat = x.to_Nat :=
-- begin
--   cases x, simp [bitvec.cong]
-- end

-- protected
-- lemma intro {n:Nat} : Π(x y : bitvec n), x.to_Nat = y.to_Nat → x = y
-- | ⟨x, h1⟩ ⟨.(_), h2⟩ rfl => rfl

-- FIXME: more efficient implementation of of_Nat
-- protected def of_nat (n : Nat) (x:Nat) : bitvec n := ⟨ x % (Nat.shiftl 1 n), power_hack _ _⟩

protected def of_nat (width : Nat) (x:Nat) : bitvec width :=
  ⟨ x % 2^width, Nat.mod_lt _ (Nat.posPowOfPos width (zero_lt_pow 1))⟩

instance {w : Nat} (n : Nat) : OfNat (bitvec w) n := ⟨bitvec.of_nat w n⟩

instance Nat_to_bitvec_coe {w : Nat} : Coe Nat (bitvec w) := ⟨bitvec.of_nat w⟩

-- theorem of_Nat_to_Nat {n : Nat} (x : bitvec n)
-- : bitvec.of_Nat n (bitvec.to_Nat x) = x :=
--     begin
--       cases x,
--       simp [bitvec.to_Nat, bitvec.of_Nat],
--       apply Nat.mod_eq_of_lt x_property,
--     end

-- theorem to_Nat_of_Nat (k n : Nat)
-- : bitvec.to_Nat (bitvec.of_Nat k n) = n % 2^k :=
--     begin
--       simp [bitvec.of_Nat, bitvec.to_Nat]
--     end

--- Most significant bit
def msb {n:Nat} (x: bitvec n) : Bool := (Nat.shiftr x.to_nat (n-1)) = 1

--- Least significant bit.
def lsb {n:Nat} (x: bitvec n) : Bool := Nat.bodd x.to_nat

section conversion
  -- Operations For converting to/from bitvectors
  protected def to_int {n:Nat} (x: bitvec n) : Int :=
    match msb x with
    | false => Int.ofNat x.to_nat
    | true  => Int.negOfNat (2^n - x.to_nat)

  --- Convert an int to two's complement bitvector.
  protected def of_int : ∀(n : Nat), Int → bitvec n
  | n, (Int.ofNat x) => bitvec.of_nat n x
  | n, (Int.negSucc x) => bitvec.of_nat n (Nat.ldiff (2^n-1) x)

end conversion

section bitwise

  -- bitwise negation
  def not {w:Nat} (x: bitvec w) : bitvec w := ⟨2^w - x.to_nat - 1, power_hack _ _
    -- begin
    --   have xval_pos : 0 < x.to_nat + 1,
    --   { apply (Nat.succ_pos x.to_nat) },
    --   apply (Nat.sub_lt _ xval_pos),
    --   apply Nat.pos_pow_of_pos,
    --   apply (Nat.succ_pos 1)
    -- end
    ⟩

  -- logical bitwise and
  def and {w:Nat} (x y : bitvec w) : bitvec w := bitvec.of_nat w (Nat.land x.to_nat y.to_nat)
  -- diff x y = x & not y
  def diff {w:Nat} (x y : bitvec w) : bitvec w := bitvec.of_nat w (Nat.ldiff x.to_nat y.to_nat)
  -- logical bitwise or
  def or  {w:Nat} (x y : bitvec w) : bitvec w := bitvec.of_nat w (Nat.lor  x.to_nat y.to_nat)
  -- logical bitwise xor
  def xor {w:Nat} (x y : bitvec w) : bitvec w := bitvec.of_nat w (Nat.lxor x.to_nat y.to_nat)

  infix:70 " .&&. " => and
  infix:65 " .||. " => or

end bitwise

section arith
  -- Arithmetic operations on bitvectors
  variable {n : Nat}

  protected def add (x y : bitvec n) : bitvec n := bitvec.of_nat n (x.to_nat + y.to_nat)

  def adc (x y : bitvec n) : bitvec n × Bool := ⟨ bitvec.add x y , x.to_nat + y.to_nat ≥ 2^n ⟩

  -- Usual arithmetic subtraction
  protected def sub (x y : bitvec n) : bitvec n := bitvec.of_int n (x.to_int - y.to_int)


  -- 2s complement negation
  protected def neg {n:Nat} (x : bitvec n) : bitvec n :=
    ⟨if x.to_nat = 0 then 0 else 2^n - x.to_nat, power_hack _ _
     -- begin
     --   by_cases (x.to_nat = 0),
     --   { simp [h], exact Nat.pos_pow_of_pos _ (of_as_true trivial), },
     --   { simp [h],
     --     --x.to_nat (2^n) x_to_nat_pos,
     --     have pos : 0 < 2^n - x.to_nat, { apply Nat.sub_pos_of_lt x.property },
     --     have x_to_nat_pos: 0 < x.to_nat, { apply Nat.pos_of_ne_zero h },
     --     apply Nat.sub_lt_of_pos_le x.to_nat (2^n) x_to_nat_pos,
     --     apply le_of_lt x.property,
     --   }
     -- end
     ⟩

  instance : Add (bitvec n)  := ⟨bitvec.add⟩
  instance : Sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : Neg (bitvec n)  := ⟨bitvec.neg⟩

  protected def mul (x y : bitvec n) : bitvec n := bitvec.of_nat n (x.to_nat * y.to_nat)

  instance : Mul (bitvec n) := ⟨bitvec.mul⟩

  def bitvec_pow (x: bitvec n) (k:Nat) : bitvec n := bitvec.of_nat n (x.to_nat^k)

  instance bitvec_has_pow : HPow (bitvec n) Nat (bitvec n) := ⟨bitvec_pow⟩

  protected def udiv (x y : bitvec n) : bitvec n := bitvec.of_nat n (x.to_nat / y.to_nat)
  protected def sdiv (x y : bitvec n) : bitvec n := bitvec.of_int n (x.to_int / y.to_int)

  protected def urem (x y : bitvec n) : bitvec n := bitvec.of_nat n (x.to_nat % y.to_nat)

  -- Lean4 integer `mod` sign follows the dividend, which is what bvsrem does... funny.
  protected def srem (x y : bitvec n) : bitvec n := bitvec.of_int n (Int.mod x.to_int y.to_int)

  -- bvsmod sign follows the divisor
  protected def smod (x y : bitvec n) : bitvec n :=
  match x.to_int, y.to_int with
  | Int.ofNat j,   Int.ofNat k   => bitvec.of_int n (Int.ofNat (j % k))
  | Int.negSucc j, Int.ofNat k   => bitvec.of_int n (Int.ofNat (Nat.succ j % k))
  | Int.ofNat j,   Int.negSucc k => bitvec.of_int n (-Int.ofNat (j % Nat.succ k))
  | Int.negSucc j, Int.negSucc k => bitvec.of_int n (-Int.ofNat (Nat.succ j % Nat.succ k))


end arith

section shift
  -- Shift related operations, including signed and unsigned shift.

  variable {n : Nat}

  -- shift left
  def shl (x : bitvec n) (i : Nat) : bitvec n := bitvec.of_nat n (Nat.shiftl x.to_nat i)

  -- unsigned shift right
  def ushr (x : bitvec n) (i : Nat) : bitvec n := bitvec.of_nat n (Nat.shiftr x.to_nat i)

  -- signed shift right
  def sshr (x: bitvec n) (i:Nat) : bitvec n := bitvec.of_int n (Int.shiftr (bitvec.to_int x) i)

end shift

section listlike
  -- Operations that treat bitvectors as a list of bits.

  --- Test if a specific bit with given index is set.
  def nth {w:Nat} (x : bitvec w) (idx : Nat) : Bool := Nat.test_bit x.to_nat idx

  -- Change number of bits result while preserving unsigned value modulo output width.
  def uresize {m:Nat} (x: bitvec m) (n:Nat) : bitvec n := bitvec.of_nat _ x.to_nat

  -- Change number of bits result while preserving signed value modulo output width.
  def sresize {m:Nat} (x: bitvec m) (n:Nat) : bitvec n := bitvec.of_int _ x.to_int
 
  -- bitvec specific version of vector.append
  def append {m n} (x: bitvec m) (y: bitvec n) : bitvec (m + n)
    := ⟨ x.to_nat * 2^n + y.to_nat, power_hack _ _  /- Nat.mul_pow_add_lt_pow x.property y.property -/ ⟩

  def repeat {n} (x: bitvec n) : forall (i : Nat), bitvec (i * n)
  | Nat.zero => 0
  | Nat.succ m => 
    let rst : bitvec (m * n) := repeat x m;
    let res : bitvec (m * n + n) := @append (m * n) n rst x;
    have hEq : (m * n + n) = (Nat.succ m * n) from Eq.symm $ Nat.succ_mul m n;
    have tEq : bitvec (m * n + n) = bitvec (Nat.succ m * n) from congrArg bitvec hEq;
    cast tEq res 

  protected
  def bsf' : ∀(n:Nat), Nat → Nat → Option Nat
    | 0,        idx, _ => none
    | (Nat.succ m), idx, x =>
      if Nat.test_bit x idx then
        some idx
      else
        bitvec.bsf' m (idx+1) x

  --- index of least-significant bit that is 1.
  def bsf : ∀{n:Nat}, bitvec n → Option Nat
    | n, x => bitvec.bsf' n 0 x.to_nat

  protected
  def bsr' : Nat → Nat → Option Nat
    | x, Nat.zero => none
    | x, (Nat.succ idx) =>
      if Nat.test_bit x idx then
        some idx
      else
        bitvec.bsr' x idx

  --- index of the most-significant bit that is 1.
  def bsr : ∀{n:Nat}, bitvec n → Option Nat
    | n, x => bitvec.bsr' x.to_nat n

  -- example : bsf (bitvec.of_nat 3 0) = none := of_as_true trivial
  -- example : bsr (bitvec.of_nat 3 0) = none := of_as_true trivial

  -- example : bsf (bitvec.of_nat 3 5) = some 0 := of_as_true trivial
  -- example : bsr (bitvec.of_nat 3 5) = some 2 := of_as_true trivial

  def slice {w: Nat} (u l k:Nat) (H: w = k + (u + 1 - l)) (x: bitvec w) : bitvec (u + 1 - l) :=
     bitvec.of_nat _ (Nat.shiftr x.to_nat l)

  def extract {w: Nat} (u l:Nat) (x: bitvec w) : bitvec (u + 1 - l) :=
     bitvec.of_nat _ (Nat.shiftr x.to_nat l)

  def rotateRight {w:Nat} (i:Nat) (x: bitvec w) : bitvec w :=
    let lhs := x.shl (w - i);
    let rhs := x.ushr w;
    bitvec.or lhs rhs

  def rotateLeft {w:Nat} (i:Nat) (x: bitvec w) : bitvec w :=
    let lhs := x.shl i;
    let rhs := x.ushr (w - i);
    bitvec.or lhs rhs

  protected
  def foldl' {α : Sort _} (f : α -> Bool → α) (x : Nat) (init : α) : Nat → α
    | Nat.zero       => init
    | (Nat.succ idx) => f (bitvec.foldl' f x init idx) (x.test_bit idx)
    
  -- foldl follows nth's behaviour, so 
  -- foldl f i b = f (f (f i b!0) b!1) b!2 etc.
  def foldl {α : Sort _} {n : Nat} (f : α → Bool → α) (init : α) (b : bitvec n) : α :=
    bitvec.foldl' f b.to_nat init n

  protected
  def foldr' {α : Sort _} (f : Bool → α → α) (x : Nat) (init : α) (n : Nat) : Nat → α
    | Nat.zero       => init
    | (Nat.succ idx) => f  (x.test_bit (n - Nat.succ idx)) (bitvec.foldr' f x init n idx)
    
  -- foldr follows nth's behaviour, so 
  -- foldr f i b = f b!0 (f b!1 ... (f b!(n-1) i))
  def foldr {α : Sort _} {n : Nat} (f : Bool → α → α) (init : α) (b : bitvec n) : α :=
    bitvec.foldr' f b.to_nat init n n

end listlike

section comparison
  -- Comparison operations, including signed and unsigned versions
  variable {n : Nat}

  def ult (x y : bitvec n) : Prop := x.to_nat < y.to_nat
  def ugt (x y : bitvec n) : Prop := ult y x
  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge (x y : bitvec n) : Prop := ule y x

  def slt (x y : bitvec n) : Prop := x.to_int < y.to_int
  def sgt (x y : bitvec n) : Prop := slt y x
  def sle (x y : bitvec n) : Prop := ¬ (slt y x)
  def sge (x y : bitvec n) : Prop := sle y x

  -- local attribute [reducible] ult
  -- local attribute [reducible] ugt
  -- local attribute [reducible] ule
  -- local attribute [reducible] uge
  attribute [reducible] ult
  attribute [reducible] ugt
  attribute [reducible] ule
  attribute [reducible] uge


  instance decidable_ult {n} {x y : bitvec n} : Decidable (bitvec.ult x y) := inferInstance -- by apply_instance
  instance decidable_ugt {n} {x y : bitvec n} : Decidable (bitvec.ugt x y) := inferInstance -- by apply_instance
  instance decidable_ule {n} {x y : bitvec n} : Decidable (bitvec.ule x y) := inferInstance -- by apply_instance
  instance decidable_uge {n} {x y : bitvec n} : Decidable (bitvec.uge x y) := inferInstance -- by apply_instance

  -- local attribute [reducible] slt
  -- local attribute [reducible] sgt
  -- local attribute [reducible] sle
  -- local attribute [reducible] sge
  attribute [reducible] slt
  attribute [reducible] sgt
  attribute [reducible] sle
  attribute [reducible] sge

  instance decidable_slt {n} {x y : bitvec n} : Decidable (bitvec.slt x y) := inferInstance -- by apply_instance
  instance decidable_sgt {n} {x y : bitvec n} : Decidable (bitvec.sgt x y) := inferInstance -- by apply_instance
  instance decidable_sle {n} {x y : bitvec n} : Decidable (bitvec.sle x y) := inferInstance -- by apply_instance
  instance decidable_sge {n} {x y : bitvec n} : Decidable (bitvec.sge x y) := inferInstance -- by apply_instance

end comparison


def concat' {n:Nat} (input: List (bitvec n)): Nat :=
  List.foldl (fun v (a:bitvec n) => Nat.shiftl v n + a.to_nat) 0 input

--- ConcateNation all bitvectors in the List together and return a new bitvector.
--
-- The most significant bits of are returned first.
def concat_list {m:Nat}(input: List (bitvec m)) (n:Nat) : bitvec n :=
  bitvec.of_nat _ (concat' input)

--- ConcateNation all bitvectors in the vector together and return a new bitvector.
--
-- The most significant bits of are returned first.
--
-- To minimize the need for proofs, we intentionally do not force that the output
-- has a specific length.
-- def concat_vec {w m : Nat}(input: vector (bitvec w) m) (n:Nat) : bitvec n :=
--   bitvec.of_nat _ (concat' input.to_list)

-- example : concat_list [(1 : bitvec 4), 0] 8 = (16 : bitvec 8) := by exact (of_as_true trivial)

--- Forms a List of bitvectors by taking a specific number of bits from parts of the
-- first argument.
--
-- The head of the List has the most-significant bits.
def split_to_list (x:Nat) (w:Nat) : Nat → List (bitvec w)
| Nat.zero => []
| (Nat.succ n) => bitvec.of_nat w (Nat.shiftr x (n*w)) :: split_to_list x w n

-- theorem length_split_to_list (x:Nat) (w : Nat) (m:Nat) : List.length (split_to_list x w m) = m :=
-- begin
--   induction m,
--   case Nat.zero { simp [split_to_list], },
--   case Nat.succ : m ind { simp [split_to_list, ind, Nat.succ_add], },
-- end

/- Split a single bitvector into a List of bitvectors with most-significant bits first. -/
def split_list {n:Nat} (x:bitvec n) (w:Nat) : List (bitvec w) := split_to_list x.to_nat w (Nat.div n w)

/- Split a single bitvector into a vector of bitvectors with most-significant bits first. -/
-- def split_vec {n:Nat} (x:bitvec n) (w m:Nat) : vector (bitvec w) m :=
--  ⟨split_to_list x.to_nat w m, length_split_to_list _ _ _⟩

-- example : split_list (16 : bitvec 8) 4 = [(1 : bitvec 4), 0] := by exact (of_as_true trivial)

--- Git bits [i..i+m] out of n.
def get_bits {n} (x:bitvec n) (i m : Nat) (p:i+m ≤ n) : bitvec m :=
  bitvec.of_nat m (Nat.shiftr x.to_nat i)

--#eval ((get_bits (0x01234567 : bitvec 32) 8 16 (of_as_true trivial) = 0x2345) : Bool)

--- Set bits at given index.
def set_bits {n} (x:bitvec n) (i:Nat) {m} (y:bitvec m) (p:i+m ≤ n) : bitvec n :=
  let mask := bitvec.of_nat n (Nat.shiftl ((2^m)-1) i);
  or (diff x mask) (bitvec.of_nat n (Nat.shiftl y.to_nat i))

--#eval ((set_bits (0x01234567 : bitvec 32) 8 (0x5432 : bitvec 16) (of_as_true trivial) = 0x01543267) : Bool)


end bitvec
