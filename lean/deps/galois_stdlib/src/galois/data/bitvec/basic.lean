/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich, Jason Dagit

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import galois.data.nat.basic
import data.vector

-- A `bitvec n` is a subtype of natural numbers such that the value of
-- the bitvec is strictly less than 2^n.
structure bitvec (sz:ℕ) :=
(to_nat : ℕ)
(property : to_nat < (2 ^ sz))

namespace bitvec

instance (w:ℕ) : decidable_eq (bitvec w) := by tactic.mk_dec_eq_instance

-- By default just show a bitvector as a nat.
instance (w:ℕ) : has_repr (bitvec w) := ⟨λv, repr (v.to_nat)⟩

section zero

  -- Create a zero bitvector
  protected
  def zero (n : ℕ) : bitvec n :=
    ⟨0, nat.pos_pow_of_pos n dec_trivial⟩

  -- bitvectors have a zero, at every length
  instance {n:ℕ} : has_zero (bitvec n) := ⟨bitvec.zero n⟩

  @[simp]
  lemma bitvec_zero_zero (x : bitvec 0) : x.to_nat = 0 :=
    begin
      cases x with x_val x_prop,
      { simp [nat.pow_zero, nat.lt_one_is_zero] at x_prop,
        simp, assumption
      }
    end

end zero

section one

lemma one_le_pow_2 {n: ℕ} (h : n > 0) : 1 < 2^n :=
  calc 1   < 2^1 : by exact (of_as_true trivial)
       ... ≤ 2^n : nat.pow_le_pow_of_le_right (of_as_true trivial) h

  -- In pratice, it's more useful to allow 0 length bitvectors to have 1
  -- as well. This leads to a special case where the 0-length bitvector
  -- 1 is really just 0. This turns out to simplify things.
  protected
  def one : Π(n:ℕ), bitvec n
  | 0        := 0
  | (nat.succ _) := ⟨1, one_le_pow_2 (nat.zero_lt_succ _)⟩

  instance {n:ℕ} : has_one (bitvec n)  := ⟨bitvec.one n⟩

end one

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

lemma cong_val {n m : ℕ} {H : n = m} (x : bitvec n)
: (bitvec.cong H x).to_nat = x.to_nat :=
begin
  cases x, simp [bitvec.cong]
end

protected
lemma intro {n:ℕ} : Π(x y : bitvec n), x.to_nat = y.to_nat → x = y
| ⟨x, h1⟩ ⟨.(_), h2⟩ rfl := rfl

protected def of_nat (n : ℕ) (x:ℕ) : bitvec n :=
  ⟨ x % 2^n, nat.mod_lt _ (nat.pos_pow_of_pos n (of_as_true trivial))⟩

theorem of_nat_to_nat {n : ℕ} (x : bitvec n)
: bitvec.of_nat n (bitvec.to_nat x) = x :=
    begin
      cases x,
      simp [bitvec.to_nat, bitvec.of_nat],
      apply nat.mod_eq_of_lt x_property,
    end

theorem to_nat_of_nat (k n : ℕ)
: bitvec.to_nat (bitvec.of_nat k n) = n % 2^k :=
    begin
      simp [bitvec.of_nat, bitvec.to_nat]
    end

--- Most significant bit
def msb {n:ℕ} (x: bitvec n) : bool := (nat.shiftr x.to_nat (n-1)) = 1

--- Least significant bit.
def lsb {n:ℕ} (x: bitvec n) : bool := nat.bodd x.to_nat

section conversion
  -- Operations for converting to/from bitvectors

  protected def to_int {n:ℕ} (x: bitvec n) : int :=
    match msb x with
    | ff := int.of_nat x.to_nat
    | tt := int.neg_of_nat (2^n - x.to_nat)
    end

  --- Convert an int to two's complement bitvector.
  protected def of_int : Π(n : ℕ), ℤ → bitvec n
  | n (int.of_nat x) := bitvec.of_nat n x
  | n -[1+ x] := bitvec.of_nat n (nat.ldiff (2^n-1) x)

end conversion

section bitwise

  -- bitwise negation
  def not {w:ℕ} (x: bitvec w) : bitvec w := ⟨2^w - x.to_nat - 1,
    begin
      have xval_pos : 0 < x.to_nat + 1,
      { apply (nat.succ_pos x.to_nat) },
      apply (nat.sub_lt _ xval_pos),
      apply nat.pos_pow_of_pos,
      apply (nat.succ_pos 1)
    end⟩

  -- logical bitwise and
  def and {w:ℕ} (x y : bitvec w) : bitvec w := bitvec.of_nat w (nat.land x.to_nat y.to_nat)
  -- logical bitwise or
  def or  {w:ℕ} (x y : bitvec w) : bitvec w := bitvec.of_nat w (nat.lor  x.to_nat y.to_nat)
  -- logical bitwise xor
  def xor {w:ℕ} (x y : bitvec w) : bitvec w := bitvec.of_nat w (nat.lxor x.to_nat y.to_nat)

  infix `.&&.`:70 := and
  infix `.||.`:65 := or

end bitwise

section arith
  -- Arithmetic operations on bitvectors
  variable {n : ℕ}

  protected def add (x y : bitvec n) : bitvec n := bitvec.of_nat n (x.to_nat + y.to_nat)

  def adc (x y : bitvec n) : bitvec n × bool := ⟨ bitvec.add x y , x.to_nat + y.to_nat ≥ 2^n ⟩

  -- Usual arithmetic subtraction
  protected def sub (x y : bitvec n) : bitvec n := bitvec.of_int n (x.to_int - y.to_int)


  -- 2s complement negation
  protected def neg {n:ℕ} (x : bitvec n) : bitvec n :=
    ⟨if x.to_nat = 0 then 0 else 2^n - x.to_nat,
     begin
       by_cases (x.to_nat = 0),
       { simp [h], exact nat.pos_pow_of_pos _ (of_as_true trivial), },
       { simp [h],
         --x.to_nat (2^n) x_to_nat_pos,
         have pos : 0 < 2^n - x.to_nat, { apply nat.sub_pos_of_lt x.property },
         have x_to_nat_pos: 0 < x.to_nat, { apply nat.pos_of_ne_zero h },
         apply nat.sub_lt_of_pos_le x.to_nat (2^n) x_to_nat_pos,
         apply le_of_lt x.property,
       }
     end⟩

  instance : has_add (bitvec n)  := ⟨bitvec.add⟩
  instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

  protected def mul (x y : bitvec n) : bitvec n := bitvec.of_nat n (x.to_nat * y.to_nat)

  instance : has_mul (bitvec n) := ⟨bitvec.mul⟩

  def bitvec_pow (x: bitvec n) (k:ℕ) : bitvec n := bitvec.of_nat n (x.to_nat^k)

  instance bitvec_has_pow : has_pow (bitvec n) ℕ := ⟨bitvec_pow⟩

end arith

section shift
  -- Shift related operations, including signed and unsigned shift.

  variable {n : ℕ}

  -- shift left
  def shl (x : bitvec n) (i : ℕ) : bitvec n := bitvec.of_nat n (nat.shiftl x.to_nat i)

  -- unsigned shift right
  def ushr (x : bitvec n) (i : ℕ) : bitvec n := bitvec.of_nat n (nat.shiftr x.to_nat i)

  -- signed shift right
  def sshr (x: bitvec n) (i:ℕ) : bitvec n := bitvec.of_int n (int.shiftr (bitvec.to_int x) i)

end shift

section listlike
  -- Operations that treat bitvectors as a list of bits.

  --- Test if a specific bit with given index is set.
  def nth {w:ℕ} (x : bitvec w) (idx : ℕ) : bool := nat.test_bit x.to_nat idx

  -- Change number of bits result while preserving unsigned value modulo output width.
  def uresize {n:ℕ} (x: bitvec n) (m:ℕ) : bitvec m := bitvec.of_nat _ x.to_nat

  -- Change number of bits result while preserving signed value modulo output width.
  def sresize {n:ℕ} (x: bitvec n) (m:ℕ) : bitvec m := bitvec.of_int m x.to_int

  open nat

  -- bitvec specific version of vector.append
  def append {m n} (x: bitvec m) (y: bitvec n) : bitvec (m + n)
    := ⟨ x.to_nat * 2^n + y.to_nat, nat.mul_pow_add_lt_pow x.property y.property ⟩

  protected
  def bsf' : Π(n:ℕ), ℕ → ℕ → option ℕ
    | 0        idx _ := none
    | (succ m) idx x :=
      if nat.test_bit x idx then
        some idx
      else
        bsf' m (idx+1) x

  --- index of least-significant bit that is 1.
  def bsf : Π{n:ℕ}, bitvec n → option ℕ
    | n x := bitvec.bsf' n 0 x.to_nat

  protected
  def bsr' : ℕ → ℕ → option ℕ
    | x zero := none
    | x (succ idx) :=
      if nat.test_bit x idx then
        some idx
      else
        bsr' x idx

  --- index of the most-significant bit that is 1.
  def bsr : Π{n:ℕ}, bitvec n → option ℕ
    | n x := bitvec.bsr' x.to_nat n

  example : bsf (bitvec.of_nat 3 0) = none := of_as_true trivial
  example : bsr (bitvec.of_nat 3 0) = none := of_as_true trivial

  example : bsf (bitvec.of_nat 3 5) = some 0 := of_as_true trivial
  example : bsr (bitvec.of_nat 3 5) = some 2 := of_as_true trivial

  def slice {w: ℕ} (u l k:ℕ) (H: w = k + (u + 1 - l)) (x: bitvec w) : bitvec (u + 1 - l) :=
     bitvec.of_nat _ (nat.shiftr x.to_nat l)

end listlike

section comparison
  -- Comparison operations, including signed and unsigned versions
  variable {n : ℕ}

  def ult (x y : bitvec n) : Prop := x.to_nat < y.to_nat
  def ugt (x y : bitvec n) : Prop := ult y x
  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge (x y : bitvec n) : Prop := ule y x

  def slt (x y : bitvec n) : Prop := x.to_int < y.to_int
  def sgt (x y : bitvec n) : Prop := slt y x
  def sle (x y : bitvec n) : Prop := ¬ (slt y x)
  def sge (x y : bitvec n) : Prop := sle y x

  local attribute [reducible] ult
  local attribute [reducible] ugt
  local attribute [reducible] ule
  local attribute [reducible] uge

  instance decidable_ult {n} {x y : bitvec n} : decidable (bitvec.ult x y) := by apply_instance
  instance decidable_ugt {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := by apply_instance
  instance decidable_ule {n} {x y : bitvec n} : decidable (bitvec.ule x y) := by apply_instance
  instance decidable_uge {n} {x y : bitvec n} : decidable (bitvec.uge x y) := by apply_instance

  local attribute [reducible] slt
  local attribute [reducible] sgt
  local attribute [reducible] sle
  local attribute [reducible] sge

  instance decidable_slt {n} {x y : bitvec n} : decidable (bitvec.slt x y) := by apply_instance
  instance decidable_sgt {n} {x y : bitvec n} : decidable (bitvec.sgt x y) := by apply_instance
  instance decidable_sle {n} {x y : bitvec n} : decidable (bitvec.sle x y) := by apply_instance
  instance decidable_sge {n} {x y : bitvec n} : decidable (bitvec.sge x y) := by apply_instance

end comparison


def concat' {n : ℕ}(input: list (bitvec n)): ℕ :=
  list.foldl (λv (a:bitvec n), nat.shiftl v n + a.to_nat) 0 input

def concat_list {m : ℕ}(input: list (bitvec m)) (n : ℕ) : bitvec n :=
  bitvec.of_nat n (concat' input)

def concat_vec {w m : ℕ}(input: vector (bitvec w) m) (n : ℕ) : bitvec m :=
  bitvec.of_nat m (concat' input.to_list)

#eval concat_list [(1 : bitvec 4), 0] 8


--- Forms a list of bitvectors by taking a specific number of bits from parts of the
-- first argument.
--
-- The head of the list has the most-significant bits.
def split_to_list (x:ℕ) (w : ℕ) : ℕ → list (bitvec w)
| nat.zero := []
| (nat.succ n) := bitvec.of_nat w (nat.shiftr x (n*w)) :: split_to_list n

theorem length_split_to_list (x:ℕ) (w : ℕ) (m:ℕ) : list.length (split_to_list x w m) = m :=
begin
  induction m,
  case nat.zero { simp [split_to_list], },
  case nat.succ : m ind { simp [split_to_list, ind, nat.succ_add], },
end

/- Split a single bitvector into a list of bitvectors with most-significant bits first. -/
def split_list {n :ℕ} (x:bitvec n) (w:ℕ) : list (bitvec w) := split_to_list x.to_nat w (nat.div n w)

/- Split a single bitvector into a vector of bitvectors with most-significant bits first. -/
def split_vec {n :ℕ} (x:bitvec n) (w:ℕ) (m : ℕ) : vector (bitvec w) m :=
 ⟨split_to_list x.to_nat w m, length_split_to_list _ _ _⟩

end bitvec
