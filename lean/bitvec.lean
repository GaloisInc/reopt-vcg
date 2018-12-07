/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich, Jason Dagit

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.vector
import .nat.lemmas

import tactic.find

import .tactic -- for dec_trivial_tac

-- A `bitvec n` is a subtype of natural numbers such that the value of
-- the bitvec is strictly less than 2^n.
@[reducible]
def bitvec (sz:ℕ) :=
  { x : ℕ // x < (2 ^ sz) }

namespace bitvec
open nat
open int
open vector

section zero

  -- Create a zero bitvector
  protected
  def zero (n : ℕ) : bitvec n :=
    ⟨0, nat.pos_pow_of_pos n dec_trivial⟩

  -- bitvectors have a zero, at every length
  instance {n:ℕ} : has_zero (bitvec n) := ⟨bitvec.zero n⟩

  @[simp]
  lemma bitvec_zero_zero (x : bitvec 0) : x.val = 0 :=
    begin
      cases x,
      { simp [nat.pow_zero, lt_one_is_zero] at x_property,
        simp, assumption
      }
    end

end zero

section one

  -- Create a bitvector with the constant one, doing so requires
  -- the bitvector to have positive length.
  protected
  def one_of_pos_len (n: ℕ) (H : n > 0) : bitvec n :=
    ⟨1, calc
          1   < 2^1 : by dec_trivial_tac
          ... ≤ 2^n : by apply (pow_le_pow_of_le_right (zero_lt_succ _) (succ_le_of_lt H))⟩

  -- In pratice, it's more useful to allow 0 length bitvectors to have 1
  -- as well. This leads to a special case where the 0-length bitvector
  -- 1 is really just 0. This turns out to simplify things.
  protected
  def one : Π(n:ℕ), bitvec n
  | 0        := bitvec.zero 0
  | (succ m) := bitvec.one_of_pos_len (succ m) (nat.zero_lt_succ m)

  instance {n:ℕ} : has_one (bitvec n)  := ⟨bitvec.one n⟩

end one

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

-- Most significant bit
def msb {n:ℕ} (x: bitvec n) : bool := (nat.shiftl x (n-1)) = 1

-- 2s complement negation
protected def neg {n:ℕ} (x : bitvec n) : bitvec n :=
  ⟨if x.val = 0 then 0 else 2^n - x.val,
   begin
     by_cases (x.val = 0),
     { simp [h], apply pos_pow_of_pos, dec_trivial_tac },
     { simp [h],
       have pos : 0 < 2^n - x.val, { apply nat.sub_pos_of_lt x.property },
       have x_val_pos: 0 < x.val, { apply nat.pos_of_ne_zero h },
       apply sub_lt_of_pos_le x.val (2^n) x_val_pos,
       apply le_of_lt x.property,
     }
    end⟩

section conversion
  -- Operations for converting to/from bitvectors
  variable {α : Type}

  protected def to_nat {n : nat} (v : bitvec n) : nat := v.val

  protected def to_int {n:ℕ} (x: bitvec n) : int :=
    match msb x with
    | ff := int.of_nat x.val
    | tt := int.neg_of_nat (bitvec.neg x).val
  end

  protected def of_nat (n : ℕ) (x:ℕ) : bitvec n := ⟨ x % 2^n, by simp ⟩

  protected def of_int : Π (n : ℕ), int → bitvec (succ n)
  | n (int.of_nat m)          := bitvec.of_nat (succ n) m
  | n (int.neg_succ_of_nat m) := bitvec.neg (bitvec.of_nat (succ n) m)

  theorem of_nat_to_nat {n : ℕ} (x : bitvec n)
  : bitvec.of_nat n (bitvec.to_nat x) = x :=
    begin
      cases x,
      simp [bitvec.to_nat, bitvec.of_nat],
      apply mod_eq_of_lt x_property,
    end

  theorem to_nat_of_nat {k n : ℕ}
  : bitvec.to_nat (bitvec.of_nat k n) = n % 2^k :=
    begin
      simp [bitvec.of_nat, bitvec.to_nat]
    end

end conversion

section bitwise

  -- bitwise negation
  def not {w:ℕ} (x: bitvec w) : bitvec w := ⟨2^w - x.val - 1,
    begin
      have xval_pos : 0 < x.val + 1,
      { apply (succ_pos x.val) },
      apply (sub_lt _ xval_pos),
      apply pos_pow_of_pos,
      apply (succ_pos 1)
    end⟩

  -- logical bitwise and
  def and {w:ℕ} (x y : bitvec w) : bitvec w := bitvec.of_nat w (nat.land x.val y.val)
  -- logical bitwise or
  def or  {w:ℕ} (x y : bitvec w) : bitvec w := bitvec.of_nat w (nat.lor  x.val y.val)
  -- logical bitwise xor
  def xor {w:ℕ} (x y : bitvec w) : bitvec w := bitvec.of_nat w (nat.lxor x.val y.val)

  infix `.&&.`:70 := and
  infix `.||.`:65 := or

end bitwise

section arith
  -- Arithmetic operations on bitvectors
  variable {n : ℕ}

  -- Add with carry (no overflow)
  def adc (x y : bitvec n) (c : bool) : bitvec n × bool :=
    let c₁ := if c then 1 else 0,
        r  := x.val + y.val + c₁ in
    ⟨ bitvec.of_nat n r, r ≥ 2^n ⟩

  protected def add (x y : bitvec n) : bitvec n := (adc x y ff).1

  -- Subtract with borrow
  def sbb (x y : bitvec n) (b : bool) : bool × bitvec n :=
    let b₁ : bitvec n := if b then 1 else 0,
        r  := match bitvec.adc x (bitvec.neg y) ff with
              | (z, b₂) := bitvec.adc z (bitvec.neg b₁) ff
              end
    in ⟨ if b then y.val + 1 > x.val else y.val > x.val , r.1 ⟩

  -- Usual arithmetic subtraction
  protected def sub (x y : bitvec n) : bitvec n := (sbb x y ff).2

  instance : has_add (bitvec n)  := ⟨bitvec.add⟩
  instance : has_sub (bitvec n)  := ⟨bitvec.sub⟩
  instance : has_neg (bitvec n)  := ⟨bitvec.neg⟩

  protected def mul (x y : bitvec n) : bitvec n := bitvec.of_nat n (x.val * y.val)

  instance : has_mul (bitvec n) := ⟨bitvec.mul⟩

  def bitvec_pow (x: bitvec n) (k:ℕ) : bitvec n := bitvec.of_nat n (x.val^k)

  instance bitvec_has_pow : has_pow (bitvec n) ℕ := ⟨bitvec_pow⟩

end arith

section shift
  -- Shift related operations, including signed and unsigned shift.

  variable {n : ℕ}

  -- shift left
  def shl (x : bitvec n) (i : ℕ) : bitvec n := bitvec.of_nat n (nat.shiftl x.val i)

  -- unsigned shift right
  def ushr (x : bitvec n) (i : ℕ) : bitvec n := bitvec.of_nat n (nat.shiftr x.val i)

  -- signed shift right
  def sshr (x: bitvec n) (i:ℕ) : bitvec n :=
    match n with
    | 0      := 0
    | succ m := bitvec.of_int m (int.shiftr (bitvec.to_int x) i)
    end

end shift

section listlike
  -- Operations that treat bitvectors as a list of bits.

  def lsb {n:ℕ} (x: bitvec n) : bool := x.val % 2 = 1
  def nth {w:ℕ} (x : bitvec w) (idx : ℕ) : bool :=
      x .&&. (shl 1 idx) ≠ 0

  def zext {n:ℕ} (m:ℕ) (x: bitvec n) : bitvec (n+m) :=
    ⟨ x.val, calc
               x.val < 2^n     : x.property
                 ... ≤ 2^(n+m) : begin
                                   apply pow_le_pow_of_le_right, dec_trivial_tac,
                                   apply le_add_right
                                 end⟩

  -- bitvec specific version of vector.append
  def append {m n} (x: bitvec m) (y: bitvec n) : bitvec (m + n)
    := ⟨ x.val * 2^n + y.val, mul_pow_add_lt_pow x.property y.property ⟩

  def trunc {n : ℕ} (x : bitvec n) (m : ℕ) : bitvec (min n m) := bitvec.of_nat (min n m) x.val

  -- splits a bitvector into {n .. m} {m - 1 .. 0} sub bitvectors
  def split_at {n : ℕ} (m : ℕ) (x : bitvec n) : bitvec (n - m) × bitvec (min n m) := -- upper × lower
    ⟨ bitvec.cong min_sub_self_right (trunc (ushr x m) (n - m)), trunc x m ⟩

  def split_at' {n m : ℕ} (H : m ≤ n) (x : bitvec n) : bitvec (n - m) × bitvec m := -- upper × lower
      ⟨ (split_at m x).fst, bitvec.cong (min_eq_right H) ((split_at m x).snd) ⟩

  lemma split_at_snd {n : ℕ} (m : ℕ) (x : bitvec n): (split_at m x).snd.val < 2 ^ m :=
    begin
      simp [split_at, trunc],
      apply nat.lt_of_lt_of_le,
      { apply mod_lt, apply nat.pos_pow_of_pos, dec_trivial_tac },
      { apply pow_le_pow_of_le_right,
        { dec_trivial_tac },
        { apply min_le_right }
      }
    end

  lemma bitvec_intro {n : ℕ} (x y : bitvec n) : x.val = y.val → x = y :=
  begin
    intro H,
    cases x, cases y, congr,
    simp at H, assumption
  end

  lemma cong_val {n m : ℕ} {H : n = m} (x : bitvec n)
  : (bitvec.cong H x).val = x.val :=
  begin
    cases x, simp [bitvec.cong]
  end

  lemma trunc_add_ushr {n m : ℕ} (H : m ≤ n) (x : bitvec n)
  : (trunc x m).val + (trunc (ushr x m) (n - m)).val * 2 ^ m = x.val :=
  begin
    simp [ trunc, min_eq_right H, min_eq_right (sub_le n m), ushr, bitvec.of_nat, shiftr_eq_div_pow],
    have : 2^(n - m) ≤ 2^n,
    { apply pow_le_pow_of_le_right,
      { dec_trivial_tac },
      { apply nat_sub_le_self _ _ H, },
    },
    have : x.val / 2 ^ m < 2 ^ n, { apply div_pow_mono x.property },
    rw mod_eq_of_lt this,
    rw (pow_mod_superfluous x.property H),
    { rw mul_comm, apply mod_add_div }
  end

  lemma split_at'_append_ident {n : ℕ} (m : ℕ) (H : m ≤ n) (x : bitvec n)
  : append (split_at' H x).fst (split_at'  H x).snd = bitvec.cong (eq.symm (nat.sub_add_cancel H)) x :=
  begin
    apply bitvec_intro,
    simp [append, split_at', cong_val, split_at],
    apply (trunc_add_ushr H)
  end

end listlike

section comparison
  -- Comparison operations, including signed and unsigned versions
  variable {n : ℕ}

  def uborrow (x y : bitvec n) : bool := prod.fst (sbb x y ff)

  def ult (x y : bitvec n) : Prop := uborrow x y
  def ugt (x y : bitvec n) : Prop := ult y x

  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge (x y : bitvec n) : Prop := ule y x

  def sborrow : Π {n : ℕ}, bitvec n → bitvec n → bool
  | 0        _ _ := ff
  | (succ n) x y :=
    match (msb x, msb y) with
    | (tt, ff) := tt
    | (ff, tt) := ff
    | (ff, ff) := uborrow x y
    | (tt, tt) := uborrow (bitvec.neg y) (bitvec.neg x) -- -x < -y when y < x
    end

  def slt (x y : bitvec n) : Prop := sborrow x y
  def sgt (x y : bitvec n) : Prop := slt y x
  def sle (x y : bitvec n) : Prop := ¬ (slt y x)
  def sge (x y : bitvec n) : Prop := sle y x

end comparison

section instances
  -- misc. instances that don't belong in one of the sections above

  instance (n : nat) : has_repr (bitvec n) := ⟨repr⟩

  instance decidable_ult {n} {x y : bitvec n} : decidable (bitvec.ult x y) := bool.decidable_eq _ _

  instance decidable_ugt {n} {x y : bitvec n} : decidable (bitvec.ugt x y) := bool.decidable_eq _ _

  instance decidable_eq {n:ℕ} : decidable_eq (bitvec n) := subtype.decidable_eq

end instances

end bitvec
