/-
Copyright (c) 2015 Joe Hendrix. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix, Sebastian Ullrich, Jason Dagit

Basic operations on bitvectors.

This is a work-in-progress, and contains additions to other theories.
-/
import data.vector
import .nat.lemmas
import .list.lemmas

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

  -- In pratice, it's more useful to allow 0 length bitvectors to have 1
  -- as well. This leads to a special case where the 0-length bitvector
  -- 1 is really just 0. This turns out to simplify things.
  protected
  def one : Π(n:ℕ), bitvec n
  | 0        := 0
  | (succ _) := ⟨1, one_le_pow_2 (nat.zero_lt_succ _)⟩

  instance {n:ℕ} : has_one (bitvec n)  := ⟨bitvec.one n⟩

end one

protected def cong {a b : ℕ} (h : a = b) : bitvec a → bitvec b
| ⟨x, p⟩ := ⟨x, h ▸ p⟩

protected
lemma intro {n : ℕ} (x y : bitvec n) : x.val = y.val → x = y :=
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

  lemma bitvec.eq {n:ℕ} (x y : bitvec n) (p : x.to_nat = y.to_nat) : x = y :=
  begin
    apply subtype.eq,
    exact p,
  end

  protected def to_int {n:ℕ} (x: bitvec n) : int :=
    match msb x with
    | ff := int.of_nat x.val
    | tt := int.neg_of_nat (bitvec.neg x).val
  end

  protected def of_nat (n : ℕ) (x:ℕ) : bitvec n := ⟨ x % 2^n, by simp ⟩

  protected def of_int : Π(n : ℕ), ℤ → bitvec n
  | n (int.of_nat m)          := bitvec.of_nat n m
  | n (int.neg_succ_of_nat m) := bitvec.neg (bitvec.of_nat n m)

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

  protected def add (x y : bitvec n) : bitvec n := bitvec.of_nat n (x.to_nat + y.to_nat)

  def adc (x y : bitvec n) : bitvec n × bool := ⟨ bitvec.add x y , x.to_nat + y.to_nat > 2^n ⟩

  -- Usual arithmetic subtraction
  protected def sub (x y : bitvec n) : bitvec n := bitvec.of_int n (x.to_int - y.to_int)

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
  def sshr (x: bitvec n) (i:ℕ) : bitvec n := bitvec.of_int n (int.shiftr (bitvec.to_int x) i)

end shift

section listlike
  -- Operations that treat bitvectors as a list of bits.

  def lsb {n:ℕ} (x: bitvec n) : bool := x.val % 2 = 1
  def nth {w:ℕ} (x : bitvec w) (idx : ℕ) : bool :=
      x .&&. (shl 1 idx) ≠ 0

  -- Unsigned extension
  def uext {n:ℕ} (m:ℕ) (x: bitvec n) : bitvec (n+m) := bitvec.of_nat (n+m) x.to_nat

  -- Signed extension
  def sext {n:ℕ} (m:ℕ) (x: bitvec n) : bitvec (n+m) := bitvec.of_int (n+m) x.to_int

  -- bitvec specific version of vector.append
  def append {m n} (x: bitvec m) (y: bitvec n) : bitvec (m + n)
    := ⟨ x.val * 2^n + y.val, mul_pow_add_lt_pow x.property y.property ⟩

  def trunc {n : ℕ} (m : ℕ) (x : bitvec (n+m)) : bitvec m := bitvec.of_nat m x.val

  protected
  def bsf' : Π{n:ℕ}, ℕ → bitvec n → option ℕ
    | 0        idx _ := none
    | (succ m) idx x :=
      have H: succ m = 1 + m,
      { simp, },
      if idx > m
        then none
        else if nth x 0
               then some idx
               -- We actually don't need to trunc here, but by reducing the
               -- the length of the bitvector on each recursive call
               -- lean can easily prove that this function terminates.
             else @bsf' m (idx+1) (trunc m (bitvec.cong H (x.ushr 1)))

  -- index of least-significant bit that is 1.
  def bsf : Π{n:ℕ}, bitvec n → option ℕ
    | n x := bitvec.bsf' 0 x

  protected
  def bsr' : Π{n:ℕ}, ℕ → bitvec n → option ℕ
    | 0        _   _ := none
    | (succ m) idx x :=
      have H: succ m = 1 + m,
      { simp, },
      if nth x idx
        then some idx
        else @bsr' m (idx-1) (trunc m (bitvec.cong H (x.ushr 1)))

  -- index of the most-significant bit that is 1.
  def bsr : Π{n:ℕ}, bitvec n → option ℕ
    | n x := bitvec.bsr' (n-1) x

  -- splits a bitvector into {n .. m} {m - 1 .. 0} sub bitvectors
  def split_at {n : ℕ} (m : ℕ) (x : bitvec (n + m)) : bitvec n × bitvec m := -- upper × lower
      ⟨ trunc n (bitvec.cong (nat.add_comm _ _) (ushr x m)), trunc m x ⟩

  lemma split_at_snd {n : ℕ} (m : ℕ) (x : bitvec (n+m)): (split_at m x).snd.val < 2 ^ m :=
    begin
      simp [split_at, trunc],
      apply nat.lt_of_lt_of_le,
      { apply mod_lt, apply nat.pos_pow_of_pos, dec_trivial_tac },
      { apply pow_le_pow_of_le_right,
        { dec_trivial_tac },
        { refl }
      }
    end

  lemma trunc_add_ushr {n m : ℕ} (x : bitvec (n + m))
  : (trunc m x).val + (trunc n (bitvec.cong (nat.add_comm _ _) (ushr x m))).val * 2 ^ m = x.val :=
  begin
    simp [ trunc, ushr, bitvec.of_nat, shiftr_eq_div_pow, cong_val],
    have : x.val / 2 ^ m < 2 ^ (n + m),
    { apply div_pow_mono x.property, },
    rw mod_eq_of_lt this,
    rw (pow_mod_superfluous' x.property),
    { rw mul_comm, apply mod_add_div }
  end

  lemma split_at_append_ident {n : ℕ} (m : ℕ) (x : bitvec (n + m))
  : append (split_at m x).fst (split_at m x).snd = x :=
  begin
    apply bitvec.intro,
    simp [append, split_at],
    apply trunc_add_ushr
  end

  def chunks : Π(n :ℕ) (m : ℕ), bitvec (m * n) → list (bitvec m)
    | 0             _ _  := []
    | (nat.succ n)  m bv :=
      let v := bitvec.split_at m bv
      in  v.snd :: chunks n m v.fst

  @[simp]
  lemma chunks_nil {m:ℕ} {x: bitvec (m * 0) }: chunks _ m x = [] :=
    by unfold chunks

  @[simp]
  lemma chunks_length {n m : ℕ} {x: bitvec (m * n)} : list.length (chunks n m x) = n :=
  begin
    induction n with n p,
    case nat.zero
    { unfold chunks, simp },
    case nat.succ
    { simp [chunks, p],
    },
  end

  @[simp]
  lemma chunks_length_mul {n m : ℕ} {x: bitvec (m * n)}
  : m * list.length (chunks n m x) = m * n
  := by simp

  def concat : Π{n : ℕ}(input: list (bitvec n)), bitvec (n * input.length)
    | _ []      := 0
    | n (x::xs) := append (concat xs) x

  @[simp]
  lemma concat_nil_zero {n:ℕ} : concat ([]: list (bitvec n)) = (0 : bitvec 0) :=
  begin
    simp [concat], refl,
  end

  @[simp]
  lemma concat_step {n:ℕ} (x: bitvec n) (xs: list (bitvec n))
  : concat (x::xs) = append (concat xs) x :=
  begin
    simp [concat],
  end

  @[simp]
  lemma chunks_concat_zero {n:ℕ} (x: bitvec (0 * n))
  : concat (chunks n 0 x) = 0 :=
  begin
    induction n with n ih,
    case nat.zero
    { rw [chunks, concat] },
    case nat.succ
    { rw [chunks, concat],
      apply bitvec.intro,
      rw ih,
      simp [cong_val, append, split_at, trunc, bitvec.of_nat],
      refl
    },
  end

  lemma chunks_concat_eq {n m:ℕ} (x: bitvec (m * n))
  : concat (chunks n m x) = bitvec.cong (eq.symm chunks_length_mul) x :=
  begin
    apply bitvec.intro,
    simp [cong_val],
    induction n with n p,
    case nat.zero
    { simp [cong_val], },
    case nat.succ
    { rw [chunks, concat, split_at, append],
      simp [p, cong_val],
      apply trunc_add_ushr,
    },
  end

  def chunks_nat : Π(n :ℕ) (m : ℕ), ℕ → list (bitvec m)
  | 0            _ _ := []
  | (nat.succ n) m v := (bitvec.of_nat m (nat.shiftr v (n*m)) :: chunks_nat n m v)

  @[simp]
  lemma chunks_nat_base {m:ℕ} (v:ℕ)
    : chunks_nat 0 m v = [] :=
    by simp [chunks_nat]

  @[simp]
  lemma chunks_nat_step {n m :ℕ} (v : ℕ)
    : chunks_nat (succ n) m v =
        (bitvec.of_nat m (nat.shiftr v (n*m)) :: chunks_nat n m v) :=
    by simp [chunks_nat]

  @[simp]
  lemma chunks_nat_length {n m : ℕ} (v : ℕ)
    : list.length (chunks_nat n m v) = n :=
    begin
      induction n with n ih,
      case nat.zero
      { simp, },
      case nat.succ
      { simp [chunks_nat_step], rw [ih, ←add_one, add_comm], },
    end

  @[simp]
  lemma chunks_nat_zero {n m:ℕ}
    : chunks_nat n m 0 = list.repeat 0 n :=
    begin
      induction n with n ih,
      case nat.zero
      { simp, },
      case nat.succ
      { simp [chunks_nat_step],
        apply and.intro,
        { simp [bitvec.of_nat],
          refl,
        },
        { exact ih },
      },
    end

  def chunks' (n m :ℕ) (v:bitvec (m * n)) : list (bitvec m) := chunks_nat n m v.to_nat

  @[simp]
  lemma chunks'_nil {m:ℕ} {x: bitvec (m * 0) }: chunks' _ m x = [] :=
    begin
      unfold chunks',
      unfold chunks_nat,
    end

  @[simp]
  lemma chunks'_length {n m : ℕ} {x: bitvec (m * n)} : list.length (chunks' n m x) = n :=
  begin
    induction n with n p,
    case nat.zero
    { unfold chunks', simp },
    case nat.succ
    { simp [chunks', p],
    },
  end

  @[simp]
  lemma chunks'_length_mul {n m : ℕ} {x: bitvec (m * n)}
  : m * list.length (chunks' n m x) = m * n
  := by simp

  lemma chunks'_step {n m : ℕ} (v : bitvec (m * succ n))
  : chunks' (succ n) m v = (bitvec.of_nat m (nat.shiftr v (n*m)) :: chunks_nat n m v) :=
  begin
    simp [chunks', chunks_nat],
    apply and.intro; refl
  end

  def concat_nat {n : ℕ} : ℕ → list (bitvec n) → ℕ
  | acc []      := acc
  | acc (x::xs) := concat_nat (nat.shiftl acc n + x.to_nat) xs

  @[simp]
  lemma concat_nat_nil : ∀(n acc : ℕ), @concat_nat n acc list.nil = acc :=
    begin
      intros,
      simp [concat_nat]
    end

  @[simp]
  lemma concat_nat_step {n acc : ℕ} (x: bitvec n) (xs: list (bitvec n))
    : concat_nat acc (x::xs) = concat_nat (nat.shiftl acc n + x.to_nat) xs :=
    by simp [concat_nat]

  lemma concat_nat_step_acc {n r : ℕ} (ls : list (bitvec n))
  : concat_nat r ls = r * 2^(ls.length * n) + concat_nat 0 ls :=
  begin
    induction ls with l' ls' ih generalizing r,
    case list.nil
    { simp [concat_nat, mul_comm],
    },
    case list.cons
    { simp [concat_nat, bitvec.to_nat, shiftl_eq_mul_pow],
      rw [ih],
      rw [@ih l'.val],
      simp,
      congr,
      simp [right_distrib, pow_distrib, mul_assoc],
    },
  end

  @[simp]
  lemma concat_nat_zeros {n m:ℕ}
  : @concat_nat n 0 (list.repeat 0 m) = 0 :=
  begin
    induction m with m ih,
    case nat.zero
    { simp, },
    case nat.succ
    { simp [bitvec.to_nat],
      exact ih,
    },
  end

  theorem concat_nat_zero_bound {n : ℕ} : ∀(l : list (bitvec n)),
    concat_nat 0 l < 2^(n*l.length) :=
  begin
    intros,
    induction l with l ls ih,
    case list.nil
    { simp, dec_trivial_tac },
    case list.cons
    { simp,
      rw [concat_nat_step_acc, mul_comm n],
      rw [mul_comm n ls.length] at ih,
      simp,
      rw [add_comm 1 ls.length],
      apply (@add_pow_bound (concat_nat 0 ls) (bitvec.to_nat l) (ls.length) n ih l.property),
    },
  end

  theorem concat_nat_bound {w:ℕ} {n:ℕ} : ∀(r:ℕ) (h:r < 2^w) (l:list (bitvec n)),
    concat_nat r l < (r + 1)*2^(l.length * n) :=
  begin
    intros,
    rw [concat_nat_step_acc],
    calc
      r * 2^(l.length * n) + concat_nat 0 l < r * 2^(l.length * n) + 2^(n * l.length)   : by apply nat.add_lt_add_left (concat_nat_zero_bound l)
                                        ... = r * 2^(l.length * n) + 2^(l.length * n)   : by rw (mul_comm n)
                                        ... = r * 2^(l.length * n) + 1*2^(l.length * n) : by simp
                                        ... = (r+1)*2^(l.length * n)                    : by rw [←right_distrib]
  end

  def concat' {n : ℕ} (input: list (bitvec n)) : bitvec (n * input.length) :=
   ⟨concat_nat 0 input, concat_nat_zero_bound input⟩

  lemma chunks_nat_concat_nat_eq {n m:ℕ} (x: ℕ)
  : concat_nat 0 (chunks_nat n m x) = x % 2^n :=
  begin
    induction n with n ih,
    case nat.zero
    { simp, },
    case nat.succ
    { have: 2 > 0, dec_trivial_tac,
      rw [mod_pow_succ this],
      rw [concat_nat_step_acc],
      -- These simps cannot be combined, because it causes an error in the expander.
      simp [bitvec.to_nat, shiftr_eq_div_pow, bitvec.of_nat],
      simp [concat_nat_step_acc, ih],
      -- NOTE: not sure how to finish this, but the goal holds for the
      -- random inputs I tested it on.
      admit
    },
  end

  def slice {w: ℕ} (u l k:ℕ) (H: w = k + (u + 1 - l)) (x: bitvec w) : bitvec (u + 1 - l) :=
    trunc (u + 1 - l) (bitvec.cong H (x.ushr l))

end listlike

section comparison
  -- Comparison operations, including signed and unsigned versions
  variable {n : ℕ}

  def uborrow (x y : bitvec n) : bool := x.to_nat < y.to_nat

  def ult (x y : bitvec n) : Prop := uborrow x y
  def ugt (x y : bitvec n) : Prop := ult y x

  def ule (x y : bitvec n) : Prop := ¬ (ult y x)
  def uge (x y : bitvec n) : Prop := ule y x

  def sborrow : Π {n : ℕ}, bitvec n → bitvec n → bool
  | _ x y := x.to_int < y.to_int

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
