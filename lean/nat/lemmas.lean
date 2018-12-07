/-
Copyright (c) 2018 Galois. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Additional lemmas for natural numbers.

This is a work-in-progress, and contains additions to other theories.
-/

import tactic.find
import ..tactic

open nat

lemma lt_one_is_zero {x:ℕ} : x < 1 ↔ x = 0 :=
  begin
    constructor,
    { intros,
      apply eq_zero_of_le_zero (le_of_lt_succ _),
      assumption },
    { intros, simp [a], dec_trivial_tac }
  end

lemma pow_mul {b n m :ℕ} : b^n * b^m = b^(n+m) :=
  begin
    induction m with m,
    case nat.zero
    { simp },
    case nat.succ
    { rw [pow_succ, ←mul_assoc (b^n), m_ih, ←pow_succ] }
  end

lemma mul_pow_add_lt_pow {x y n m:ℕ} (Hx: x < 2^m) (Hy: y < 2^n) : x * 2^n + y < 2^(m + n) :=
  calc
    x*2^n + y < x*2^n + 2^n   : nat.add_lt_add_left Hy (x*2^n)
          ... = (x + 1) * 2^n : begin rw right_distrib, simp end
          ... ≤ 2^m * 2^n     : nat.mul_le_mul_right (2^n) (succ_le_of_lt Hx)
          ... = 2^(m + n)     : pow_mul


lemma min_sub_self_right {a b : ℕ}: min a (a - b) = a - b :=
  begin apply min_eq_right, apply sub_le end

lemma min_sub_self_left {a b : ℕ}: min (a - b) a = a - b :=
  begin apply min_eq_left, apply sub_le end

lemma div_lt_of_lt_mul {m n : ℕ} : ∀ {k} (Hk : k > 0), m < k * n → m / k < n
  | 0        Hk h := by apply absurd Hk (lt_irrefl 0)
  | (succ k) Hk h :=
    suffices succ k * (m / succ k) < succ k * n, from lt_of_mul_lt_mul_left this (zero_le _),
    calc
      succ k * (m / succ k) ≤ m % succ k + succ k * (m / succ k) : le_add_left _ _
                        ... = m                                  : by rw mod_add_div
                        ... < succ k * n                         : h

lemma div_pow_mono' {x n i : ℕ} (h: x < 2^n) (hi : i ≤ n)
  : x / 2 ^ i < 2 ^ (n - i) :=
  begin
    apply div_lt_of_lt_mul,
    { apply pos_pow_of_pos, dec_trivial_tac },
    { rw pow_mul, rw (nat.add_sub_of_le hi), exact h }
  end

@[simp]
-- mod_lt specialized to powers of 2
lemma mod_lt_pow_2 (x n : ℕ) : x % 2 ^ n < 2 ^ n :=
  begin
    apply (mod_lt _),
    apply (pos_pow_of_pos _ _),
    simp [zero_lt_succ]
  end

lemma sub_add_lt_self (a b c : ℕ) (Hab: a > b) (Hbc : b > c) : a - b + c < a :=
  begin
    induction c with c generalizing a b,
    case nat.zero
    { apply sub_lt_of_pos_le _ _ Hbc (le_of_lt Hab) },
    { cases b,
      case nat.zero
      { have : false, { apply not_lt_zero _ Hbc},
        contradiction,
      },
      { cases a,
        case nat.zero
        { have : false, { apply not_lt_zero _ Hab },
          contradiction,
        },
        case nat.succ
        { have Hbc: b > c, { apply lt_of_succ_lt_succ Hbc },
          have Hab: a > b, { apply lt_of_succ_lt_succ Hab },
          have := c_ih _ _ Hab Hbc,
          simp,
          rw [nat.add_comm],
          apply succ_lt_succ this,
        }
      },
    },
  end

lemma div_pow_mono {x n i : ℕ} (h: x < 2^n) : x / 2^i < 2^n :=
  calc
      x / 2^i ≤ x   : nat.div_le_self x (2^i)
          ... < 2^n : h

lemma pow_mod_superfluous {x n m : ℕ} (H : x < 2 ^ n) (Hm: m ≤ n): (x / 2 ^ m % 2 ^ (n - m)) = x / 2 ^ m :=
begin
  apply mod_eq_of_lt, apply (div_pow_mono' H Hm)
end

lemma nat_sub_le_self (a b : ℕ) (h: a ≥ b) : a - b ≤ a :=
  begin
    apply le_of_lt_succ,
    apply sub_lt_succ
  end
