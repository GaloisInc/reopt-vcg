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

lemma sshr_in_range_n_le_i {n i x : ℕ} (hx: x < 2^n) (hni: n ≤ i) : 2^n - 2^(n-i) + x/2^i < 2^n :=
  begin
    simp [nat.sub_eq_zero_of_le hni],
    rw div_eq_of_lt,
    { simp,
      apply sub_lt_of_pos_le,
      { dec_trivial_tac },
      { apply pos_pow_of_pos,
        dec_trivial_tac,
      },
    },
    { apply nat.lt_of_lt_of_le,
      { exact hx },
      { apply pow_le_pow_of_le_right,
        dec_trivial_tac,
        exact hni,
      },
    },
  end

lemma sshr_in_range_i_lt_n_2 {n i x : ℕ} (hx: x < 2^n) (hni: i < n) : 2^n - 2^(n-i) + x/2^i < 2^n :=
  begin
    cases i, -- This is slightly annoying, but we need to prove
             -- the i = 0 case separately so we can use i > 0
             -- for sub_lt_of_pos_le as the argument to
             -- pow_lt_pow_of_lt_right in the other case.
    case nat.zero
    { simp, rw nat.sub_self (2^n), simp, exact hx },
      case nat.succ
      { have i_lt_n : succ i ≤ n,
        { apply le_of_lt hni },
        have : x/2^succ i < 2^(n-succ i),
        { apply div_lt_of_lt_mul,
        apply pos_pow_of_pos,
        dec_trivial_tac,
        rw [pow_mul, add_sub_of_le],
        apply hx,
        apply i_lt_n
      },
      apply sub_add_lt_self (2^n) (2^(n-succ i)) (x/2^(succ i)) _ this,
      apply pow_lt_pow_of_lt_right (lt_succ_self _)
                                   (sub_lt_of_pos_le _ _ (nat.zero_lt_succ i) i_lt_n)
    }
  end

lemma sshr_in_range_i_lt_n_i_pos {n i x : ℕ} (hx: x < 2^n) (hni: i < n) (hipos: i > 0)
: 2^n - 2^(n-i) + x/2^i < 2^n :=
  begin
  { have i_le_n : i ≤ n, { apply le_of_lt hni },
    have x_div_lt : x/2^i < 2^(n-i),
    { apply div_lt_of_lt_mul,
      apply pos_pow_of_pos,
      dec_trivial_tac,
      rw [pow_mul, add_sub_of_le],
      apply hx,
      apply i_le_n
    },
    apply sub_add_lt_self (2^n) (2^(n-i)) (x/2^i) _ x_div_lt,
    apply pow_lt_pow_of_lt_right,
    { dec_trivial_tac },
    { apply sub_lt_of_pos_le i n hipos,
      apply le_of_lt hni
    },
  }
  end

lemma sshr_in_range_i_lt_n {n i x : ℕ} (hx: x < 2^n) (hni: i < n) : 2^n - 2^(n-i) + x/2^i < 2^n :=
  begin
    -- We case on i because when i is positive, the cruxt of the
    -- proof is applying pow_lt_pow_of_lt_right (which requires i > 0)
    -- (see sshr_in_range_i_lt_n_i_pos).
    --
    -- The case when i = 0 basically follows from hx once you
    -- simplify.
    by_cases i_cmp_zero : i > 0,
    { apply sshr_in_range_i_lt_n_i_pos hx hni i_cmp_zero },
    { have i_zero : i = 0,
      { apply eq_zero_of_le_zero,
        apply le_of_not_gt i_cmp_zero,
      },
      simp [i_zero, nat.sub_self (2^n)],
      exact hx
    },
  end

lemma sshr_in_range {n i x : ℕ} (h: x < 2^n) : 2^n - 2^(n-i) + x/2^i < 2^n :=
  begin
    by_cases this : n ≤ i,
    { apply sshr_in_range_n_le_i h this },
    { apply sshr_in_range_i_lt_n h (lt_of_not_ge this) },
  end

lemma pow_mod_superfluous {x n m : ℕ} (H : x < 2 ^ n) (Hm: m ≤ n): (x / 2 ^ m % 2 ^ (n - m)) = x / 2 ^ m :=
begin
  apply mod_eq_of_lt, apply (div_pow_mono' H Hm)
end
