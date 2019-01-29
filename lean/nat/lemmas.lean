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

lemma one_le_pow_2 {n: ℕ} (h : n > 0) : 1 < 2^n :=
  calc 1   < 2^1 : by dec_trivial_tac
       ... ≤ 2^n : nat.pow_le_pow_of_le_right (by dec_trivial_tac) h

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

lemma le_mul_succ {n m : ℕ} : m ≤ m * (succ n) :=
  begin
    calc   m ≤ m * 1 : by simp
         ... ≤ m * (nat.succ n) : begin
                                    apply nat.mul_le_mul_left,
                                    apply nat.succ_le_succ,
                                    apply nat.zero_le
                                  end
  end

lemma mul_right {m n k: ℕ} : m = n → k * m = k * n :=
  begin
    induction k with k ih,
    case nat.zero
    { simp, },
    case nat.succ
    { intros,
      simp [right_distrib, ih a, a],
    }
  end

lemma add_right {m n k: ℕ} : m = n → k + m = k + n :=
  begin
    induction k with k ih,
    case nat.zero
    { intros, simp, assumption },
    case nat.succ
    { intros, simp [ih, a] }
  end

lemma pow_intro {b i j :ℕ}
  : i = j → b^i = b^j :=
  begin
    intros,
    rw a,
  end

lemma pow_distrib {b i j :ℕ}
  : b^(i+j) = b^i*b^j :=
  begin
    induction i with i ih,
    case nat.zero
    { simp, },
    case nat.succ
    { rw [pow_succ, nat.mul_assoc (b^i), nat.mul_comm b,
          ←nat.mul_assoc (b^i), ←ih, ←pow_succ],
      simp,
    },
  end

lemma two_pow_div_eq {x m n : ℕ}
  : 2^(m * succ n)/2^m = 2^(m*n) :=
  begin
    have two_pos: 0 < 2, dec_trivial_tac,
    have: 2^(m * succ n) ≥ 2^m,
    { apply pow_le_pow_of_le_right two_pos,
      apply le_mul_succ,
    },
    have pow_two_pos: 2^m > 0,
    { apply (pos_pow_of_pos _ two_pos),
    },
    have two_pow_mn_big: 1 ≤ 2^(m*n),
    { apply nat.succ_le_of_lt,
      apply (pos_pow_of_pos _ two_pos),
    },
    have two_pow_distrib: 2^(m*succ n) = 2^(m*n + m),
    { apply pow_intro,
      rw [←add_one, left_distrib],
      simp,
    },
    calc
    2^(m * succ n)/2^m = (2^(m*succ n) - 2^m)/2^m + 1   : by apply div_eq_sub_div (pos_pow_of_pos m two_pos) this
                   ... = (2^(m*n + m) - 2^m)/2^m + 1    : by rw two_pow_distrib
                   ... = (2^(m*n)*2^m - 2^m)/2^m + 1    : by rw pow_distrib
                   ... = (2^m*2^(m*n) - 2^m)/2^m + 1    : by rw mul_comm
                   ... = (2^m*2^(m*n) - 2^m*1)/2^m + 1  : by simp
                   ... = 2^m*(2^(m*n) - 1)/2^m + 1      : by rw ←nat.mul_sub_left_distrib
                   ... = (2^(m*n) - 1)*2^m/2^m + 1      : by rw mul_comm
                   ... = (2^(m*n) - 1) + 1              : by rw (nat.mul_div_left _ pow_two_pos)
                   ... = 2^(m*n) - 1 + 1                : by simp
                   ... = 2^(m*n)                        : nat.sub_add_cancel two_pow_mn_big

  end

lemma le_of_add_right {n m : ℕ}
  : n + m ≥ m :=
  begin
    apply le_add_of_nonneg_left,
    apply zero_le,
  end

lemma le_of_add_left {n m : ℕ}
  : n + m ≥ n :=
  begin
    apply le_add_of_nonneg_right,
    apply zero_le,
  end

@[simp]
lemma min_add_eq_right {n m : ℕ}
  : min (n + m) m = m :=
  begin
    apply min_eq_right,
    apply le_of_add_right,
  end

@[simp]
lemma min_add_eq_left {n m : ℕ}
  : min (n + m) n = n :=
  begin
    apply min_eq_right,
    apply le_of_add_left,
  end

lemma div_left {x y z k : ℕ} (H: k > 0) (Hlt: x < z * k)
  : x / k < (z * k) / k :=
  begin
    intros,
    rw (div_lt_iff_lt_mul _ _ H),
    rw mul_div_left _ H,
    assumption,
  end

lemma div_of_pow_two_lt_pow_add {n m x : ℕ} (h: x < 2^(m * succ n))
  : x/2^m < 2^(m*n) :=
  begin
    have two_pos: 0 < 2, dec_trivial_tac,
    have pow_m_pos: 0 < 2^m,
    { apply pos_pow_of_pos _ two_pos, },
    have: 2^(m * succ n) = 2^(m*n) * 2^m,
    { rw [←add_one, left_distrib], simp,
      rw [add_comm, pow_distrib],
    },
    have: x < 2^(m*n) * 2^m,
    { rwa this at h,
    },
    rwa ←div_lt_iff_lt_mul x (2^(m*n)) pow_m_pos at this,
  end

lemma mod_div_of_pow_two_eq {n m x : ℕ} (h: x < 2^(m * succ n))
  : x % 2 ^ m + x / 2 ^ m % 2 ^ (m * n) * 2 ^ m = x :=
  begin
    have: x/2^m < 2^(m*n),
    { exact div_of_pow_two_lt_pow_add h, },
    rw [mod_eq_of_lt this],
    rw [mul_comm],
    rw mod_add_div,
  end

lemma gt_of_not_zero {n:ℕ}
  : (¬n = 0) → n > 0 :=
  begin
    intro h,
    cases n,
    case nat.zero
    { exfalso, apply h, refl },
    case nat.succ
    { apply nat.zero_lt_succ },
  end

lemma lt_div_pow {x n m : ℕ} (H: x < 2^(n + m))
  : x / 2 ^ m < 2 ^ n :=
  begin
    have: 2^m > 0,
    { apply pos_pow_of_pos, dec_trivial_tac },
    rw div_lt_iff_lt_mul x (2^n) this,
    rw [←pow_distrib],
    exact H
  end

lemma pow_mod_superfluous' {x n m : ℕ} (H : x < 2^(n + m))
  : x / 2 ^ m % 2 ^ n = x / 2^m :=
  begin
    apply mod_eq_of_lt,
    apply lt_div_pow H,
  end

lemma lt_of_mul {n m k : ℕ}
  : k > 0 → n < m → n < m * k :=
  begin
    intros,
    cases k,
    { cases a, },
    { intros,
      rw [succ_eq_add_one, left_distrib],
      simp,
      apply (nat.lt_add_right _ _ _ a_1),
    },
  end

lemma shiftr_mono {n m k : ℕ} (H: n < m)
  : nat.shiftr n k < m :=
  begin
    have : 0 < 2^k,
    { apply pos_pow_of_pos,
      dec_trivial_tac
    },
    rw [shiftr_eq_div_pow, div_lt_iff_lt_mul _ _ this],
    apply lt_of_mul this H,
  end

lemma add_pow_bound {c v k n : ℕ} (Hc: c < 2^(k*n)) (Hv: v < 2^n)
  : c + v * 2^(k*n) < 2^((k + 1) * n) :=
  begin
    calc
    c + v * 2^(k*n) < 2^(k*n) + v * 2^(k*n) : by apply nat.add_lt_add_right Hc
                ... = (v + 1) * 2^(k*n)     : by simp [right_distrib]
                ... ≤ 2^n * 2^(k*n)         : begin apply (nat.mul_le_mul_right), apply (nat.succ_le_of_lt Hv) end
                ... = 2^((k+1) * n)         : begin simp [pow_distrib, right_distrib], end
  end
