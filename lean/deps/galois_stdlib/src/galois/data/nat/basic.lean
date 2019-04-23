-- This  file contains basic lemmas for nat
import ...algebra.order

namespace galois
namespace nat

open nat

/-- pred _ + _ rewrite rule. -/
theorem pred_add (m n : ℕ) : pred m + n = if m = 0 then n else pred (m + n) :=
begin
  cases m,
  case zero {
    simp,
  },
  case succ : m {
    have p : ¬(succ m = 0) := by trivial,
    simp [pred, p],
  },
end

/-- _ + pred _ rewrite rule. -/
theorem add_pred (m n : ℕ) : m + pred n = if n = 0 then m else pred (m + n) :=
begin
  cases n,
  case zero {
    simp,
  },
  case succ : n {
    have p : ¬(succ n = 0) := by trivial,
    simp [pred, p],
  },
end

-- Reduce x < y to theorem with addition
protected theorem lt_is_succ_le (x y : ℕ) : x < y ↔ x + 1 ≤ y := by trivial

-- Reduce succ x < succ y to x < y
protected
lemma succ_le_succ_iff (m n : ℕ) : succ m ≤ succ n ↔ m ≤ n := ⟨le_of_succ_le_succ, succ_le_succ⟩

-- Reduce succ x < succ y to x < y
protected
lemma succ_lt_succ_iff (m n : ℕ) : succ m < succ n ↔ m < n := ⟨lt_of_succ_lt_succ, succ_lt_succ⟩

theorem lt_succ_iff (m n : ℕ) : m < nat.succ n ↔ m ≤ n := nat.succ_le_succ_iff m n

-- This rewrites a subtraction on left-hand-side of inequality into a predicate
-- involving addition.
protected lemma sub_lt_to_add (a m n : ℕ) : a - n < m ↔ (a < m + n ∧ (n ≤ a ∨ 0 < m)) :=
begin
  revert a m,
  induction n,
  case zero {
    intros a m,
    simp [nat.zero_le],
  },
  case succ : n ind {
    intros a m,
    cases a,
    case zero {
      simp [zero_sub, zero_lt_succ, not_succ_le_zero],
    },
    case succ {
      simp [add_succ, nat.succ_lt_succ_iff, nat.succ_le_succ_iff, ind],
    },
  },
end

-- This rewrites a subtraction on right-hand side of inequality into an addition.
protected lemma lt_sub_iff (a m n : ℕ) : a < m - n ↔ a + n < m :=
begin
  revert n,
  induction m with m ind,
  { simp [nat.lt_is_succ_le, add_succ, not_succ_le_zero, zero_sub],
  },
  { intro n,
    cases n with n,
    { simp, },
    { simp [nat.succ_lt_succ_iff, ind],
    },
  },
end

lemma lt_one_is_zero (x:ℕ) : x < 1 ↔ x = 0 :=
begin
  constructor,
  { intros x_lt_1,
    apply eq_zero_of_le_zero (le_of_lt_succ x_lt_1),
  },
  { intros, simp [a], exact (of_as_true trivial),
  }
end

section -- mathlib copies
variables {m n k : ℕ}

theorem pred_sub (n m : ℕ) : pred n - m = pred (n - m) :=
by rw [← sub_one, nat.sub_sub, one_add]; refl


protected theorem lt_of_sub_lt_sub_right : m - k < n - k → m < n :=
lt_imp_lt_of_le_imp_le (λ h, nat.sub_le_sub_right h k)

protected theorem add_lt_of_lt_sub_right (h : m < n - k) : m + k < n :=
@nat.lt_of_sub_lt_sub_right _ _ k (by rwa nat.add_sub_cancel)

protected theorem add_lt_of_lt_sub_left (h : m < n - k) : k + m < n :=
by rw add_comm; exact nat.add_lt_of_lt_sub_right h

protected theorem le_sub_right_of_add_le (h : m + k ≤ n) : m ≤ n - k :=
by rw ← nat.add_sub_cancel m k; exact nat.sub_le_sub_right h k

protected theorem lt_sub_right_of_add_lt (h : m + k < n) : m < n - k :=
lt_of_succ_le $ nat.le_sub_right_of_add_le $
by rw succ_add; exact succ_le_of_lt h

protected theorem lt_sub_left_of_add_lt (h : k + m < n) : m < n - k :=
nat.lt_sub_right_of_add_lt (by rwa add_comm at h)

protected theorem lt_sub_left_iff_add_lt : n < k - m ↔ m + n < k :=
⟨nat.add_lt_of_lt_sub_left, nat.lt_sub_left_of_add_lt⟩

protected theorem le_sub_left_of_add_le (h : k + m ≤ n) : m ≤ n - k :=
nat.le_sub_right_of_add_le (by rwa add_comm at h)

protected theorem lt_sub_right_iff_add_lt : m < k - n ↔ m + n < k :=
by rw [nat.lt_sub_left_iff_add_lt, add_comm]

protected theorem lt_add_of_sub_lt_left : n - k < m → n < k + m :=
lt_imp_lt_of_le_imp_le nat.le_sub_left_of_add_le

protected theorem sub_le_left_of_le_add : n ≤ k + m → n - k ≤ m :=
le_imp_le_of_lt_imp_lt nat.add_lt_of_lt_sub_left

protected theorem sub_lt_left_iff_lt_add (H : n ≤ k) : k - n < m ↔ k < n + m :=
⟨nat.lt_add_of_sub_lt_left,
 λ h₁,
  have succ k ≤ n + m,   from succ_le_of_lt h₁,
  have succ (k - n) ≤ m, from
    calc succ (k - n) = succ k - n : by rw (succ_sub H)
          ...     ≤ n + m - n      : nat.sub_le_sub_right this n
          ...     = m              : by rw nat.add_sub_cancel_left,
  lt_of_succ_le this⟩

protected lemma sub_le_self (n m : ℕ) : n - m ≤ n :=
  nat.sub_le_left_of_le_add (nat.le_add_left _ _)

end

theorem pow_add (a m n : ℕ) : a^(m + n) = a^m * a^n :=
by induction n; simp [*, pow_succ, mul_assoc]

lemma mul_pow_add_lt_pow {x y n m:ℕ} (Hx: x < 2^m) (Hy: y < 2^n) : x * 2^n + y < 2^(m + n) :=
  calc
    x*2^n + y < x*2^n + 2^n   : nat.add_lt_add_left Hy (x*2^n)
          ... = (x + 1) * 2^n : begin rw right_distrib, simp end
          ... ≤ 2^m * 2^n     : nat.mul_le_mul_right (2^n) (succ_le_of_lt Hx)
          ... = 2^(m + n)     : eq.symm (nat.pow_add _ _ _)

end nat
end galois
