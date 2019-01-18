import data.nat.basic

-- This  file contains basic lemmas for nat
namespace nat

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

-- Reduce succ x < succ y
protected lemma succ_lt_succ_iff : ∀{m n : ℕ}, succ n < succ m ↔ n < m :=
begin
  intros m n,
  simp [nat.lt_is_succ_le, succ_le_succ_iff],
end

-- This rewrites a subtraction on left-hand-side of inequality into a predicate
-- involving addition.
protected lemma sub_lt_to_add (a m n : ℕ) : a - n < m ↔ (a < m + n ∧ (n ≤ a ∨ 0 < m)) :=
begin
  revert a m,
  induction n,
  case zero {
    intros a m,
    simp [zero_le],
  },
  case succ : n ind {
    intros a m,
    cases a,
    case zero {
      simp [zero_sub, zero_lt_succ, not_succ_le_zero],
    },
    case succ {
      simp [add_succ, nat.succ_lt_succ_iff, succ_le_succ_iff, ind],
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

lemma mul_pow_add_lt_pow {x y n m:ℕ} (Hx: x < 2^m) (Hy: y < 2^n) : x * 2^n + y < 2^(m + n) :=
  calc
    x*2^n + y < x*2^n + 2^n   : nat.add_lt_add_left Hy (x*2^n)
          ... = (x + 1) * 2^n : begin rw right_distrib, simp end
          ... ≤ 2^m * 2^n     : nat.mul_le_mul_right (2^n) (succ_le_of_lt Hx)
          ... = 2^(m + n)     : eq.symm (nat.pow_add _ _ _)

end nat
