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

end nat
