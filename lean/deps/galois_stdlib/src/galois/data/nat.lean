import data.nat.basic
import data.buffer

namespace nat

-- Reduce x < y to theorem with addition
protected theorem lt_is_succ_le (x y : ℕ) : x < y ↔ x + 1 ≤ y := by trivial

-- Reduce succ x < succ y
protected lemma succ_lt_succ_iff : ∀{m n : ℕ}, succ n < succ m ↔ n < m :=
begin
  intros m n,
  simp [nat.lt_is_succ_le, nat.succ_le_succ_iff],
end

-- This rewrites a subtraction on left-hand-side of inequality into a predicate
-- involving addition.
protected lemma sub_lt_to_add (a m n : ℕ) : a - n < m ↔ (a < m + n ∧ (n ≤ a ∨ 0 < m)) :=
begin
  revert a m,
  induction n,
  case nat.zero {
    intros a m,
    simp [zero_le],
  },
  case nat.succ : n ind {
    intros a m,
    cases a,
    case nat.zero {
      simp [nat.zero_sub, zero_lt_succ, not_succ_le_zero],
    },
    case nat.succ {
      simp [add_succ, nat.succ_lt_succ_iff, nat.succ_le_succ_iff, ind],
    },
  },
end

-- This rewrites a subtraction on right-hand side of inequality into an addition.
protected lemma lt_sub_iff (a m n : ℕ) : a < m - n ↔ a + n < m :=
begin
  revert n,
  induction m with m ind,
  { simp [nat.lt_is_succ_le, add_succ, nat.not_succ_le_zero, nat.zero_sub],
  },
  { intro n,
    cases n with n,
    { simp, },
    { simp [nat.succ_lt_succ_iff, ind],
    },
  },
end

section rendering

def to_digits_buffer.f {base : ℕ} (base_pos : base > 1)
     (n:ℕ) (rec : Π(m:ℕ), m < n → buffer ℕ → buffer ℕ) (prev:buffer ℕ) : buffer ℕ :=
  if h : n < base then
    prev.push_back n
   else
     let n_pos : n > 0 :=
          calc n ≥ base : le_of_not_gt h
            ...  > 1    : base_pos
            ...  > 0    : zero_lt_succ 0 in
     rec (nat.div n base) (div_lt_self n_pos base_pos) (prev.push_back (nat.mod n base))

/--
This is an operation for converting natural numbers into a buffer of naturals.

The standard prelude defines a similiar function nat.to_digits, but it's runtime
is linear with respect to unary size of the number.
-/
def to_digits_buffer (base : ℕ) (base_pos : base > 1) (n:ℕ) : buffer ℕ :=
  well_founded.fix lt_wf (to_digits_buffer.f base_pos) n buffer.nil


/-- Show that nat.to_digits never returns empty list. -/
theorem to_digits_ne_nil (base:ℕ) (x:ℕ) :  nat.to_digits base x ≠ list.nil :=
begin
  cases x,
  case nat.zero : { simp [nat.to_digits], },
  case nat.succ : x {
    simp [nat.to_digits],
    cases (nat.to_digits base x),
    { simp [nat.digit_succ], },
    { simp [nat.digit_succ],
      -- case split on ite condition, then use assumption to resovle goal.
      apply (dite (hd + 1 = base)); { intro eq, simp [eq], },
    },
  },
end

end rendering

end nat
