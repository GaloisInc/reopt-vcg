import galois.logic
import tactic.fin_cases

namespace char

/-- Predicate that holds if character is a 7-bit ascii printable character. -/
def is_ascii7_printable (c:char) : Prop := 0x20 ≤ c.val ∧ c.val ≤ 0x7e

local attribute [reducible] is_ascii7_printable

namespace is_ascii7_printable
instance decidable : decidable_pred is_ascii7_printable := by apply_instance
end is_ascii7_printable

theorem alpha_is_printable {c:char} : c.is_alpha → c.is_ascii7_printable :=
begin
  unfold is_alpha, unfold is_ascii7_printable,
  intro isa,
  cases isa;
  {
    simp [is_upper, is_lower] at isa,
    apply and.intro,
    { transitivity, tactic.swap, exact isa.left, exact dec_trivial, },
    { transitivity, exact isa.right, exact dec_trivial, },
  },
end

theorem digit_is_printable {c:char} : c.is_digit → c.is_ascii7_printable :=
begin
  unfold is_digit,
  intro isd,
  apply and.intro,
  { transitivity, tactic.swap, exact isd.left, exact dec_trivial, },
  { transitivity, exact isd.right, exact dec_trivial, },
end

theorem digit_char_is_digit (i:ℕ) (p : i < 10): is_digit (nat.digit_char i) :=
begin
  unfold nat.digit_char,
  have q : 0 ≤ i := nat.zero_le _,
  -- Repeatedly try numbers starting from zero until we can't prove the theorem.
  repeat {
    cases (nat.eq_or_lt_of_le q) with h lt,
    case or.inl : h {
      simp only [h.symm, if_pos], exact (of_as_true trivial),
    },
    simp only [(ne_of_lt lt).symm, if_false],
    have q := nat.succ_le_of_lt lt,
  },
  -- The last q should assert that i is at least 10
  have q : 10 ≤ i := q,
  have r := not_lt_of_ge q,
  contradiction,
end

section

protected
theorem le_refl : ∀ a : char, a ≤ a :=
begin
  intro c,
  unfold has_le.le, unfold char.le,
end

end

protected
theorem le_trans : ∀ a b c : char, a ≤ b → b ≤ c → a ≤ c :=
begin
  intros a b c,
  unfold has_le.le, unfold char.le,
  apply le_trans,
end

protected
theorem lt_iff_le_not_le : ∀ a b : char, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
begin
  intros a b,
  unfold has_le.le, unfold char.le,
  unfold has_lt.lt, unfold char.lt,
  apply lt_iff_le_not_le ,
end

protected
theorem le_antisymm : ∀ a b : char, a ≤ b → b ≤ a → a = b :=
begin
  intros a b,
  cases a, cases b,
  unfold has_le.le, unfold char.le,
  intros a_le_b b_le_a,
  exact eq_of_veq (le_antisymm a_le_b b_le_a),
end

protected
theorem le_total : ∀ a b : char, a ≤ b ∨ b ≤ a :=
begin
  intros a b,
  unfold has_le.le, unfold char.le,
  apply le_total
end

-- Show characters have a linear order.
instance : linear_order char :=
{ le := char.le
, le_refl := char.le_refl
, le_trans := char.le_trans
, lt := char.lt
, lt_iff_le_not_le := char.lt_iff_le_not_le
, le_antisymm := char.le_antisymm
, le_total := char.le_total
}


end char
