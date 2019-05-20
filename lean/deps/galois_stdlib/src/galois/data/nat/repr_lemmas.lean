-- Lemmas
import galois.data.list.nth_le

namespace galois
namespace nat
open nat

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

/-- Prove each list entry returned by digit_succ is less than the base -/
theorem digit_succ_bound {base:ℕ} (basep : base ≥ 2)
  {v : list ℕ}
  {i:ℕ}
  (i_lt_digit_succ : i < (digit_succ base v).length)
  (v_read : Π(j_lt : i < v.length), list.nth_le v i j_lt < base)
: list.nth_le (digit_succ base v) i i_lt_digit_succ < base :=
begin
  have base_is_pos : 0 < base := le_of_succ_le basep,
  revert i,
  induction v,
  case list.nil {
    intros i i_lt_digit_succ v_read,
    simp [digit_succ, list.nth_le_singleton],
    exact basep,
  },
  case list.cons : h r ind {
    intros i i_lt_digit_succ v_read,
    dsimp [digit_succ],
    -- Split on whether h + 1 is base and simplify ite
    apply dite (h + 1 = base); intro h_limit; simp [h_limit],
    -- Case for h + 1 = base.
    { cases i; simp [list.nth_le],
      case zero {
        exact base_is_pos
      },
      case succ : i {
        apply ind,
        { intros i_lt,
          -- Rewrite i_lt in goal with meta variable to allow matching at q,
          rw [proof_irrel i_lt _],
          -- Use v_read
          exact v_read (succ_lt_succ i_lt),
        },
      },
    },
    { cases i,
      case zero {
        dsimp [list.nth_le],
        dsimp [list.nth_le] at v_read,
        have h_le : h + 1 ≤ base,
        { exact v_read (succ_le_succ (zero_le _)),
        },
        cases (lt_or_eq_of_le h_le),
        case or.inl : is_lt { exact is_lt },
        case or.inr : is_eq { exact (absurd is_eq h_limit), },
      },
      case succ : i {
        simp [digit_succ, h_limit, succ_add] at i_lt_digit_succ,
        apply v_read i_lt_digit_succ,
      },
    },
  },
end

/-- Prove each list entry returned by to_digits is less than the base -/
theorem nth_to_digits_is_lt {base v : ℕ} (base_ok : base ≥ 2)
   {i:ℕ}  (p : i < (to_digits base v).length)
: list.nth_le (to_digits base v) i p < base :=
begin
  have base_is_pos : 0 < base := nat.le_of_succ_le base_ok,
  induction v,
  case nat.zero {
    simp [nat.to_digits] at p,
    simp [nat.to_digits, list.nth_le []],
    cases i,
    case nat.zero {
      simp [list.nth_le, *],
    },
    by_contradiction,
    exact nat.not_succ_le_zero _ (nat.le_of_lt_succ p),
  },
  case nat.succ : v ind {
    simp [nat.to_digits],
    apply nat.digit_succ_bound base_ok,
    { intros i_lt,
      exact ind i_lt,
    },
  },
end

end nat
end galois
