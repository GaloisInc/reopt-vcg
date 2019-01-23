-- Lemmas primarily about nth_le
import data.list.basic -- from mathlib
import galois.data.nat.basic

namespace list

/-- Simplify a singleton list -/
theorem nth_le_singleton {α: Type _} (x : α) (i : ℕ) (p : i < 1)
: list.nth_le [x] i p = x :=
begin
  cases i,
  case nat.zero {
    simp [list.nth_le],
  },
  case nat.succ : i {
    have q := nat.not_succ_le_zero _ (nat.le_of_lt_succ p),
    exact (false.elim q),
  },
end

section nth_le_reverse

/-- Lemma to help with stating nth_le_cons_rest. -/
theorem nth_le_cons_rest.index  {i j} (i_pos : i > 0) (p:i < j + 1) : i-1 < j :=
begin
  cases i,
  case nat.zero { have h : false := nat.not_lt_zero _ i_pos, contradiction, },
  case nat.succ : i {
    simp only [nat.add_succ, nat.add_zero, nat.succ_lt_succ_iff] at p,
    exact p,
  },
end

theorem nth_le_cons_rest {α} (x:α) {l:list α} {i:ℕ} (i_pos : i > 0) (p:i < l.length + 1)
: nth_le (x :: l) i p = nth_le l (i-1) (nth_le_cons_rest.index i_pos p) :=
begin
  cases i,
  case nat.zero { have h : false := nat.not_lt_zero _ i_pos, contradiction, },
  case nat.succ : i {
    simp only [nth_le, nat.succ_sub_succ], trivial,
  },
end

theorem nth_le_reverse_core.index1 {α} {l:list α} {i:ℕ} (i_lt : i < l.length)
: l.length - i - 1 < l.length :=
begin
  simp only [nat.sub_lt_to_add, nat.add_assoc],
  apply and.intro, apply and.intro,
  { apply nat.lt_add_of_pos_right,
    simp [nat.succ_add],
    exact nat.zero_lt_succ i,
  },
  { have h := nat.le_of_lt i_lt,
    simp [h],
  },
  { cases l,
    { have h := nat.not_lt_zero _ i_lt, contradiction, },
    { exact or.inr (nat.zero_lt_succ _), },
  },
end

theorem nth_le_reverse_core.index2 {α} {l r:list α} {i:ℕ}
  (i_lt : i < (list.reverse_core l r).length)
  (i_ge_l : not (i < l.length))
: i - l.length < r.length :=
begin
  simp only [reverse_core_eq, length_append, length_reverse] at i_lt,
  simp at i_ge_l,
  simp [nat.sub_lt_to_add, nat.add_comm r.length l.length, i_lt, i_ge_l],
end

/- Define nth_le (reverse_core ..) equationally. -/
theorem nth_le_reverse_core {α} : ∀ (l r : list α) (i : nat) (i_lt : i < (reverse_core l r).length)        ,
  nth_le (reverse_core l r) i i_lt =
    if h : i < l.length then
      nth_le l (l.length - (i + 1)) (nth_le_reverse_core.index1 h)
    else
      nth_le r (i - l.length) (nth_le_reverse_core.index2 i_lt h) :=
begin
  intros l,
  induction l,
  case list.nil {
    intros r i i_lt,
    simp [reverse_core],
  },
  case list.cons : lh l_rest ind {
    intros r i i_lt,
    simp [reverse_core, ind],
    apply dite (i < length l_rest),
    { intro i_lt_l_rest,
      have i_lt_len  : (i < length (lh :: l_rest)) := nat.lt_succ_of_lt i_lt_l_rest,
      have len_l_rest : length l_rest ≥ i + 1 := i_lt_l_rest,
      simp only [dif_pos, i_lt_l_rest, i_lt_len,  i_lt_l_rest, nat.succ_add, nat.zero_add,
                 nat.succ_sub len_l_rest, nth_le],
      trivial,
    },
    { intro i_ge_l_rest,
      simp only [dif_neg i_ge_l_rest],
      simp at i_ge_l_rest,
      apply or.elim (nat.eq_or_lt_of_le (i_ge_l_rest)),
      { intro l_eq,
        have ite_cond : i < length (lh :: l_rest),
        { simp [length, l_eq, nat.zero_lt_succ], },
        simp only [ dif_pos, ite_cond ],
        simp [nat.succ_add, l_eq],
      },
      {
        intro l_lt,
        have ite_cond : ¬(i < length (lh :: l_rest)),
        { simp only [ length, not_lt],
          exact l_lt,
        },
        simp [ite_cond],
        have pr : 0 < i - length l_rest,
        { simp [nat.lt_sub_iff], exact l_lt, },
        simp [nth_le_cons_rest _ pr, nat.sub_sub],
      },
    },
  },
end

/-- Lemma for nth_le_reverse_simp -/
theorem nth_le_reverse_simp.lemma {α} {l:list α} {i:ℕ} (i_lt : i < l.reverse.length)
: l.length - i - 1 < l.length :=
begin
  simp only [length_reverse] at i_lt,
  simp only [nat.sub_lt_to_add, nat.add_assoc],
  apply and.intro, apply and.intro,
  { apply nat.lt_add_of_pos_right,
    simp [nat.succ_add],
    exact nat.zero_lt_succ i,
  },
  { have h := nat.le_of_lt i_lt,
    simp [h],
  },
  { cases l,
    { have h := nat.not_lt_zero _ i_lt, contradiction, },
    { exact or.inr (nat.zero_lt_succ _), },
  },
end

/-- This is a version of nth_le_reverse designed for better use as a simp rule. -/
@[simp]
theorem nth_le_reverse_simp {α} {l:list α} {i:ℕ} (i_lt : i < l.reverse.length)
: nth_le l.reverse i i_lt = list.nth_le l (l.length - i - 1) (nth_le_reverse_simp.lemma i_lt) :=
begin
  simp only [length_reverse] at i_lt,
  simp only [reverse, nth_le_reverse_core , dif_pos i_lt, nat.sub_sub],
  trivial,
end

end nth_le_reverse

end list
