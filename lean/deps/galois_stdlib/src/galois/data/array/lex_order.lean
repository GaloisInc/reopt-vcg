-- Defines predicates for strict and non-strict lexicographic orderings over arrays.

namespace array

/--
This compares two arrays lexicographically with an extra argument to denote the value of the predicate
if they are equal.
-/
inductive lex_compare {α} [h:linear_order α] (are_eq : Prop) {m n} (x : array m α) (y : array n α) : Prop
| has_lt_index {}
    (j : ℕ)
    (j_m : j < m) (j_n : j < n)
    (is_lt : x.read ⟨j,j_m⟩ < y.read ⟨j, j_n⟩)
    (eq : ∀(k : ℕ) (k_j : k < j), x.read ⟨k,trans k_j j_m⟩ = y.read ⟨k, trans k_j j_n⟩)
    : lex_compare
| is_prefix
    (shorter_array : are_eq)
    (eq : ∀(k : ℕ) (k_m : k < m) (k_n : k < n), x.read ⟨k,k_m⟩ = y.read ⟨k,k_n⟩)
    : lex_compare

namespace lex_compare

/- This decides the lex_compare relation given decidability of the underlying relation. -/
def decide {α:Type _}
  [h:linear_order α] [r:decidable_rel (h.lt)] (when_eq : Prop) {m} (x:array m α) {n} (y:array n α)
  [decidable when_eq]
: Π(i:ℕ) -- Index in array to check next
   (j:ℕ) -- Number of elements remaining to check
   (p:i + j = min m n)
   (q : ∀(k:ℕ) (k_i : k < i) (k_lt_m : k < m) (k_lt_n : k < n), x.read ⟨k, k_lt_m⟩ = y.read ⟨k, k_lt_n⟩),
   decidable (lex_compare when_eq x y)
| i 0 p q :=
  if m_le_n : when_eq then
    decidable.is_true
    begin
      apply lex_compare.is_prefix m_le_n,
      intros k k_lt_m k_lt_n,
      simp only [nat.add_zero] at p,
      have k_lt_i : k < i,
      { simp only [p], exact (lt_min k_lt_m k_lt_n), },
      apply q k k_lt_i k_lt_m k_lt_n,
    end
  else
    decidable.is_false
    begin
      intro c,
      cases c,
      case lex_compare.is_prefix { contradiction, },
      case lex_compare.has_lt_index : j j_lt_m j_lt_n read_x_lt_read_y read_eq {
        simp only [nat.add_zero] at p,
        have j_lt_i : j < i, { simp only [p], exact (lt_min j_lt_m j_lt_n), },
        have r : read x ⟨j, j_lt_m⟩ = read y ⟨j, j_lt_n⟩ := q j j_lt_i j_lt_m j_lt_n,
        simp only [r] at read_x_lt_read_y,
        exact (lt_irrefl _ read_x_lt_read_y),
      },
    end
| i (nat.succ j) p q :=
  let i_lt_min : i < min m n :=
    begin
      simp only [eq.symm p],
      apply nat.lt_add_of_zero_lt_left _ _ (nat.zero_lt_succ _),
    end in
  let i_lt_m : i < m := lt_of_lt_of_le i_lt_min (min_le_left m n) in
  let i_lt_n : i < n := lt_of_lt_of_le i_lt_min (min_le_right m n) in
  if read_x_lt_read_y : x.read ⟨i, i_lt_m⟩ < y.read ⟨i, i_lt_n⟩ then
    decidable.is_true
    begin
      apply lex_compare.has_lt_index i i_lt_m i_lt_n read_x_lt_read_y,
      intros k k_lt_i,
      apply q k k_lt_i,
    end
  else if read_y_lt_read_x : y.read ⟨i, i_lt_n⟩ < x.read ⟨i, i_lt_m⟩ then
    decidable.is_false
    begin
      intro c,
      cases c,
      case lex_compare.is_prefix : m_le_n c_eq {
        have read_i_eq := c_eq i i_lt_m i_lt_n,
        simp only [read_i_eq] at read_y_lt_read_x,
        apply lt_irrefl _ read_y_lt_read_x,
      },
      case lex_compare.has_lt_index : j j_lt_m j_lt_n read_j_lt k_eq {
        have tri := lt_trichotomy i j,
        cases tri,
        case or.inl : i_lt_j {
          have read_i_eq := k_eq i i_lt_j,
          simp only [read_i_eq] at read_y_lt_read_x,
          apply lt_irrefl _ read_y_lt_read_x,
        },
        cases tri,
        case or.inl : i_eq_j {
          have fin_m_i_eq_j : fin.mk i i_lt_m = fin.mk j j_lt_m := fin.eq_of_veq i_eq_j,
          have fin_n_i_eq_j : fin.mk i i_lt_n = fin.mk j j_lt_n := fin.eq_of_veq i_eq_j,
          simp only [fin_m_i_eq_j, fin_n_i_eq_j] at read_y_lt_read_x,
          exact (not_lt_of_gt read_y_lt_read_x read_j_lt),
        },
        case or.inr : j_lt_i {
          have read_j_eq := q j j_lt_i j_lt_m j_lt_n,
          simp only [read_j_eq] at read_j_lt,
          apply lt_irrefl _ read_j_lt,
        },
      },
    end
  else
    let idx_inv : i + 1 + j = min m n := by simp [symm p] in
    -- Prove we checked all the elements less than i+1
    let prev_checked : ∀ (k : ℕ) (k_lt : k < i + 1) (k_m : k < m) (k_n : k < n),
                         read x ⟨k, k_m⟩ = read y ⟨k, k_n⟩ :=
      begin
        intros k k_lt_succ_i k_lt_m k_lt_n,
        have k_choices : k < i ∨ k = i := lt_or_eq_of_le (nat.le_of_lt_succ k_lt_succ_i ),
        cases k_choices,
        case or.inl : k_lt_i {
          exact (q _ k_lt_i k_lt_m k_lt_n),
        },
        case or.inr : k_eq_i {
          -- Replace k with i in goal
          have fin_m_k_eq_i : fin.mk k k_lt_m = fin.mk i i_lt_m := fin.eq_of_veq k_eq_i,
          have fin_n_k_eq_i : fin.mk k k_lt_n = fin.mk i i_lt_n := fin.eq_of_veq k_eq_i,
          simp [fin_m_k_eq_i, fin_n_k_eq_i],
          -- Prove x.read i = y.read i
          have read_tri := lt_trichotomy (read x ⟨i, i_lt_m⟩) (read y ⟨i, i_lt_n⟩),
          simp [read_x_lt_read_y, read_y_lt_read_x] at read_tri,
          exact read_tri,
        },
      end in
    decide (i+1) j idx_inv prev_checked

instance {α:Type _} [h:linear_order α] [r:decidable_rel (h.lt)] {m} (x:array m α) {n} (y:array n α)
  (when_eq : Prop) [decidable when_eq]
: decidable (lex_compare when_eq x y) :=
  let p : ∀(k:ℕ) (k_i : k < 0) (k_m : k < m) (k_n : k < n), x.read ⟨k, k_m⟩ = y.read ⟨k, k_n⟩ :=
    begin
      intros k k_lt_zero,
      exact false.elim (nat.not_lt_zero k k_lt_zero),
    end in
  decide when_eq x y 0 (min m n) (nat.zero_add (min m n)) p

end lex_compare

/-- One array is lexicographically strictly less than or equal another. -/
def lex_le {α} [h:linear_order α] {m n} (x : array m α) (y : array n α) : Prop :=
  lex_compare (m ≤ n) x y

namespace lex_le

instance {α:Type _} [h:linear_order α] [r:decidable_rel (h.lt)] {m} (x:array m α) {n} (y:array n α)
: decidable (lex_le x y) :=
  begin unfold lex_le, apply_instance, end

end lex_le

/-- One array is lexicographically strictly less than or equal another. -/
def lex_lt {α} [h:linear_order α] {m n} (x : array m α) (y : array n α) : Prop :=
  lex_compare (m < n) x y

namespace lex_lt
instance {α:Type _} [h:linear_order α] [r:decidable_rel (h.lt)] {m} (x:array m α) {n} (y:array n α)
: decidable (lex_lt x y) :=
  begin unfold lex_lt, apply_instance, end
end lex_lt

end array
