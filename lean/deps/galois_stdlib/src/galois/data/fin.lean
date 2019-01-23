namespace fin

section

parameter (n:ℕ)
parameter (P:fin n → Prop)
parameter [dp:decidable_pred P]

def extend_lt {i j} : fin i → i < j → fin j
| x i_le_j := ⟨x.val, nat.lt_trans x.is_lt i_le_j⟩

def extend {i j} : fin i → i ≤ j → fin j
| x i_le_j := ⟨x.val, nat.lt_of_lt_of_le x.is_lt i_le_j⟩

def decidable_forall.partial : ∀(i:ℕ) (h:i ≤ n), decidable (Π(j:fin i), P (extend j h))
| 0 h := decidable.is_true
  begin
    intros j,
    have f := nat.not_lt_zero j.val j.is_lt,
    contradiction,
  end
| (nat.succ i) h :=
  match dp ⟨i, h⟩ with
  | (decidable.is_false i_false) := decidable.is_false
    begin
      by_contradiction assumption,
      apply i_false,
      exact (assumption ⟨i, nat.lt.base i⟩),
    end
  | (decidable.is_true i_ok) :=
    match decidable_forall.partial i (nat.le_of_succ_le h) with
    | (decidable.is_false rec_false) := decidable.is_false
      begin
        by_contradiction assumption,
        apply rec_false,
        intro j,
        exact assumption ⟨j.val, nat.lt_succ_of_lt j.is_lt⟩
      end
    | (decidable.is_true rec_ok) := decidable.is_true
      begin
        simp [extend] at rec_ok,
        simp [extend],
        intro j,
        cases j,
        -- Split on value of j induced by proof j < i+1
        cases j_is_lt,
        { exact i_ok, },
        { exact rec_ok ⟨j_val, j_is_lt_a⟩, },
      end
    end
  end

/-- This proves that quantification over fin is decidable. -/
instance decidable_forall : decidable (Π(j:fin n), P j) :=
  decidable_of_decidable_of_eq (decidable_forall.partial n (nat.le_refl n))
  begin
    apply propext,
    apply forall_congr,
    intro j,
    apply eq.to_iff,
    apply congr_arg,
    cases j,
    simp [extend],
  end

end

end fin
