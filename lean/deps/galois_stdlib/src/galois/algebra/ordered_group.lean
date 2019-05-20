namespace galois

section ordered_cancel_comm_monoid

universe u
variable {α : Type u}

variables [ordered_cancel_comm_monoid α] {a b c : α}

@[simp] lemma add_le_add_iff_left (a : α) {b c : α} : a + b ≤ a + c ↔ b ≤ c :=
⟨le_of_add_le_add_left, λ h, add_le_add_left h _⟩

@[simp] lemma add_le_add_iff_right (c : α) : a + c ≤ b + c ↔ a ≤ b :=
add_comm c a ▸ add_comm c b ▸ add_le_add_iff_left c

@[simp] lemma add_lt_add_iff_left (a : α) {b c : α} : a + b < a + c ↔ b < c :=
⟨lt_of_add_lt_add_left, λ h, add_lt_add_left h _⟩

@[simp] lemma add_lt_add_iff_right (c : α) : a + c < b + c ↔ a < b :=
add_comm c a ▸ add_comm c b ▸ add_lt_add_iff_left c

@[simp] lemma le_add_iff_nonneg_right (a : α) {b : α} : a ≤ a + b ↔ 0 ≤ b :=
have a + 0 ≤ a + b ↔ 0 ≤ b, from add_le_add_iff_left a,
by rwa add_zero at this

@[simp] lemma lt_add_iff_pos_right (a : α) {b : α} : a < a + b ↔ 0 < b :=
have a + 0 < a + b ↔ 0 < b, from add_lt_add_iff_left a,
by rwa add_zero at this

end ordered_cancel_comm_monoid
end galois
